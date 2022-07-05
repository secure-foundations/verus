use crate::ast::{Binder, Binders, Datatype, Datatypes, Ident, Path, PathX, Typ, TypX, Typs};
use crate::def::{
    prefix_box, prefix_unbox, suffix_local_stmt_id, BOX_BOOL, BOX_INT, PREFIX_TEMP_VAR, UNBOX_BOOL,
    UNBOX_INT,
};
use crate::poly::typ_as_mono;
use crate::sst::LocalDecl;
use crate::sst_to_air::{monotyp_to_path, typ_to_id};
use core::panic;
use sise::Node;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Internal expression to evaulate model constant
/// ModelExpr will be translated into `sise::Node`, and sent to Z3 for evaluation
pub type ModelExpr = Arc<ModelExprX>;
pub type ModelExprs = Arc<Vec<ModelExpr>>;
#[derive(Debug)]
// even if some expr is evaluated into some value, we might not be able to reuse that value when querying to Z3.
// (For example, Z3 don't understand something like `poly!val!4` even if it uses it internally)
// Therefore, we shouldn't store evaluated values from Z3 and reuse them into Z3.
pub enum ModelExprX {
    Const(Ident), // for integer and bool only
    Var(Ident),
    Apply(Ident, ModelExprs),
    AIRExpr(air::ast::Expr),
}

/// VIR-level Concrete value from SMT model
pub type ModelConstant = Arc<ModelConstantX>;
pub type ModelConstants = Arc<Vec<ModelConstant>>;
#[derive(Debug, Clone)]
pub enum ModelConstantX {
    Bool(bool),
    Int(Arc<String>),
    Datatype(ModelVariant),
    Seq(ModelConstants),
    // set
    // map
    // possiblly function type
    // List?
    // BitVec - note that bit-vector type is not present in VIR level - should I get info from air level?
}

/// Single field in a variant
pub type ModelField = Binder<(Typ, ModelConstant)>;
/// List of fields in a variant
/// For tuple-style variants, the fields appear in order and are named "0", "1", etc.
/// For struct-style variants, the fields may appear in any order
pub type ModelFields = Binders<(Typ, ModelConstant)>;
pub type ModelVariant = Binder<ModelFields>;

/// Result of VIR level model building
pub type ModelDef = Arc<ModelDefX>;
pub type ModelDefs = Arc<Vec<ModelDef>>;
#[derive(Debug)]
pub struct ModelDefX {
    pub name: Ident,
    pub typ: Typ,
    pub value: ModelConstant,
}

pub fn mk_apply(app: Ident, expr: ModelExpr) -> ModelExpr {
    Arc::new(ModelExprX::Apply(app, Arc::new(vec![expr])))
}

pub fn print_model_constant(constant: &ModelConstant, indent: &String) {
    let increased_indent = format!("    {}", indent);
    let more_increased_indent = format!("        {}", indent);
    match &**constant {
        ModelConstantX::Datatype(variant) => {
            println!("{} {:?} ", indent, variant.name);
            for field in &**variant.a {
                println!("{} {:?}:", increased_indent, field.name);
                print_model_constant(&field.a.1, &more_increased_indent);
            }
        }
        ModelConstantX::Bool(b) => println!("{} {:?}", indent, b),
        ModelConstantX::Int(s) => println!("{} {:?}", indent, s.to_string()),
        ModelConstantX::Seq(constants) => {
            for c in &**constants {
                print_model_constant(c, &increased_indent);
            }
        }
    };
}

impl ModelDefX {
    pub fn pretty_print(def: &ModelDefX) {
        println!("{:?}:", def.name);
        println!("  type: {:?}", def.typ);
        print_model_constant(&def.value, &"".to_string());
        println!("");
    }
}

#[derive(Clone, Debug)]
/// VIR-level model of a concrete counterexample
pub struct Model {
    /// VIR-level counter example, must call [build()] to populate this
    pub model: HashMap<Ident, ModelDef>,
    /// AIR-level model
    pub air_model: air::model::Model,
    /// VIR-level datatypes for surrounding module
    pub raw_datatypes: Datatypes,
    //// just a hasmhap from raw_datatypes for local_vars for speed
    pub datatypes: HashMap<Path, Datatype>,
    /// VIR-level types
    pub types: HashMap<Ident, Typ>,
    /// local variables
    pub local_vars: HashSet<Ident>,
    ///
    pub is_mutable: HashMap<Ident, bool>,
}

impl Model {
    pub fn new(
        air_model: air::model::Model,
        datatypes: Datatypes,
        local_decls: &Vec<LocalDecl>,
    ) -> Model {
        let mut types = HashMap::new();
        let mut local_vars = HashSet::new();
        let mut is_mutable = HashMap::new();
        for decl in local_decls {
            let name = decl.ident.0.clone();
            if name.to_string().starts_with(PREFIX_TEMP_VAR) {
                continue;
            }
            is_mutable.insert(name.clone(), decl.mutable);
            // println!("decl: {:?}", decl);
            types.insert(name.clone(), decl.typ.clone());
            local_vars.insert(name.clone());
        }
        Model {
            model: HashMap::new(),
            air_model,
            raw_datatypes: datatypes,
            datatypes: HashMap::new(),
            types,
            local_vars,
            is_mutable,
        }
    }

    fn string_to_bool(&self, result: String) -> Result<bool, String> {
        if result == "true" {
            Ok(true)
        } else if result == "false" {
            Ok(false)
        } else {
            Err(format!("expected true or false, but got {:?}", result))
        }
    }

    fn find_datatype(&self, path: Path) -> Option<Datatype> {
        let dt = self.datatypes.get(&path);
        match dt {
            Some(datatype_found) => return Some(datatype_found.clone()),
            _ => {}
        };

        for dtyp in &self.raw_datatypes {
            if dtyp.x.path == path {
                return Some(dtyp.clone());
            }
        }
        None
    }

    fn model_expr_to_node(&self, expr: &ModelExpr) -> Node {
        match &**expr {
            ModelExprX::Const(c) => Node::Atom(c.to_string()),
            ModelExprX::Var(air_name) => {
                // let air_name = self.get_air_name(ident, None); // TODO: change None to sid
                Node::Atom(air_name.to_string())
            }
            ModelExprX::Apply(app, exprs) => {
                let mut nodes: Vec<Node> = Vec::new();
                nodes.push(Node::Atom(app.to_string()));
                for expr in exprs.iter() {
                    nodes.push(self.model_expr_to_node(expr));
                }
                Node::List(nodes)
            }
            ModelExprX::AIRExpr(e) => {
                let pp = air::printer::Printer::new(true);
                pp.expr_to_node(e)
            }
        }
    }

    /// Generate a string to be used in the SMT file to box a given VIR type
    fn box_func(&self, typ: &Typ) -> Result<String, String> {
        let boxing = match &**typ {
            TypX::Datatype(path, typs) => {
                if typs.len() == 0 || path.segments[0].to_string() != "pervasive".to_string() {
                    prefix_box(path).to_string()
                } else {
                    // (Poly%pervasive.vec.Vec<u32.>.  v@)          "<T>"
                    let mono = typ_as_mono(typ).expect(format!("{:?}", typ).as_str());
                    let path = monotyp_to_path(&mono);
                    prefix_box(&path).to_string()
                }
            }
            TypX::Bool => String::from(BOX_BOOL),
            TypX::Int(_range) => String::from(BOX_INT),
            _ => return Err(format!("TODO: box_func for typ {:?}", typ)),
        };
        Ok(boxing)
    }

    /// Generate a string to be used in the SMT file to unbox a given VIR type
    fn unbox_func(&self, typ: &Typ) -> Result<String, String> {
        let unboxing = match &**typ {
            TypX::Datatype(path, typs) => {
                if typs.len() == 0 || path.segments[0].to_string() != "pervasive".to_string() {
                    prefix_unbox(path).to_string()
                } else {
                    let mono = typ_as_mono(typ).expect(format!("{:?}", typ).as_str());
                    let path = monotyp_to_path(&mono);
                    prefix_unbox(&path).to_string()
                }
            }
            TypX::Bool => String::from(UNBOX_BOOL),
            TypX::Int(_range) => String::from(UNBOX_INT),
            _ => return Err(format!("TODO: unbox_func for typ {:?}", typ)),
        };
        Ok(unboxing)
    }

    fn get_air_name(&self, name: &Ident, sid: Option<Ident>) -> Ident {
        let name_at_sign = suffix_local_stmt_id(&(Arc::new(name.to_string())));
        // if `name` is immutable, just give `@` and return
        if !self.is_mutable.get(name).expect("not found in is_mutable") {
            return name_at_sign;
        };
        // if `name` is mutable, get snapshot and translate
        match sid {
            Some(sid) => {
                // now rename according to snapmap
                self.air_model.translate_variable(&name_at_sign, &sid).expect(
                    format!(
                        "Failed to translate mutable variable to air name: {:?}, {:?}",
                        name, sid
                    )
                    .as_str(),
                )
            }
            // if sid is None, `name` should be immutable
            None => {
                panic!("Internal error");
            }
        }
    }

    /// For a variable, evaluate the value of this variable at this SMT model
    fn build_model_constant(
        &self,
        var: Ident, // this is just for tracking the variable that owns this constant. For struct/enum/seq/etc, a single variable can own multiple constants
        expr: &ModelExpr, // we will evaluate this expr to constant
        typ: &Typ,
        context: &mut air::context::Context,
    ) -> Result<ModelConstant, String> {
        let var_expr = self.model_expr_to_node(&expr);
        let result_constant: ModelConstant = match &**typ {
            TypX::Datatype(path, typs) => {
                if path.segments[0].to_string() == "pervasive".to_string()
                    && path.segments[1].to_string() == "seq".to_string()
                    && path.segments[2].to_string() == "Seq".to_string()
                    && typs.len() == 1
                {
                    self.build_seq_constant(var, expr, typ, path, typs, context)?
                } else if path.segments[0].to_string() == "pervasive".to_string()
                    && path.segments[1].to_string() == "vec".to_string()
                    && path.segments[2].to_string() == "Vec".to_string()
                    && typs.len() == 1
                {
                    self.build_vec_constant(var, expr, typ, path, typs, context)?
                }
                // white-list pervasive's datatypes
                // all datatypes should be white-listed
                else if path.segments[0].to_string() == "pervasive".to_string()
                    && path.segments[1].to_string() != "option".to_string()
                    && path.segments[1].to_string() != "result".to_string()
                {
                    return Err(format!(
                        "Now Pervasive only supported seq/vec/option/result, but got {:?}",
                        &path
                    ));
                } else {
                    // TODO: how to get information from user -> how to "debug" user-defined container
                    // now datatype should be struct or enum at this point (container type should be handled in a separte routine)

                    // let ident = &path.segments[0];
                    let ident = crate::sst_to_air::path_to_air_ident(path);
                    let dtyp = self
                        .find_datatype(path.clone())
                        .expect(format!("Couldn't find dataype with path: {:?}", path).as_str());
                    // println!("datatype:  {:?}", dtyp);
                    let mut model_fields: Vec<ModelField> = vec![];
                    let mut found_variant = Arc::new("variant not found".to_string());
                    // for pp in &*dtyp.x.typ_params {
                    //     println!("typ param: {:?}", pp);
                    // }
                    for variant in &*dtyp.x.variants {
                        // query "which variant"
                        // Note that `struct` has only one variant, while enum possible have many variants
                        // (eval (is-Message./Move  msg@))              // Might be Z3 specific
                        // (eval ((_ is Message./Move) msg@))           // SMTLIB "tester"
                        //  pervasive.option.Option./Some/_0
                        let appl = format!("is-{}/{}", ident.to_string(), variant.name.to_string());
                        let items = vec![Node::Atom(appl), self.model_expr_to_node(&expr)];
                        let result = context.eval_expr(Node::List(items))?;
                        let res = self.string_to_bool(result)?;
                        if !res {
                            continue;
                        }
                        found_variant = variant.name.clone();

                        for field in &*variant.a {
                            // query "what are the values"
                            // (eval (ValidI64./ValidI64/?val ret@))
                            // (eval (ValidI64./ValidI64/?is_nan ret@))
                            // println!("field {:?} : {:?}", field.name, field.a.0);

                            let appl = format!(
                                "{}/{}/?{}",
                                ident.to_string(),
                                variant.name.to_string(),
                                field.name.to_string()
                            );
                            // Now recursive call for this specific field
                            // (eval tmp%%1@)  -> (tuple%2./tuple%2 Poly!val!2 Poly!val!3)
                            // (eval (%Poly%Option. (tuple%2./tuple%2/?field%0 tmp%%1@))) -> (Option./Some Poly!val!7)
                            let new_expr = mk_apply(Arc::new(appl), expr.clone());
                            let model_const: ModelConstant = match &*field.a.0 {
                                TypX::Bool | TypX::Int(_) | TypX::Datatype(_, _) => self
                                    .build_model_constant(
                                        var.clone(),
                                        &new_expr,
                                        &field.a.0,
                                        context,
                                    )?,
                                TypX::TypParam(id) => {
                                    // println!("typ param: {:?}", id);
                                    // (eval (Option./Some/_0 a@))
                                    // (eval (%I Poly!val!5))   -> error  unknown constant
                                    // (eval (%I (Option./Some/_0 a@)))
                                    // TODO: typs has multiple types for example, when a tuple has two different enums
                                    let unbox = self.unbox_func(&typs[0])?;
                                    let unboxed_expr = mk_apply(Arc::new(unbox), new_expr);
                                    self.build_model_constant(
                                        var.clone(),
                                        &unboxed_expr,
                                        &typs[0], // is this typ info correct??
                                        context,
                                    )?
                                }
                                _ => {
                                    panic!(
                                        "TODO: non primitive type in field, type: {:?}",
                                        field.a.0
                                    )
                                }
                            };

                            let model_field: ModelField = Arc::new(air::ast::BinderX {
                                name: field.name.clone(),
                                a: (field.a.0.clone(), model_const),
                            });
                            model_fields.push(model_field);
                        }
                    }
                    let model_fields: ModelFields = Arc::new(model_fields);
                    Arc::new(ModelConstantX::Datatype(Arc::new(air::ast::BinderX {
                        name: found_variant,
                        a: model_fields,
                    })))
                }
            }
            TypX::Bool => {
                let result = context.eval_expr(var_expr)?;
                let b = self.string_to_bool(result)?;
                Arc::new(ModelConstantX::Bool(b))
            }
            TypX::Int(_range) => {
                let result = context.eval_expr(var_expr)?;
                Arc::new(ModelConstantX::Int(Arc::new(result)))
            }
            // For evaluation, simply unbox
            TypX::Boxed(typ_in) => {
                let unbox = self.unbox_func(typ_in)?;
                let unboxed_expr = mk_apply(Arc::new(unbox), expr.clone());
                self.build_model_constant(var.clone(), &unboxed_expr, typ_in, context)?
            }
            // /// Bool, Int, Datatype are translated directly into corresponding SMT types (they are not SMT-boxed)
            // Bool,
            // Int(IntRange),
            // /// Tuple type (t1, ..., tn).  Note: ast_simplify replaces Tuple with Datatype.
            // Tuple(Typs),
            // /// Spec closure type (t1, ..., tn) -> t0.
            // Lambda(Typs, Typ),
            // /// Datatype (concrete or abstract) applied to type arguments
            // Datatype(Path, Typs),
            // /// Boxed for SMT encoding (unrelated to Rust Box type), can be unboxed:
            // Boxed(Typ),
            // /// Type parameter (inherently SMT-boxed, and cannot be unboxed)
            // TypParam(Ident),
            // /// Type of type identifiers
            // TypeId,
            // /// AIR type, used internally during translation
            // Air(air::ast::Typ),
            _ => {
                panic!("TODO at VIR model constant building: var: {:?}, typ: {:?}", var, typ)
            }
        };
        Ok(result_constant)
    }

    pub fn build_seq_constant(
        &self,
        var: Ident,
        expr: &ModelExpr,
        seq_typ: &Typ,
        _path: &Path,
        typs: &Typs, // the type of seq element
        context: &mut air::context::Context,
    ) -> Result<ModelConstant, String> {
        // first, evaluate this seq's length
        // (eval (pervasive.seq.Seq.len.? (UINT 32) (Poly%pervasive.seq.Seq<u32.>. v@)))
        // TODO: What if length does not return concrete int value?
        // sometimes got partially evaluated values.  e.g. `(pervasive.seq.Seq.len.? Type!val!2 Poly!val!2)`
        let boxing_string = self.box_func(seq_typ)?;
        let boxed_seq_expr = mk_apply(Arc::new(boxing_string), expr.clone());
        let typ = &typs[0]; // the type of seq element
        let typ_expr = typ_to_id(typ);

        let query_len_appl = "pervasive.seq.Seq.len.?".to_string();
        let query_len_expr = Arc::new(ModelExprX::Apply(
            Arc::new(query_len_appl),
            Arc::new(vec![Arc::new(ModelExprX::AIRExpr(typ_expr.clone())), boxed_seq_expr.clone()]),
        ));
        let query_len_node = self.model_expr_to_node(&query_len_expr);
        let length_string = match context.eval_expr(query_len_node) {
            Ok(len_string) => len_string,
            Err(err_string) => {
                return Err(format!("When evaluating seq/vec length, {}", err_string));
            }
        };
        // println!("seq len: {}", length_string);

        // Second, evaluate each element of this sequence
        // (eval (%I (pervasive.seq.Seq.index.? (UINT 32) (Poly%pervasive.seq.Seq<u32.>. v@) (I 0))))
        let mut seq_elts: Vec<ModelConstant> = vec![];
        let seq_length_result = length_string.parse();
        let seq_length: u32 = match seq_length_result {
            Ok(l) => l,
            Err(_) => {
                return Err(format!(
                    "Model's Seq/Vec length not evaluated to an integer. Please make additional assume about length. Half evaluated length from Z3: {:?}.",
                    length_string
                ));
            }
        };

        if seq_length > 100 {
            return Err(format!(
                "Model's Seq/Vec length bigger than 100, got length {:?}. Please make additional assume about length",
                seq_length
            ));
        }

        println!("got length {:?}", seq_length);

        let query_index_appl = Arc::new("pervasive.seq.Seq.index.?".to_string());
        for idx in 0..seq_length {
            let idx_expr = Arc::new(ModelExprX::Const(Arc::new(idx.to_string())));
            let index_expr = mk_apply(Arc::new(self.box_func(typ)?), idx_expr);
            let elt_expr = Arc::new(ModelExprX::Apply(
                Arc::new(query_index_appl.to_string()),
                Arc::new(vec![
                    Arc::new(ModelExprX::AIRExpr(typ_expr.clone())),
                    boxed_seq_expr.clone(),
                    index_expr,
                ]),
            ));
            let elt = self.build_model_constant(
                var.clone(),
                &elt_expr,
                &Arc::new(TypX::Boxed(typ.clone())),
                context,
            )?;
            seq_elts.push(elt);
        }

        Ok(Arc::new(ModelConstantX::Seq(Arc::new(seq_elts))))
    }

    pub fn build_vec_constant(
        &self,
        var: Ident,
        expr: &ModelExpr,
        vec_typ: &Typ,
        _path: &Path,
        typs: &Typs, // the type of vector element
        context: &mut air::context::Context,
    ) -> Result<ModelConstant, String> {
        // implicitly `.view()` this and handle this as `seq`.
        // REVIEW: is this desirable?
        // Example:  (pervasive.vec.Vec.view.? (UINT 32) (Poly%pervasive.vec.Vec<u32.>.  v@))
        // Note that `.view()` returns `Poly`. Make typ as `boxed`
        let boxing_string = self.box_func(vec_typ)?;
        let boxed_vec_expr = mk_apply(Arc::new(boxing_string), expr.clone());

        let typ = &typs[0]; // the type of vector element
        let typ_expr = typ_to_id(typ);

        let view_appl = "pervasive.vec.Vec.view.?".to_string();
        let view_expr = Arc::new(ModelExprX::Apply(
            Arc::new(view_appl),
            Arc::new(vec![Arc::new(ModelExprX::AIRExpr(typ_expr.clone())), boxed_vec_expr.clone()]),
        ));

        let seq_path = Arc::new(PathX {
            krate: None,
            segments: Arc::new(vec![
                Arc::new("pervasive".to_string()),
                Arc::new("seq".to_string()),
                Arc::new("Seq".to_string()),
            ]),
        });
        let seq_typ = Arc::new(TypX::Datatype(seq_path, typs.clone()));

        let unbox_string = self.unbox_func(&seq_typ)?;
        let unboxed_view_expr = mk_apply(Arc::new(unbox_string), view_expr);

        // let boxed_seq_typ = Arc::new(TypX::Boxed(seq_typ));
        // self.build_seq_constant(var, &view_expr, &boxed_seq_typ, _path, typs, context)
        self.build_model_constant(var.clone(), &unboxed_view_expr, &seq_typ, context)
    }

    pub fn build_model_def(
        &self,
        var: &Ident, // this is just for tracking the variable that owns this constant. For struct/enum/seq/etc, a single variable can own multiple constants
        expr: &ModelExpr,
        typ: &Typ,
        context: &mut air::context::Context,
    ) -> Result<ModelDef, String> {
        let value = self.build_model_constant(var.clone(), expr, typ, context)?;
        Ok(Arc::new(ModelDefX {
            name: var.clone(),
            typ: self.types.get(var).unwrap().clone(),
            value,
        }))
    }

    pub fn eval_variable(
        &self,
        var: &Ident,
        sid: &Ident,
        context: &mut air::context::Context,
    ) -> Result<ModelDef, String> {
        let var_string = var.to_string();

        let option_var = self.local_vars.get(var);
        match option_var {
            Some(_) => {}
            None => {
                return Err(format!(
                    "Error: cannot evaluate a variable which is not present in VIR local_vars, got {:?}",
                    var.to_string()
                ));
            }
        }

        // Query VIR Model first for immutable variables (see if this is produced when `build()`)
        let value = self.model.get(var);
        match value {
            Some(def) => {
                return Ok(def.clone());
            }
            _ => {
                println!("not found in VIR locals, this should be mutable variable:{}", var_string)
            }
        };
        let air_name = self.get_air_name(var, Some(sid.clone()));
        let typ = self.types.get(var).expect(format!("no type found for {:?}", var).as_str());
        let def = self.build_model_def(var, &Arc::new(ModelExprX::Var(air_name)), typ, context)?;
        Ok(def)
    }

    pub fn build(&mut self, context: &mut air::context::Context) {
        if self.model.len() > 0 {
            panic! {"Internal err: VIR model build precondition not satisfied"}
        }

        // gather datatype information for this counter example model -> self.datatypes
        for (_var, typ) in &self.types {
            match &**typ {
                TypX::Datatype(path, _typs) => {
                    let ident = &path.segments[0];
                    let dtyp = self.find_datatype(path.clone()).expect(
                        format!("VIR model error: datatype not found for {:?}", &*ident).as_str(),
                    );
                    self.datatypes.insert(path.clone(), dtyp.clone());
                }
                _ => {}
            };
        }

        // translate AIR model into VIR model
        // reference air::ast::typ, vir::ast::typ
        for var in &self.local_vars {
            // note that we are skipping mutable variables now
            if *self.is_mutable.get(var).unwrap() {
                println!("build skip for mutable var: {:?}", var);
                continue;
            };

            // println!("building {:?}", var);
            // TODO: use eval_variable here
            let typ = self.types.get(var).unwrap();
            let air_name = self.get_air_name(var, None);
            let def = self.build_model_def(var, &Arc::new(ModelExprX::Var(air_name)), typ, context);
            match def {
                Ok(model_def) => {
                    let _ = self.model.insert(var.clone(), model_def);
                }
                Err(err_info) => println!(
                    "VIR model constant build for variable {} failed. {}",
                    var.to_string(),
                    err_info
                ),
            };
        }

        println!(
            "VIR model built for immutable variables, you can also evaluate mutable variable through `set-line n` and `eval var`"
        );
        // for dd in &self.model {
        //     println!("{:?}", dd);
        // }
    }
}
