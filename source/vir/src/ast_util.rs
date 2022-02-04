use crate::ast::{
    BinaryOp, CallTarget, Constant, DatatypeX, Expr, ExprX, Fun, FunX, FunctionX, Ident, Idents,
    IntRange, Krate, Mode, Param, Params, Path, PathX, PatternX, SpannedTyped, Stmt, StmtX, Typ,
    TypX, Typs, Variant, Variants, VirErr, Visibility,
};
use crate::def::Spanned;
use crate::util::vec_map;
use air::ast::{Binder, BinderX, Binders, Span};
pub use air::ast_util::{ident_binder, str_ident};
use air::errors::error;
use std::fmt;
use std::sync::Arc;

/// Construct an Error and wrap it in Err.
/// For more complex Error objects, use the builder functions in air::errors

pub fn err_str<A>(span: &Span, msg: &str) -> Result<A, VirErr> {
    Err(error(msg, span))
}

pub fn err_string<A>(span: &Span, msg: String) -> Result<A, VirErr> {
    Err(error(msg, span))
}

impl PathX {
    pub fn pop_segment(&self) -> Path {
        let mut segments = (*self.segments).clone();
        segments.pop();
        Arc::new(PathX { krate: self.krate.clone(), segments: Arc::new(segments) })
    }
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mode::Spec => write!(f, "spec"),
            Mode::Proof => write!(f, "proof"),
            Mode::Exec => write!(f, "exec"),
        }
    }
}

pub fn types_equal(typ1: &Typ, typ2: &Typ) -> bool {
    match (&**typ1, &**typ2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(range1), TypX::Int(range2)) => range1 == range2,
        (TypX::Tuple(typs1), TypX::Tuple(typs2)) => n_types_equal(typs1, typs2),
        (TypX::Datatype(p1, typs1), TypX::Datatype(p2, typs2)) => {
            p1 == p2 && n_types_equal(typs1, typs2)
        }
        (TypX::Boxed(t1), TypX::Boxed(t2)) => types_equal(t1, t2),
        (TypX::TypParam(x1), TypX::TypParam(x2)) => x1 == x2,
        _ => false,
    }
}

pub fn n_types_equal(typs1: &Typs, typs2: &Typs) -> bool {
    typs1.len() == typs2.len() && typs1.iter().zip(typs2.iter()).all(|(t1, t2)| types_equal(t1, t2))
}

pub fn bitwidth_from_type(et: &Typ) -> Option<u32> {
    if let TypX::Int(IntRange::U(size)) = &**et {
        return Some(*size);
    }
    if let TypX::Int(IntRange::I(size)) = &**et {
        return Some(*size);
    }
    None
}

pub fn path_as_rust_name(path: &Path) -> String {
    let krate = match &path.krate {
        None => "crate".to_string(),
        Some(krate) => krate.to_string(),
    };
    let mut strings: Vec<String> = vec![krate];
    for segment in path.segments.iter() {
        strings.push(segment.to_string());
    }
    strings.join("::")
}

pub fn fun_as_rust_dbg(fun: &Fun) -> String {
    let FunX { path, trait_path } = &**fun;
    let path_str = path_as_rust_name(path);
    if let Some(trait_path) = trait_path {
        let trait_path_str = path_as_rust_name(trait_path);
        format!("{}<{}>", path_str, trait_path_str)
    } else {
        path_str
    }
}

// Can source_module see an item owned by owning_module?
pub fn is_visible_to_of_owner(owning_module: &Option<Path>, source_module: &Path) -> bool {
    let sources = &source_module.segments;
    match owning_module {
        None => true,
        Some(target) if target.segments.len() > sources.len() => false,
        Some(target) => {
            // Child can access private item in parent, so check if target is parent:
            let targets = &target.segments;
            target.krate == source_module.krate && targets[..] == sources[..targets.len()]
        }
    }
}

// Can source_module see an item with target_visibility?
pub fn is_visible_to(target_visibility: &Visibility, source_module: &Path) -> bool {
    let Visibility { owning_module, is_private } = target_visibility;
    !is_private || is_visible_to_of_owner(owning_module, source_module)
}

impl<X> SpannedTyped<X> {
    pub fn new(span: &Span, typ: &Typ, x: X) -> Arc<Self> {
        Arc::new(SpannedTyped { span: span.clone(), typ: typ.clone(), x })
    }

    pub fn new_x(&self, x: X) -> Arc<Self> {
        Arc::new(SpannedTyped { span: self.span.clone(), typ: self.typ.clone(), x })
    }
}

pub fn mk_bool(span: &Span, b: bool) -> Expr {
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExprX::Const(Constant::Bool(b)))
}

pub fn mk_implies(span: &Span, e1: &Expr, e2: &Expr) -> Expr {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Bool),
        ExprX::Binary(BinaryOp::Implies, e1.clone(), e2.clone()),
    )
}

pub fn chain_binary(span: &Span, op: BinaryOp, init: &Expr, exprs: &Vec<Expr>) -> Expr {
    let mut expr = init.clone();
    for e in exprs.iter() {
        expr = SpannedTyped::new(span, &init.typ, ExprX::Binary(op, expr, e.clone()));
    }
    expr
}

pub fn conjoin(span: &Span, exprs: &Vec<Expr>) -> Expr {
    chain_binary(span, BinaryOp::And, &mk_bool(span, true), exprs)
}

pub fn mk_call(span: &Span, ty: &Typ, call_target: &CallTarget, args: &Vec<Expr>) -> Expr {
    SpannedTyped::new(span, ty, ExprX::Call(call_target.clone(), Arc::new(args.clone())))
}

pub fn mk_and(span: &Span, e1: Expr, e2: &Expr) -> Expr {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Bool),
        ExprX::Binary(BinaryOp::And, e1.clone(), e2.clone()),
    )
}

pub fn mk_or(span: &Span, e1: &Expr, e2: &Expr) -> Expr {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Bool),
        ExprX::Binary(BinaryOp::Or, e1.clone(), e2.clone()),
    )
}

pub fn mk_eq(span: &Span, m: Mode, e1: &Expr, e2: &Expr) -> Expr {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Bool),
        ExprX::Binary(BinaryOp::Eq(m), e1.clone(), e2.clone()),
    )
}

pub fn mk_ife(span: &Span, e1: &Expr, e2: &Expr, e3: &Expr) -> Expr {
    assert!(types_equal(&e2.typ, &e3.typ));
    SpannedTyped::new(span, &e2.typ, ExprX::If(e1.clone(), e2.clone(), Some(e3.clone())))
}

pub fn mk_assume(span: &Span, e: &Expr) -> Expr {
    let unit_ty = Arc::new(TypX::Tuple(Arc::new(Vec::new())));
    SpannedTyped::new(span, &unit_ty, ExprX::Assume(e.clone()))
}

pub fn mk_assert(span: &Span, e: &Expr) -> Expr {
    let unit_ty = Arc::new(TypX::Tuple(Arc::new(Vec::new())));
    SpannedTyped::new(span, &unit_ty, ExprX::Assert(None, e.clone()))
}

pub fn mk_decl_stmt(span: &Span, mode: Mode, mutable: bool, ident: &Ident, e: &Expr) -> Stmt {
    Spanned::new(
        span.clone(),
        StmtX::Decl {
            pattern: SpannedTyped::new(
                span,
                &e.typ,
                PatternX::Var { name: ident.clone(), mutable },
            ),
            mode,
            init: Some(e.clone()),
        },
    )
}

pub fn mk_var(span: &Span, ty: &Typ, s: String) -> Expr {
    SpannedTyped::new(span, ty, ExprX::Var(Arc::new(s)))
}

pub fn param_to_binder(param: &Param) -> Binder<Typ> {
    Arc::new(BinderX { name: param.x.name.clone(), a: param.x.typ.clone() })
}

pub fn params_to_binders(params: &Params) -> Binders<Typ> {
    Arc::new(vec_map(&**params, param_to_binder))
}

impl FunctionX {
    // unit return values are treated as no return value
    pub fn has_return(&self) -> bool {
        match &*self.ret.x.typ {
            TypX::Tuple(ts) if ts.len() == 0 => false,
            TypX::Datatype(path, _) if path == &crate::def::prefix_tuple_type(0) => false,
            _ => true,
        }
    }

    pub fn typ_params(&self) -> Idents {
        Arc::new(vec_map(&self.typ_bounds, |(x, _)| x.clone()))
    }
}

pub fn get_variant<'a>(variants: &'a Variants, variant: &Ident) -> &'a Variant {
    match variants.iter().find(|v| v.name == *variant) {
        Some(variant) => variant,
        None => panic!("internal error: missing variant {}", &variant),
    }
}

pub fn get_field<'a, A: Clone>(variant: &'a Binders<A>, field: &Ident) -> &'a Binder<A> {
    match variant.iter().find(|f| f.name == *field) {
        Some(field) => field,
        None => panic!("internal error: missing field {}", &field),
    }
}

impl DatatypeX {
    pub fn get_only_variant(&self) -> &Variant {
        assert_eq!(self.variants.len(), 1);
        &self.variants[0]
    }

    pub fn get_variant(&self, variant: &Ident) -> &Variant {
        get_variant(&self.variants, variant)
    }
}

pub fn debug_write(mut write: impl std::io::Write, vir_crate: &Krate) {
    for datatype in vir_crate.datatypes.iter() {
        writeln!(&mut write, "datatype {:?} @ {:?}", datatype.x.path, datatype.span)
            .expect("cannot write to vir write");
        writeln!(&mut write, "{:?}", datatype.x.variants).expect("cannot write to vir write");
        writeln!(&mut write).expect("cannot write to vir write");
    }
    for func in vir_crate.functions.iter() {
        writeln!(&mut write, "fn {} @ {:?}", fun_as_rust_dbg(&func.x.name), func.span)
            .expect("cannot write to vir write");
        writeln!(
            &mut write,
            "visibility {:?} mode {:?} fuel {} is_abstract {}",
            func.x.visibility, func.x.mode, func.x.fuel, func.x.is_abstract
        )
        .expect("cannot write to vir write");
        for require in func.x.require.iter() {
            writeln!(&mut write, "requires {:#?}", require).expect("cannot write to vir write");
        }
        for ensure in func.x.ensure.iter() {
            writeln!(&mut write, "ensures {:#?}", ensure).expect("cannot write to vir write");
        }
        for param in func.x.params.iter() {
            writeln!(
                &mut write,
                "parameter {}: {:?} @ {:?}",
                param.x.name, param.x.typ, param.span
            )
            .expect("cannot write to vir write");
        }
        writeln!(&mut write, "returns {:?}", func.x.ret).expect("cannot write to vir write");
        writeln!(&mut write, "body {:#?}", func.x.body).expect("cannot write to vir write");
        writeln!(&mut write).expect("cannot write to vir write");
    }
}
