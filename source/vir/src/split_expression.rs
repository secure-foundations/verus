use crate::ast::{
    BinaryOp, Expr, Function, Idents, Params, SpannedTyped, Typ, TypX, Typs, UnaryOp,
};
use crate::ast_to_sst::{expr_to_pure_exp, get_function};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Exp, ExpX, Exps};
use air::ast::{Binder, BinderX, Span};
use core::panic;
use std::collections::HashMap;
use std::sync::Arc;

fn subsitute_argument(
    exp: &Exp,
    arg_map: &HashMap<Arc<String>, Exp>,
) -> Result<Exp, (Span, String)> {
    let result = match &exp.x {
        ExpX::Var((id, _num)) => {
            // println!("id: {:?}", id);
            match arg_map.get(id) {
                Some(e) => e.clone(),
                None => exp.clone(),
            }
        }
        ExpX::Call(x, typs, es) => {
            let mut es_replaced = vec![];
            for e in es.iter() {
                let e_replaced = subsitute_argument(e, arg_map)?;
                es_replaced.push(e_replaced);
            }
            let new_exp = ExpX::Call(x.clone(), typs.clone(), Arc::new(es_replaced));
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Unary(op, e1) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let new_exp = ExpX::Unary(*op, e1_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::UnaryOpr(uop, e1) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let new_exp = ExpX::UnaryOpr(uop.clone(), e1_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Binary(bop, e1, e2) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let e2_replaced = subsitute_argument(e2, arg_map)?;
            let new_exp = ExpX::Binary(*bop, e1_replaced, e2_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::If(e1, e2, e3) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let e2_replaced = subsitute_argument(e2, arg_map)?;
            let e3_replaced = subsitute_argument(e3, arg_map)?;
            let new_exp = ExpX::If(e1_replaced, e2_replaced, e3_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Bind(bnd, e1) => {
            // TODO: check if binded name and  `var to replace` is same
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let bnd_replaced: Bnd = match &bnd.x {
                BndX::Let(binders) => {
                    let mut new_binders: Vec<Binder<Exp>> = vec![];
                    for old_b in &**binders {
                        let new_b = BinderX {
                            name: old_b.name.clone(),
                            a: subsitute_argument(&old_b.a, arg_map)?,
                        };
                        new_binders.push(Arc::new(new_b));
                    }
                    Spanned::new(bnd.span.clone(), BndX::Let(Arc::new(new_binders)))
                }
                BndX::Quant(quant, bndrs, trigs) => {
                    // replace vars in trigger
                    let mut replaced_trigs: Vec<crate::sst::Trig> = vec![];
                    for ts in &***trigs {
                        let mut replaced_ts: Vec<Exp> = vec![];
                        for t in &**ts {
                            replaced_ts.push(subsitute_argument(t, arg_map)?);
                        }
                        replaced_trigs.push(Arc::new(replaced_ts));
                    }
                    Spanned::new(
                        bnd.span.clone(),
                        BndX::Quant(quant.clone(), bndrs.clone(), Arc::new(replaced_trigs)),
                    )
                }
                _ => return Err((exp.span.clone(), format!("TODO: binders, subsitute_argument"))),
            };
            let new_exp = ExpX::Bind(bnd_replaced, e1_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Const(_) => exp.clone(),
        _ => {
            // | ExpX::WithTriggers(_, _) => exp.clone()
            // VarLoc(UniqueIdent),
            // VarAt(UniqueIdent, VarAt),
            // Loc(Exp),
            // Old(Ident, UniqueIdent),
            // CallLambda(Typ, Exp, Exps),
            // Ctor(Path, Ident, Binders<Exp>),
            // WithTriggers(Trigs, Exp),
            return Err((exp.span.clone(), format!("TODO: unsubsituted exp, subsitute_argument ")));
        }
    };
    Ok(result)
}

// e1: param, e2: exp_to_replace
fn assert_same_type(param_typ: &Typ, e2: &Exp) -> Result<(), (Span, String)> {
    match (&**param_typ, &*e2.typ) {
        (TypX::Bool, TypX::Bool) |
        (TypX::Int(_),TypX::Int(_)) |
        (TypX::Tuple(_), TypX::Tuple(_)) |
        (TypX::Lambda(_, _), TypX::Lambda(_,_)) |
        (TypX::Datatype(_, _), TypX::Datatype(_,_)) |
        // TODO: recursive check instead
        (TypX::Boxed(_), TypX::Boxed(_)) |
        (TypX::TypParam(_), TypX::TypParam(_)) |
        (TypX::TypeId, TypX::TypeId) |
        (TypX::Air(_), TypX::Air(_)) => Ok(()),
        _ => return Err((e2.span.clone(), "TODO or interal error: arg type mismatch during function inlining".to_string())),
    }
}
pub(crate) fn tr_inline_expression(
    body_exp: &Exp,
    params: &Params,
    exps: &Exps,
) -> Result<Exp, (Span, String)> {
    let mut arg_map: HashMap<Arc<String>, Exp> = HashMap::new();
    let mut count = 0;
    for param in &**params {
        let exp_to_insert = &exps[count];
        assert_same_type(&param.x.typ, exp_to_insert)?;
        arg_map.insert(param.x.name.clone(), exp_to_insert.clone());
        count = count + 1;
    }
    return subsitute_argument(body_exp, &arg_map);
}

pub(crate) fn pure_ast_expression_to_sst(ctx: &Ctx, body: &Expr, params: &Params) -> Exp {
    let pars = crate::func_to_air::params_to_pars(params, false);
    let mut state = crate::ast_to_sst::State::new();
    state.declare_params(&pars);
    state.view_as_spec = true;
    let body_exp = expr_to_pure_exp(&ctx, &mut state, &body).expect("pure_ast_expression_to_sst");
    state.finalize_exp(&body_exp)
}

// simply inline, the caller of `inline` should call `split_expr` with the inlined expr.
fn tr_inline_function(ctx: &Ctx, fun: Function, exps: &Exps) -> Result<Exp, (Span, String)> {
    // TODO: check the visibility of the function
    //       when the function is not visible, remind the user that it is not visible
    // then return Err
    // let visibile = fun.x.attrs.hidden;    // `fun` here should be the holder of the failing assertion

    let body = fun.x.body.as_ref().unwrap();
    let params = &fun.x.params;
    let body_exp = pure_ast_expression_to_sst(ctx, body, params);
    return tr_inline_expression(&body_exp, params, exps);
}

// trace
// 1) when inlining function, log call stack into `trace`
// 2) boolean negation
pub type TracedExp = Arc<TracedExpX>;
pub type TracedExps = Arc<Vec<TracedExp>>;
pub struct TracedExpX {
    pub e: Exp,
    pub trace: air::errors::Error,
}
impl TracedExpX {
    pub fn new(e: Exp, trace: air::errors::Error) -> TracedExp {
        Arc::new(TracedExpX { e, trace })
    }
}

fn negate_atom(exp: &TracedExp) -> TracedExp {
    let negated_expx = ExpX::Unary(UnaryOp::Not, exp.e.clone());
    let negated_exp = SpannedTyped::new(&exp.e.span, &exp.e.typ, negated_expx);
    TracedExpX::new(negated_exp, exp.trace.clone())
}

fn merge_two_es(es1: TracedExps, es2: TracedExps) -> TracedExps {
    let mut merged_vec = vec![];
    for e in &*es1 {
        merged_vec.push(e.clone());
    }
    for e in &*es2 {
        merged_vec.push(e.clone());
    }
    return Arc::new(merged_vec);
}

// Note: this splitting referenced Dafny
// https://github.com/dafny-lang/dafny/blob/cf285b9282499c46eb24f05c7ecc7c72423cd878/Source/Dafny/Verifier/Translator.cs#L11100
pub fn split_expr(ctx: &Ctx, exp: &TracedExp, negated: bool) -> TracedExps {
    match *exp.e.typ {
        TypX::Bool => (),
        _ => panic!("cannot split non boolean expression"),
    }
    match &exp.e.x {
        ExpX::Unary(UnaryOp::Not, e1) => {
            let tr_exp = TracedExpX::new(
                e1.clone(),
                exp.trace.secondary_label(
                    &exp.e.span,
                    "This leftmost boolean-not negated the highlighted expression",
                ),
            );
            return split_expr(ctx, &tr_exp, !negated);
        }
        ExpX::Binary(bop, e1, e2) => {
            match bop {
                BinaryOp::And if !negated => {
                    let es1 =
                        split_expr(ctx, &TracedExpX::new(e1.clone(), exp.trace.clone()), false);
                    let es2 =
                        split_expr(ctx, &TracedExpX::new(e2.clone(), exp.trace.clone()), false);
                    return merge_two_es(es1, es2);
                }
                // apply DeMorgan's Law
                BinaryOp::Or if negated => {
                    let es1 =
                        split_expr(ctx, &TracedExpX::new(e1.clone(), exp.trace.clone()), true);
                    let es2 =
                        split_expr(ctx, &TracedExpX::new(e2.clone(), exp.trace.clone()), true);
                    return merge_two_es(es1, es2);
                }
                // in case of implies, split rhs. (e.g.  A => (B && C)  to  [ (A => B) , (A => C) ] )
                BinaryOp::Implies if !negated => {
                    let es2 =
                        split_expr(ctx, &TracedExpX::new(e2.clone(), exp.trace.clone()), negated);
                    let mut splitted: Vec<TracedExp> = vec![];
                    for e in &*es2 {
                        let new_e = ExpX::Binary(BinaryOp::Implies, e1.clone(), e.e.clone());
                        let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                        let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                        splitted.push(new_tr_exp);
                    }
                    return Arc::new(splitted);
                }
                // TODO
                // BinaryOp::Implies if negated
                _ if negated => return Arc::new(vec![negate_atom(exp)]),
                _ => return Arc::new(vec![exp.clone()]),
            }
        }
        ExpX::Call(fun_name, typs, exps) => {
            let fun = get_function(ctx, &exp.e.span, fun_name).unwrap();
            let res_inlined_exp = tr_inline_function(ctx, fun, exps);
            match res_inlined_exp {
                Ok(inlined_exp) => {
                    // println!("inlined exp: {:?}", inlined_exp);
                    let inlined_tr_exp = TracedExpX::new(
                        inlined_exp,
                        exp.trace.primary_label(&exp.e.span, "TODO: pretty print inlined expr"),
                    );
                    return split_expr(ctx, &inlined_tr_exp, negated);
                }
                Err((sp, msg)) => {
                    println!("inline failed for {:?}", fun_name);
                    let not_inlined_exp =
                        TracedExpX::new(exp.e.clone(), exp.trace.primary_label(&sp, msg));
                    // stop inlining. treat as atom
                    if negated {
                        return Arc::new(vec![negate_atom(&not_inlined_exp)]);
                    } else {
                        return Arc::new(vec![not_inlined_exp]);
                    }
                }
            }
        }
        ExpX::If(e1, e2, e3) if !negated => {
            let then_e = ExpX::Binary(BinaryOp::Implies, e1.clone(), e2.clone());
            let then_exp = SpannedTyped::new(&e2.span, &exp.e.typ, then_e);

            let not_e1 =
                SpannedTyped::new(&e1.span, &exp.e.typ, ExpX::Unary(UnaryOp::Not, e1.clone()));
            let else_e = ExpX::Binary(BinaryOp::Implies, not_e1, e3.clone());
            let else_exp = SpannedTyped::new(&e3.span, &exp.e.typ, else_e);

            let es1 =
                split_expr(ctx, &TracedExpX::new(then_exp.clone(), exp.trace.clone()), negated);
            let es2 =
                split_expr(ctx, &TracedExpX::new(else_exp.clone(), exp.trace.clone()), negated);
            return merge_two_es(es1, es2);
        }
        ExpX::UnaryOpr(uop, e1) => {
            let es1 = split_expr(ctx, &TracedExpX::new(e1.clone(), exp.trace.clone()), negated);
            let mut splitted: Vec<TracedExp> = vec![];
            for e in &*es1 {
                let new_e = ExpX::UnaryOpr(uop.clone(), e.e.clone());
                let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                splitted.push(new_tr_exp);
            }
            return Arc::new(splitted);
        }
        ExpX::Bind(bnd, e1) => {
            let es1 = split_expr(ctx, &TracedExpX::new(e1.clone(), exp.trace.clone()), negated);
            let mut splitted: Vec<TracedExp> = vec![];
            for e in &*es1 {
                // REVIEW: should I split expression in `let sth = exp`?
                let new_expx = ExpX::Bind(bnd.clone(), e.e.clone());
                let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_expx);
                let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                splitted.push(new_tr_exp);
            }
            return Arc::new(splitted);
        }

        // TODO: more cases

        // cases that cannot be splitted. "atom" boolean expressions
        _ if negated => return Arc::new(vec![negate_atom(exp)]),
        _ => {
            // println!("unsplitted: {:?}", exp.e.x);
            return Arc::new(vec![exp.clone()]);
        }
    }
}
