use crate::ast::{
    CallTarget, Datatype, ExprX, Fun, FunX, Function, Krate, MaskSpec, Mode, Path, PathX, TypX,
    UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string};
use crate::datatype_to_air::is_datatype_transparent;
use crate::early_exit_cf::assert_no_early_exit_in_inv_block;
use std::collections::HashMap;
use std::sync::Arc;

struct Ctxt {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) dts: HashMap<Path, Datatype>,
}

fn check_function(ctxt: &Ctxt, function: &Function) -> Result<(), VirErr> {
    for p in function.x.params.iter() {
        if p.x.name == function.x.ret.x.name {
            return err_str(&p.span, "parameter name cannot be same as return value name");
        }
    }

    if function.x.attrs.atomic {
        if function.x.mode != Mode::Exec {
            return err_str(&function.span, "'atomic' only makes sense on an 'exec' function");
        }
        if function.x.body.is_some() {
            return err_str(
                &function.span,
                "'atomic' is a trusted annotation: it may not be used on a verified function",
            );
        }
    }
    match &function.x.mask_spec {
        MaskSpec::NoSpec => {}
        _ => {
            if function.x.mode == Mode::Spec {
                return err_str(&function.span, "invariants cannot be opened in spec functions");
            }
        }
    }
    if function.x.attrs.broadcast_forall {
        if function.x.mode != Mode::Proof {
            return err_str(&function.span, "broadcast_forall function must be declared as proof");
        }
        if function.x.has_return() {
            return err_str(&function.span, "broadcast_forall function cannot have return type");
        }
        for param in function.x.params.iter() {
            if param.x.mode != Mode::Spec {
                return err_str(
                    &function.span,
                    "broadcast_forall function must have spec parameters",
                );
            }
        }
        if function.x.body.is_some() {
            return err_str(
                &function.span,
                "broadcast_forall function must be declared as external_body",
            );
        }
    }

    if function.x.attrs.bit_vector {
        // TODO: return error if function has a non-integer type, or function call
        unimplemented!("function level bitvector mode");
    }

    if function.x.attrs.autoview {
        if function.x.mode == Mode::Spec {
            return err_str(&function.span, "autoview function cannot be declared spec");
        }
        let mut segments = (*function.x.name.path.segments).clone();
        *segments.last_mut().expect("autoview segments") = Arc::new("view".to_string());
        let segments = Arc::new(segments);
        let path = Arc::new(PathX { segments, ..(*function.x.name.path).clone() });
        let fun = Arc::new(FunX { path, ..(*function.x.name).clone() });
        if let Some(f) = ctxt.funs.get(&fun) {
            if f.x.params.len() != 1 {
                return err_str(
                    &f.span,
                    "because of autoview, view() function must have 0 paramters",
                );
            }
            let typ_args = if let TypX::Datatype(_, args) = &*f.x.params[0].x.typ {
                args.clone()
            } else {
                panic!("autoview_typ must be Datatype")
            };
            assert!(typ_args.len() <= f.x.typ_bounds.len());
            if f.x.typ_bounds.len() != typ_args.len() {
                return err_str(
                    &f.span,
                    "because of autoview, view() function must have 0 type paramters",
                );
            }
            if f.x.mode != Mode::Spec {
                return err_str(
                    &f.span,
                    "because of autoview, view() function must be declared spec",
                );
            }
        } else {
            return err_str(
                &function.span,
                "autoview function must have corresponding view() function",
            );
        }
    }
    for req in function.x.require.iter() {
        crate::ast_visitor::expr_visitor_check(req, &mut |expr| {
            if let ExprX::Var(x) = &expr.x {
                for param in function.x.params.iter().filter(|p| p.x.is_mut) {
                    if *x == param.x.name {
                        return err_string(
                            &expr.span,
                            format!(
                                "in requires, use `old({})` to refer to the pre-state of an &mut variable",
                                param.x.name
                            ),
                        );
                    }
                }
            }
            Ok(())
        })?;
    }
    if let Some(body) = &function.x.body {
        // Check that public, non-abstract spec function bodies don't refer to private items:
        let disallow_private_access = function.x.publish.is_some()
            && !function.x.visibility.is_private
            && function.x.mode == Mode::Spec;

        crate::ast_visitor::expr_visitor_check(body, &mut |expr| {
            match &expr.x {
                ExprX::Call(CallTarget::Static(x, _), args) => {
                    let f = &ctxt.funs[x];
                    for (_param, arg) in
                        f.x.params.iter().zip(args.iter()).filter(|(p, _)| p.x.is_mut)
                    {
                        let ok = match &arg.x {
                            ExprX::Loc(l) => match l.x {
                                ExprX::VarLoc(_) => true,
                                _ => false,
                            },
                            _ => false,
                        };
                        if !ok {
                            return err_str(
                                &arg.span,
                                "complex arguments to &mut parameters are currently unsupported",
                            );
                        }
                    }
                    if disallow_private_access {
                        let callee = &ctxt.funs[x];
                        if callee.x.visibility.is_private {
                            return err_string(
                                &expr.span,
                                format!(
                                    "public spec function cannot refer to private items, when it is marked #[verifier(publish)]"
                                ),
                            );
                        }
                    }
                }
                ExprX::Ctor(path, _variant, _fields, _update) => {
                    if let Some(dt) = ctxt.dts.get(path) {
                        if let Some(module) = &function.x.visibility.owning_module {
                            if !is_datatype_transparent(&module, dt) {
                                return err_string(
                                    &expr.span,
                                    format!("constructor of datatype with unencoded fields here"),
                                );
                            }
                        }
                    } else {
                        panic!("constructor of undefined datatype");
                    }
                }
                ExprX::UnaryOpr(UnaryOpr::Field { datatype: path, variant, field }, _) => {
                    if let Some(dt) = ctxt.dts.get(path) {
                        if let Some(module) = &function.x.visibility.owning_module {
                            if !is_datatype_transparent(&module, dt) {
                                return err_string(
                                    &expr.span,
                                    format!("field access of datatype with unencoded fields here"),
                                );
                            }
                        }
                        if disallow_private_access {
                            let variant = dt.x.get_variant(variant);
                            let (_, _, vis) = &crate::ast_util::get_field(&variant.a, &field).a;
                            if vis.is_private {
                                return err_string(
                                    &expr.span,
                                    format!(
                                        "public spec function cannot refer to private items, if it is marked #[verifier(publish)]"
                                    ),
                                );
                            }
                        }
                    } else {
                        panic!("field access of undefined datatype");
                    }
                }
                ExprX::OpenInvariant(_inv, _binder, body) => {
                    assert_no_early_exit_in_inv_block(&body.span, body)?;
                }
                _ => {}
            }
            Ok(())
        })?;
    }
    Ok(())
}

fn check_datatype(dt: &Datatype) -> Result<(), VirErr> {
    let unforgeable = dt.x.unforgeable;
    let dt_mode = dt.x.mode;

    if unforgeable && dt_mode != Mode::Proof {
        return err_string(&dt.span, format!("an unforgeable datatype must be in #[proof] mode"));
    }

    // For an 'unforgeable' datatype, all fields must be #[spec]

    if unforgeable {
        for variant in dt.x.variants.iter() {
            for binder in variant.a.iter() {
                let (_typ, field_mode, _vis) = &binder.a;
                if *field_mode != Mode::Spec {
                    return err_string(
                        &dt.span,
                        format!("all fields of a unforgeable datatype must be marked #[spec]"),
                    );
                }
            }
        }
    }

    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<(), VirErr> {
    let funs = krate
        .functions
        .iter()
        .map(|function| (function.x.name.clone(), function.clone()))
        .collect();
    let dts = krate
        .datatypes
        .iter()
        .map(|datatype| (datatype.x.path.clone(), datatype.clone()))
        .collect();
    let ctxt = Ctxt { funs, dts };
    for function in krate.functions.iter() {
        check_function(&ctxt, function)?;
    }
    for dt in krate.datatypes.iter() {
        check_datatype(dt)?;
    }
    crate::recursive_types::check_recursive_types(krate)?;
    Ok(())
}
