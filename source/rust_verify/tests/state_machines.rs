#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use crate::pervasive::{atomic::*};
    #[allow(unused_imports)] use crate::pervasive::{modes::*};
    #[allow(unused_imports)] use crate::pervasive::result::*;
    #[allow(unused_imports)] use crate::pervasive::option::*;
    #[allow(unused_imports)] use crate::pervasive::map::*;
    #[allow(unused_imports)] use crate::pervasive::multiset::*;
    #[allow(unused_imports)] use builtin::*;
    #[allow(unused_imports)] use builtin_macros::*;
    #[allow(unused_imports)] use state_machines_macros::*;

    #[spec]
    #[is_variant]
    pub enum Foo {
        Bar(int),
        Qax(int),
        Duck(int),
    }
};

test_verify_one_file! {
    #[test] test_birds_eye_init_error IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields { #[sharding(variable)] pub t: int }

            init!{
                initialize() {
                    birds_eye let x = 5; // error
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "`birds_eye` has no effect in an init!")
}

test_verify_one_file! {
    #[test] test_birds_eye_nontokenized_error IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields { pub t: int }

            transition!{
                tr() {
                    birds_eye let x = 5; // error
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "`birds_eye` only makes sense for tokenized state machines")
}

test_verify_one_file! {
    #[test] test_birds_eye_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    birds_eye let x = 5;
                    guard so >= Some(x); // error: guard depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "a guard value must be a deterministic function")
}

test_verify_one_file! {
    #[test] test_withdraw_bind_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    withdraw so -= Some(let y);
                    guard so >= Some(x); // error: guard depends on withdraw binding
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "a guard value must be a deterministic function")
}

test_verify_one_file! {
    #[test] test_birds_eye_req IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    birds_eye let x = 5;
                    require(x == 5); // error: require depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'require' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_one_file! {
    #[test] test_withdraw_bind_req IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    withdraw so -= Some(let x);
                    require(x == 5); // error: require depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'require' statements should not be in the scope of a `withdraw` let-binding")
}

test_verify_one_file! {
    #[test] test_birds_eye_req2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    if 0 == 0 {
                        birds_eye let x = 5;
                        assert(x == 5);
                    }
                    require(x == 5); // error: require depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'require' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_one_file! {
    #[test] test_withdraw_bind_req2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    if 0 == 0 {
                        withdraw so -= Some(let x);
                        assert(x == 5);
                    }
                    require(x == 5); // error: require depends on withdraw binding
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'require' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_one_file! {
    #[test] test_birds_eye_special IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub so: Option<int>
            }

            transition!{
                tr() {
                    birds_eye let x = 5;
                    remove so -= Some(x); // error: depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'remove' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_one_file! {
    #[test] test_withdraw_binding_remove IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub so: Option<int>
            }

            transition!{
                tr() {
                    withdraw so -= Some(let x);
                    remove so -= Some(x); // error: depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'remove' statements should not be in the scope of a `withdraw` let-binding")
}

test_verify_one_file! {
    #[test] test_birds_eye_special2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub so: Option<int>
            }

            transition!{
                tr() {
                    if 0 == 0 {
                        birds_eye let x = 5;
                        assert(x == 5);
                    }
                    remove so -= Some(0); // error: depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'remove' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_one_file! {
    #[test] test_update_constant IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(constant)] pub t: int
            }

            transition!{
                tr() {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'update' statement not allowed for field with sharding strategy 'constant'")
}

test_verify_one_file! {
    #[test] test_use_option_directly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub t: Option<int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t.get_Some_0();
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_map_directly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)] pub t: Map<int, int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t.index(0);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_multiset_directly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)] pub t: Multiset<int>,
                #[sharding(variable)] pub v: Multiset<int>,
            }

            transition!{
                tr() {
                    update v = pre.t;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_storage_option_directly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub t: Option<int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t.get_Some_0();
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_nottokenized_directly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(not_tokenized)] pub t: int,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = { let s = pre; s.v };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field_withdraw_kv_value IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)] pub v: Map<int, int>,
            }

            transition!{
                tr() {
                    withdraw v -= [5 => { let s = pre; s.v } ];
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field_remove_kv_key IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)] pub v: Map<int, int>,
            }

            transition!{
                tr() {
                    remove v -= [5 => { let s = pre; s.v } ];
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field_withdraw_kv_key IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)] pub v: Map<int, int>,
            }

            init!{
                initialize() {
                    init v = Map::empty();
                }
            }

            transition!{
                tr() {
                    // this is ok:
                    withdraw v -= [{ let s = pre; s.v.index(0) } => 5]
                          by { assume(false); };
                }
            }
        }}

        fn foo(#[proof] m: Map<int, int>) {
            requires(equal(m, Map::empty()));

            #[proof] let inst = X::Instance::initialize(m);
            #[proof] let t = inst.tr();
            assert(equal(t, 5));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_use_pre_no_field2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.some_fn();
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "`pre` cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field3 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.not_a_field;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "any field access must be a state field")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field4 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.0;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "expected a named field")
}

test_verify_one_file! {
    #[test] field_name_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub instance: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] field_name_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub token_a: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] sm_name_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ instance {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] sm_name_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ token_a {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] let_name_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr() {
                    let instance = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] let_name_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr() {
                    let token_a = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] arg_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(instance: int) {
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] arg_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(token_a: int) {
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] binding_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub t: Option<int>,
            }

            transition!{
                tr() {
                    remove t -= Some(let instance);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] duplicate_inductive_lemma IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                    update t = x;
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }

            #[inductive(tr)]
            pub fn lemma_tr2(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_error_msg(e, "duplicate 'inductive' lemma")
}

test_verify_one_file! {
    #[test] missing_inductive_lemma IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                    update t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }
        }}
    } => Err(e) => assert_error_msg(e, "missing inductiveness proofs for")
}

test_verify_one_file! {
    #[test] missing_inductive_lemma_init IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }
        }}
    } => Err(e) => assert_error_msg(e, "missing inductiveness proofs for")
}

test_verify_one_file! {
    #[test] inductive_lemma_readonly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            readonly!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_error_msg(e, "'inductive' lemma does not make sense for a 'readonly' transition")
}

test_verify_one_file! {
    #[test] lemma_wrong_args IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, y: int) {
            }
        }}
    } => Err(e) => assert_error_msg(e, "params for 'inductive' lemma should be")
}

test_verify_one_file! {
    #[test] lemma_bad_transition_name IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tro)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_error_msg(e, "could not find transition")
}

test_verify_one_file! {
    #[test] lemma_bad_generic_params IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1<T>(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_error_msg(e, "should have no generic parameters")
}

test_verify_one_file! {
    #[test] lemma_bad_return_type IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) -> bool {
            }
        }}
    } => Err(e) => assert_error_msg(e, "should have no return type")
}

test_verify_one_file! {
    #[test] lemma_bad_header IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
                requires(true);
            }
        }}
    } => Err(e) => assert_error_msg(e, "the precondition and postcondition are implicit")
}

test_verify_one_file! {
    #[test] lemma_doesnt_verify IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                    update t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] lemma_doesnt_verify_init IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }

            #[inductive(tr)]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] sm_generic_param_not_type IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X<'a> {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "Only generic type parameters are supported")
}

test_verify_one_file! {
    #[test] multiple_fields IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            fields {
                #[sharding(variable)] pub x: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "Expected only one declaration of `fields` block")
}

test_verify_one_file! {
    #[test] no_fields IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
        }}
    } => Err(e) => assert_error_msg(e, "'fields' declaration was not found")
}

test_verify_one_file! {
    #[test] conflicting_attrs IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            #[inductive(tr)]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }
        }}
    } => Err(e) => assert_error_msg(e, "conflicting attributes")
}

test_verify_one_file! {
    #[test] explicit_mode_inv IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            #[spec]
            pub fn the_inv(self) -> bool {
                true
            }
        }}
    } => Err(e) => assert_error_msg(e, "should not be explicitly labelled")
}

test_verify_one_file! {
    #[test] explicit_mode_field IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] #[spec] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "should not be explicitly labelled")
}

test_verify_one_file! {
    #[test] explicit_mode_proof IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                true
            }

            #[inductive(tr)]
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_error_msg(e, "should not be explicitly labelled")
}

test_verify_one_file! {
    #[test] inv_wrong_params IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(x: int) -> bool {
                true
            }

            #[inductive(tr)]
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_error_msg(e, "an invariant function must take 1 argument (self)")
}

test_verify_one_file! {
    #[test] inv_wrong_ret IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> int {
                5
            }

            #[inductive(tr)]
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_error_msg(e, "an invariant function must return a bool")
}

test_verify_one_file! {
    #[test] inv_wrong_generics IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv<V>(self) -> bool {
                true
            }

            #[inductive(tr)]
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_error_msg(e, "an invariant function must take 0 type arguments")
}

test_verify_one_file! {
    #[test] normal_sm_sharding IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "sharding strategy only makes sense for tokenized state machines")
}

test_verify_one_file! {
    #[test] tokenized_sm_no_sharding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "tokenized state machine requires a sharding strategy")
}

test_verify_one_file! {
    #[test] unrecognized_sharding_strategy_name IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(foo)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "unrecognized sharding strategy")
}

test_verify_one_file! {
    #[test] duplicate_sharding_attr IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                #[sharding(variable)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "duplicate sharding attribute")
}

test_verify_one_file! {
    #[test] wrong_form_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_option2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Multiset<int>,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_option3 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Map<int, int>,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_storage_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_map IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Map<_, _>")
}

test_verify_one_file! {
    #[test] wrong_form_storage_map IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Map<_, _>")
}

test_verify_one_file! {
    #[test] wrong_form_multiset IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Multiset<_>")
}

test_verify_one_file! {
    #[test] special_op_conditional IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    if true {
                        add t += Some(5);
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_one_file! {
    #[test] special_op_binding_conditional IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    if true {
                        remove t -= Some(let x);
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_one_file! {
    #[test] special_op_match IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr(foo: Foo) {
                    match foo {
                        Foo::Bar(x) => {
                            add t += Some(5);
                        }
                        Foo::Qax(y) => { }
                        Foo::Duck(z) => { }
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_one_file! {
    #[test] remove_after_have IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    have t >= Some(5);
                    remove t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] remove_after_have_with_binding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    have t >= Some(let z);
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] have_after_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                    have t >= Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] remove_after_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                    remove t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] init_wf_init_missing IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "procedure does not initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_dupe IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    init t = 5;
                    init t = 6;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "might be initialized multiple times")
}

test_verify_one_file! {
    #[test] init_wf_init_dupe_conditional IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    init t = 5;
                    if 1 + 2 == 3 {
                        init t = 6;
                    } else {
                        init t = 7;
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "might be initialized multiple times")
}

test_verify_one_file! {
    #[test] init_wf_init_if IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    if 1 + 2 == 3 {
                        init t = 6;
                    } else {
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "the else-branch does not initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_dupe_match IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init(foo: Foo) {
                    init t = 5;
                    match foo {
                        Foo::Bar(x) => { init t = 6; }
                        Foo::Qax(y) => { init t = 7; }
                        Foo::Duck(z) => { init t = 8; }
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "might be initialized multiple times")
}

test_verify_one_file! {
    #[test] init_wf_init_else IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    if 1 + 2 == 3 {
                    } else {
                        init t = 6;
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "the if-branch does not initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_match IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    match foo {
                        Foo::Bar(x) => {
                            init t = 6;
                        }
                        Foo::Qax(y) => {
                        }
                        Foo::Duck(z) => {
                            init t = 7;
                        }
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "all branches of a match-statement must initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_match2 IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    match foo {
                        Foo::Bar(x) => {
                        }
                        Foo::Qax(y) => {
                            init t = 6;
                        }
                        Foo::Duck(z) => {
                        }
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "all branches of a match-statement must initialize")
}

test_verify_one_file! {
    #[test] init_wf_update IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    init t = 6;
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'update' statement not allowed in initialization")
}

test_verify_one_file! {
    #[test] init_wf_update2 IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'update' statement not allowed in initialization")
}

test_verify_one_file! {
    #[test] init_wf_special IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            init!{
                init() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "use 'init' instead")
}

test_verify_one_file! {
    #[test] init_wf_special_with_binding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            init!{
                init() {
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "use 'init' instead")
}

test_verify_one_file! {
    #[test] init_wf_assert IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    assert(true);
                    init t = 6;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'assert' statement not allowed in initialization")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    update t = 6;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe_conditional IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    if true {
                        update t = 6;
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe_conditional2 IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    if true {
                    } else {
                        update t = 6;
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe_match IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    match foo {
                        Foo::Bar(x) => {
                            update t = 6;
                        }
                        Foo::Qax(y) => { }
                        Foo::Duck(z) => { }
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_init IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'init' statement not allowed")
}

test_verify_one_file! {
    #[test] normal_wf_update_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    guard t >= Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement only allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_update IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            readonly!{
                tr() {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_init IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            readonly!{
                tr() {
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed outside 'init' routine")
}

test_verify_one_file! {
    #[test] readonly_wf_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_remove_with_binding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_remove IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    remove t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_deposit IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    deposit t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_withdraw IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    withdraw t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] field_not_found IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update whats_this = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "field 'whats_this' not found")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_remove IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    remove t -= Some(5) by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_remove_with_binding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    remove t -= Some(let y) by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_remove IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    remove t -= [5 => 7] by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_remove IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    remove t -= { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += Some(5) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.is_None());
                assert(post.t.is_Some());
                assert(post.t.get_Some_0() == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_general_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += (Option::Some(5)) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.is_None());
                assert(post.t.is_Some());
                assert(post.t.get_Some_0() == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    add t += [5 => 7] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(!pre.t.dom().contains(5));
                assert(post.t.dom().contains(5));
                assert(post.t.index(5) == 7);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_general_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    add t += (Map::<int, int>::empty().insert(5, 7)) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(!pre.t.dom().contains(5));
                assert(post.t.dom().contains(5));
                assert(post.t.index(5) == 7);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    add t += { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_general_add IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    add t += ({ 5 }) by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_have IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    have t >= Some(5) by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_have IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    have t >= [5 => 7] by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_have IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    have t >= { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_withdraw IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    withdraw t -= Some(5) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.is_Some());
                assert(pre.t.get_Some_0() == 5);
                assert(post.t.is_None());
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_withdraw IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    withdraw t -= [5 => 7] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.dom().contains(5));
                assert(pre.t.index(5) == 7);
                assert(!post.t.dom().contains(5));
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_withdraw_with_binding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    withdraw t -= [5 => let z] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.dom().contains(5));
                assert(!post.t.dom().contains(5));
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_withdraw IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    withdraw t -= { 5 } by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.count(5) >= 1);
                assert(equal(post.t, pre.t.remove(5)));
            }
        }}
    // not supported right now:
    } => Err(e) => assert_error_msg(e, "storage_multiset strategy not implemented")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            readonly!{
                tr() {
                    guard t >= Some(5) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.is_Some() && t.get_Some_0() == 5);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
            }

            readonly!{
                tr() {
                    guard t >= [5 => 7] by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.dom().contains(5) && t.index(5) == 7);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_general_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            readonly!{
                tr() {
                    guard t >= (Option::Some(5)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.is_Some() && t.get_Some_0() == 5);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_general_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
            }

            readonly!{
                tr() {
                    guard t >= (Map::<int,int>::empty().insert(5, 7)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.dom().contains(5) && t.index(5) == 7);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            readonly!{
                tr() {
                    guard t >= { 5 } by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.count(5) >= 1);
                }
            }
        }}
    // not supported right now:
    } => Err(e) => assert_error_msg(e, "storage_multiset strategy not implemented")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_general_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            readonly!{
                tr() {
                    guard t >= (Multiset::singleton(5)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.count(5) >= 1);
                }
            }
        }}
    // not supported right now:
    } => Err(e) => assert_error_msg(e, "unrecognized sharding strategy: 'storage_multiset'")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_deposit IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    deposit t += Some(5) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.is_None());
                assert(post.t.is_Some());
                assert(post.t.get_Some_0() == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_deposit IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    deposit t += [5 => 7] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(!pre.t.dom().contains(5));
                assert(post.t.dom().contains(5));
                assert(post.t.index(5) == 7);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_deposit IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    deposit t += { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "storage_multiset strategy not implemented")
}

test_verify_one_file! {
    #[test] assert_safety_condition_fail IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    assert(pre.t == 0); // FAILS
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] assert_safety_condition_readonly_fail IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            readonly!{
                tr() {
                    assert(pre.t == 0); // FAILS
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] wrong_op_var_add_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "statement not allowed for field with sharding strategy")
}

test_verify_one_file! {
    #[test] wrong_op_multiset_add_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_one_file! {
    #[test] wrong_op_multiset_add_option_with_binding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>,
            }

            transition!{
                tr() {
                    add t += Some(let z);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_one_file! {
    #[test] wrong_op_map_add_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_one_file! {
    #[test] wrong_op_option_add_map IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += [5 => 5];
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'option'")
}

test_verify_one_file! {
    #[test] wrong_op_option_add_multiset IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += {5};
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'option'")
}

test_verify_one_file! {
    #[test] wrong_op_map_add_multiset IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    add t += {5};
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_one_file! {
    #[test] wrong_op_multiset_add_map IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>,
            }

            transition!{
                tr() {
                    add t += [5 => 5];
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_one_file! {
    #[test] wrong_op_map_guard_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            readonly!{
                tr() {
                    guard t >= Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_one_file! {
    #[test] wrong_op_option_deposit_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                   deposit t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'deposit' statement not allowed for field with sharding strategy 'option'")
}

test_verify_one_file! {
    #[test] wrong_op_storage_option_add_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                   add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'add' statement not allowed for field with sharding strategy 'storage_option'")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    if true {
                        let x = 5;
                    } else {
                        let x = 5;
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents2 IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    let x = 5;
                    let x = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents3 IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: Map<int, int>
            }

            transition!{
                tr(x: int) {
                    let x = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents4 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr(x: int) {
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

// TODO this current panics but should just be a normal error
/*
test_verify_one_file!{
    #[test] type_recursion_fail IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: X::Instance,
            }
        }}
    } => Err(e)
}
*/

test_verify_one_file! {
    #[test] type_recursion_fail_negative IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                // this should fail because Map has a maybe_negative first param

                #[sharding(variable)]
                pub t: Map<X::Instance, int>
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "non-positive polarity")
}

test_verify_one_file! {
    #[test] lemma_recursion_fail IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: int,
            }

            init!{
                initialize() {
                    init t = 1;
                }
            }

            readonly!{
                ro() {
                    assert(pre.t == 2);
                }
            }

            #[invariant]
            pub fn inv_2(self) -> bool {
                self.t == 2
            }

            #[inductive(initialize)]
            fn inductive_init(post: Self) {
                #[proof] let (inst, token) = X::Instance::initialize();
                inst.ro(&token);
                // this should derive a contradiction if not for the recursion checking
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "recursive function must call decreases")
}

test_verify_one_file! {
    #[test] lemma_recursion_assert_fail IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: int,
            }

            init!{
                initialize() {
                    init t = 1;
                }
            }

            readonly!{
                ro() {
                    assert(pre.t == 2) by {
                        foo_lemma();
                    };
                }
            }
        }}

        #[proof]
        fn foo_lemma() {
            #[proof] let (inst, token) = X::Instance::initialize();
            inst.ro(&token);
        }
    } => Err(e) => assert_vir_error_msg(e, "recursive function must call decreases")
}

test_verify_one_file! {
    #[test] relation_codegen IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub x: int,
                pub y: int,
                pub z: int,
            }

            init!{
                initialize(x: int, y: int, z: int) {
                    init x = x;
                    init y = y;
                    require(y <= z);
                    if x == y {
                        init z = z;
                    } else {
                        init z = z + 1;
                    }
                }
            }

            transition!{
                tr1(b: bool, c: bool) {
                    require(b);
                    assert(pre.y <= pre.z);
                    require(c);
                    update z = pre.z + 1;
                }
            }

            transition!{
                tr2(b: bool, c: bool) {
                    if b {
                        update z = pre.z + 1;
                    } else {
                        assert(pre.y <= pre.z);
                    }
                    require(c);
                }
            }

            transition!{
                tr3(b: bool, c: bool) {
                    if b {
                        assert(pre.y <= pre.z);
                    } else {
                        let j = pre.z + 1;
                        update z = j;
                    }
                    require(c);
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool { self.y <= self.z }

            #[inductive(initialize)]
            fn init_inductive(post: Self, x: int, y: int, z: int) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self, b: bool, c: bool) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self, b: bool, c: bool) { }

            #[inductive(tr3)]
            fn tr3_inductive(pre: Self, post: Self, b: bool, c: bool) { }

        }}

        #[spec]
        fn rel_init(post: X::State, x: int, y: int, z: int) -> bool {
            post.x == x && post.y == y && y <= z &&
            if x == y { post.z == z } else { post.z == z + 1 }
        }

        #[spec]
        fn rel_tr1(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            b && (pre.y <= pre.z >>= (
                c
                && post.z == pre.z + 1
                && post.x == pre.x
                && post.y == pre.y))
        }

        #[spec]
        fn rel_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            b && (pre.y <= pre.z && (
                c
                && post.z == pre.z + 1
                && post.x == pre.x
                && post.y == pre.y))
        }

        #[spec]
        fn rel_tr2(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            (if b { post.z == pre.z + 1 } else { pre.y <= pre.z >>= post.z == pre.z })
            && ((!b >>= pre.y <= pre.z) >>=
                c && pre.x == post.x && pre.y == post.y)
        }

        #[spec]
        fn rel_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            (if b { post.z == pre.z + 1 } else { post.z == pre.z })
            && ((!b >>= pre.y <= pre.z) &&
                c && pre.x == post.x && pre.y == post.y)
        }

        #[spec]
        fn rel_tr3(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            (if !b { post.z == pre.z + 1 } else { pre.y <= pre.z >>= post.z == pre.z })
            && ((b >>= pre.y <= pre.z) >>=
                c && pre.x == post.x && pre.y == post.y)
        }

        #[spec]
        fn rel_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            (if !b { post.z == pre.z + 1 } else { post.z == pre.z })
            && ((b >>= pre.y <= pre.z) &&
                c && pre.x == post.x && pre.y == post.y)
        }


        #[proof]
        fn correct_init(post: X::State, x: int, y: int, z: int) {
            requires(X::State::initialize(post, x, y, z));
            ensures(rel_init(post, x, y, z));
        }

        #[proof]
        fn rev_init(post: X::State, x: int, y: int, z: int) {
            requires(rel_init(post, x, y, z));
            ensures(X::State::initialize(post, x, y, z));
        }

        #[proof]
        fn correct_tr1(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr1(pre, post, b, c));
            ensures(rel_tr1(pre, post, b, c));
        }

        #[proof]
        fn rev_tr1(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr1(pre, post, b, c));
            ensures(X::State::tr1(pre, post, b, c));
        }

        #[proof]
        fn correct_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr1_strong(pre, post, b, c));
            ensures(rel_tr1_strong(pre, post, b, c));
        }

        #[proof]
        fn rev_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr1_strong(pre, post, b, c));
            ensures(X::State::tr1_strong(pre, post, b, c));
        }

        #[proof]
        fn correct_tr2(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr2(pre, post, b, c));
            ensures(rel_tr2(pre, post, b, c));
        }

        #[proof]
        fn rev_tr2(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr2(pre, post, b, c));
            ensures(X::State::tr2(pre, post, b, c));
        }

        #[proof]
        fn correct_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr2_strong(pre, post, b, c));
            ensures(rel_tr2_strong(pre, post, b, c));
        }

        #[proof]
        fn rev_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr2_strong(pre, post, b, c));
            ensures(X::State::tr2_strong(pre, post, b, c));
        }

        #[proof]
        fn correct_tr3(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr3(pre, post, b, c));
            ensures(rel_tr3(pre, post, b, c));
        }

        #[proof]
        fn rev_tr3(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr3(pre, post, b, c));
            ensures(X::State::tr3(pre, post, b, c));
        }

        #[proof]
        fn correct_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr3_strong(pre, post, b, c));
            ensures(rel_tr3_strong(pre, post, b, c));
        }

        #[proof]
        fn rev_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr3_strong(pre, post, b, c));
            ensures(X::State::tr3_strong(pre, post, b, c));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] relation_codegen_match IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub x: int,
                pub y: int,
                pub z: int,
            }

            init!{
                initialize(x: int, y: int, z: int, foo: Foo) {
                    init x = x;
                    init y = y;
                    require(y <= z);
                    match foo {
                        Foo::Bar(a) => { init z = z; }
                        Foo::Qax(b) => { init z = z + 1; }
                        Foo::Duck(d) => { init z = z + 2; }
                    }
                }
            }

            transition!{
                tr1(foo: Foo, c: bool) {
                    match foo {
                        Foo::Bar(a) => { update z = pre.z + 1; }
                        Foo::Qax(b) => { assert(pre.y <= pre.z); }
                        Foo::Duck(d) => { assert(foo.is_Duck()); }
                    }
                    require(c);
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool { self.y <= self.z }

            #[inductive(initialize)]
            fn init_inductive(post: Self, x: int, y: int, z: int, foo: Foo) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self, foo: Foo, c: bool) { }
        }}

        #[spec]
        fn rel_init(post: X::State, x: int, y: int, z: int, foo: Foo) -> bool {
            post.x == x && post.y == y && y <= z &&
            match foo {
                Foo::Bar(a) => { post.z == z }
                Foo::Qax(b) => { post.z == z + 1 }
                Foo::Duck(d) => { post.z == z + 2 }
            }
        }

        #[spec]
        fn rel_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) -> bool {
            (match foo {
                Foo::Bar(a) => { post.z == pre.z + 1 }
                Foo::Qax(b) => { pre.y <= pre.z >>= post.z == pre.z }
                Foo::Duck(d) => { post.z == pre.z }
            }) && ((match foo {
                Foo::Bar(a) => { true }
                Foo::Qax(b) => { pre.y <= pre.z }
                Foo::Duck(d) => { true }
            }) >>=
                c && pre.x == post.x && pre.y == post.y)
        }

        #[spec]
        fn rel_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) -> bool {
            (match foo {
                Foo::Bar(a) => { post.z == pre.z + 1 }
                Foo::Qax(b) => { post.z == pre.z && pre.y <= pre.z }
                Foo::Duck(d) => { post.z == pre.z }
            })
            && (c && pre.x == post.x && pre.y == post.y)
        }

        #[proof]
        fn correct_init(post: X::State, x: int, y: int, z: int, foo: Foo) {
            requires(X::State::initialize(post, x, y, z, foo));
            ensures(rel_init(post, x, y, z, foo));
        }

        #[proof]
        fn rev_init(post: X::State, x: int, y: int, z: int, foo: Foo) {
            requires(rel_init(post, x, y, z, foo));
            ensures(X::State::initialize(post, x, y, z, foo));
        }

        #[proof]
        fn correct_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(X::State::tr1(pre, post, foo, c));
            ensures(rel_tr1(pre, post, foo, c));
        }

        #[proof]
        fn rev_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(rel_tr1(pre, post, foo, c));
            ensures(X::State::tr1(pre, post, foo, c));
        }

        #[proof]
        fn correct_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(X::State::tr1_strong(pre, post, foo, c));
            ensures(rel_tr1_strong(pre, post, foo, c));
        }

        #[proof]
        fn rev_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(rel_tr1_strong(pre, post, foo, c));
            ensures(X::State::tr1_strong(pre, post, foo, c));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] relation_codegen_special IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(map)]
                pub map: Map<int, int>,

                #[sharding(multiset)]
                pub mset: Multiset<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,

                #[sharding(storage_map)]
                pub storage_map: Map<int, int>,
            }

            transition!{
                tr1() {
                    remove opt -= Some(5);
                    add opt += Some(8);

                    remove map -= [0 => 1];
                    have map >= [2 => 3];
                    add map += [4 => 5] by { assume(false); };

                    remove mset -= {10};
                    have mset >= {11};
                    add mset += {12};

                    withdraw storage_opt -= Some(13) by { assume(false); };
                    deposit storage_opt += Some(14);

                    withdraw storage_map -= [15 => 16] by { assume(false); };
                    deposit storage_map += [17 => 18] by { assume(false); };
                }
            }

            transition!{
                tr2() {
                    have opt >= Some(7);
                    add map += [4 => 5] by { assume(false); };
                }
            }

            transition!{
                tr3() {
                    remove opt -= Some(7);
                    withdraw storage_opt -= Some(12) by { assume(false); };
                }
            }

            transition!{
                tr4() {
                    add opt += Some(7) by { assume(false); };
                    deposit storage_opt += Some(12) by { assume(false); };
                }
            }
        }}


        #[spec]
        fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(5))
            && pre.map.contains_pair(0, 1)
            && pre.map.remove(0).contains_pair(2, 3)
            && (!pre.map.remove(0).dom().contains(4)
              >>=  pre.mset.count(10) >= 1
              && pre.mset.remove(10).count(11) >= 1
              && (equal(pre.storage_opt, Option::Some(13))
                >>= (pre.storage_map.contains_pair(15, 16)
                  >>= (!pre.storage_map.remove(15).dom().contains(17)
                    >>= equal(post.storage_map, pre.storage_map.remove(15).insert(17, 18))
                     && equal(post.opt, Option::Some(8))
                     && equal(post.map, pre.map.remove(0).insert(4, 5))
                     && equal(post.mset, pre.mset.remove(10).insert(12))
                     && equal(post.storage_opt, Option::Some(14))
                  ))))
        }

        #[spec]
        fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(5))
            && equal(post.opt, Option::Some(8))

            && pre.map.contains_pair(0, 1)
            && pre.map.remove(0).contains_pair(2, 3)
            && !pre.map.remove(0).dom().contains(4)
            && equal(post.map, pre.map.remove(0).insert(4, 5))

            && pre.mset.count(10) >= 1
            && pre.mset.remove(10).count(11) >= 1
            && equal(post.mset, pre.mset.remove(10).insert(12))

            && equal(pre.storage_opt, Option::Some(13))
            && equal(post.storage_opt, Option::Some(14))

            && pre.storage_map.contains_pair(15, 16)
            && !pre.storage_map.remove(15).dom().contains(17)
            && equal(post.storage_map, pre.storage_map.remove(15).insert(17, 18))
        }

        #[spec]
        fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && (!pre.map.dom().contains(4) >>=
                   equal(post.map, pre.map.insert(4, 5))
                && equal(post.opt, pre.opt)
                && equal(post.storage_opt, pre.storage_opt)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.mset, pre.mset)
            )
        }

        #[spec]
        fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && !pre.map.dom().contains(4)
            && equal(post.map, pre.map.insert(4, 5))
            && equal(post.opt, pre.opt)
            && equal(post.storage_opt, pre.storage_opt)
            && equal(post.storage_map, pre.storage_map)
            && equal(post.mset, pre.mset)
        }

        #[spec]
        fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && (equal(pre.storage_opt, Option::Some(12))
              >>= equal(post.storage_opt, Option::None)
                && equal(post.map, pre.map)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.mset, pre.mset)
                && equal(post.opt, Option::None)
            )
        }

        #[spec]
        fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && equal(post.opt, Option::None)
            && equal(pre.storage_opt, Option::Some(12))
            && equal(post.storage_opt, Option::None)
            && equal(post.map, pre.map)
            && equal(post.storage_map, pre.storage_map)
            && equal(post.mset, pre.mset)
        }

        #[spec]
        fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::None) >>= (
              (equal(pre.storage_opt, Option::None) >>= (
                equal(post.storage_opt, Option::Some(12))
                && equal(post.map, pre.map)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.mset, pre.mset)
                && equal(post.opt, Option::Some(7))
              ))
            )
        }

        #[spec]
        fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::None)
            && equal(post.opt, Option::Some(7))
            && equal(pre.storage_opt, Option::None)
            && equal(post.storage_opt, Option::Some(12))
            && equal(post.map, pre.map)
            && equal(post.storage_map, pre.storage_map)
            && equal(post.mset, pre.mset)
        }

        #[proof]
        fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        #[proof]
        fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        #[proof]
        fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        #[proof]
        fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        #[proof]
        fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        #[proof]
        fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        #[proof]
        fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        #[proof]
        fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        #[proof]
        fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        #[proof]
        fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        #[proof]
        fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        #[proof]
        fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }

        #[proof]
        fn correct_tr4(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4(pre, post));
            ensures(rel_tr4(pre, post));
        }

        #[proof]
        fn rev_tr4(pre: Y::State, post: Y::State) {
            requires(rel_tr4(pre, post));
            ensures(Y::State::tr4(pre, post));
        }

        #[proof]
        fn correct_tr4_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4_strong(pre, post));
            ensures(rel_tr4_strong(pre, post));
        }

        #[proof]
        fn rev_tr4_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr4_strong(pre, post));
            ensures(Y::State::tr4_strong(pre, post));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] relation_codegen_special_general IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(map)]
                pub map: Map<int, int>,

                #[sharding(multiset)]
                pub mset: Multiset<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,

                #[sharding(storage_map)]
                pub storage_map: Map<int, int>,
            }

            transition!{
                tr1() {
                    remove opt -= ( Option::Some(5) );
                    add opt += ( Option::Some(8) );

                    remove map -= ( Map::<int, int>::empty().insert(0, 1) );
                    have map >= ( Map::<int, int>::empty().insert(2, 3) );
                    add map += ( Map::<int, int>::empty().insert(4, 5) ) by { assume(false); };

                    remove mset -= ( Multiset::<int>::singleton(10) );
                    have mset >= ( Multiset::<int>::singleton(11) );
                    add mset += ( Multiset::<int>::singleton(12) );

                    withdraw storage_opt -= ( Option::Some(13) ) by { assume(false); };
                    deposit storage_opt += ( Option::Some(14) );

                    withdraw storage_map -= ( Map::<int, int>::empty().insert(15, 16) ) by { assume(false); };
                    deposit storage_map += ( Map::<int, int>::empty().insert(17, 18) ) by { assume(false); };
                }
            }

            transition!{
                tr2() {
                    have opt >= (Option::Some(7));
                    add map += (Map::<int, int>::empty().insert(4, 5)) by { assume(false); };
                }
            }

            transition!{
                tr3() {
                    remove opt -= (Option::Some(7));
                    withdraw storage_opt -= (Option::Some(12)) by { assume(false); };
                }
            }

            transition!{
                tr4() {
                    add opt += (Option::Some(7)) by { assume(false); };
                    deposit storage_opt += (Option::Some(12)) by { assume(false); };
                }
            }
        }}

        #[spec]
        fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(5))

            && map![0 => 1].le(pre.map)
            && map![2 => 3].le(pre.map.remove_keys(map![0 => 1].dom()))
            && (pre.map.remove_keys(map![0 => 1].dom()).dom().disjoint(map![4 => 5].dom()) >>=

            Multiset::singleton(10).le(pre.mset)
            && Multiset::singleton(11).le(pre.mset.sub(Multiset::singleton(10)))

            && (equal(pre.storage_opt, Option::Some(13)) >>=

            (map![15 => 16].le(pre.storage_map) >>=
            (pre.storage_map.remove_keys(map![15 => 16].dom()).dom().disjoint(map![17 => 18].dom()) >>=
            equal(post.opt, Option::Some(8))
            && equal(post.map, pre.map.remove_keys(map![0 => 1].dom()).union_prefer_right(map![4 => 5]))
            && equal(post.mset,
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12)))
            && equal(post.storage_opt, Option::Some(14))
            && equal(post.storage_map,
                pre.storage_map.remove_keys(map![15 => 16].dom()).union_prefer_right(map![17 => 18]))
            ))))
        }

        #[spec]
        fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(5))
            && equal(post.opt, Option::Some(8))

            && map![0 => 1].le(pre.map)
            && map![2 => 3].le(pre.map.remove_keys(map![0 => 1].dom()))
            && pre.map.remove_keys(map![0 => 1].dom()).dom().disjoint(map![4 => 5].dom())
            && equal(post.map, pre.map.remove_keys(map![0 => 1].dom()).union_prefer_right(map![4 => 5]))

            && Multiset::singleton(10).le(pre.mset)
            && Multiset::singleton(11).le(pre.mset.sub(Multiset::singleton(10)))
            && equal(post.mset,
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12)))

            && equal(pre.storage_opt, Option::Some(13))
            && equal(post.storage_opt, Option::Some(14))

            && map![15 => 16].le(pre.storage_map)
            && pre.storage_map.remove_keys(map![15 => 16].dom()).dom().disjoint(map![17 => 18].dom())
            && equal(post.storage_map,
                pre.storage_map.remove_keys(map![15 => 16].dom()).union_prefer_right(map![17 => 18]))
        }

        #[spec]
        fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && (!pre.map.dom().contains(4) >>=
                   equal(post.map, pre.map.union_prefer_right(map![4 => 5]))
                && equal(post.opt, pre.opt)
                && equal(post.storage_opt, pre.storage_opt)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.mset, pre.mset)
            )
        }

        #[spec]
        fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && !pre.map.dom().contains(4)
            && equal(post.map, pre.map.union_prefer_right(map![4 => 5]))
            && equal(post.opt, pre.opt)
            && equal(post.storage_opt, pre.storage_opt)
            && equal(post.storage_map, pre.storage_map)
            && equal(post.mset, pre.mset)
        }

        #[spec]
        fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && (equal(pre.storage_opt, Option::Some(12))
              >>= equal(post.storage_opt, Option::None)
                && equal(post.map, pre.map)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.mset, pre.mset)
                && equal(post.opt, Option::None)
            )
        }

        #[spec]
        fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(7))
            && equal(post.opt, Option::None)
            && equal(pre.storage_opt, Option::Some(12))
            && equal(post.storage_opt, Option::None)
            && equal(post.map, pre.map)
            && equal(post.storage_map, pre.storage_map)
            && equal(post.mset, pre.mset)
        }

        #[spec]
        fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::None) >>= (
              (equal(pre.storage_opt, Option::None) >>= (
                equal(post.storage_opt, Option::Some(12))
                && equal(post.map, pre.map)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.mset, pre.mset)
                && equal(post.opt, Option::Some(7))
              ))
            )
        }

        #[spec]
        fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::None)
            && equal(post.opt, Option::Some(7))
            && equal(pre.storage_opt, Option::None)
            && equal(post.storage_opt, Option::Some(12))
            && equal(post.map, pre.map)
            && equal(post.storage_map, pre.storage_map)
            && equal(post.mset, pre.mset)
        }

        #[proof]
        fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        #[proof]
        fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        #[proof]
        fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        #[proof]
        fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        #[proof]
        fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        #[proof]
        fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        #[proof]
        fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        #[proof]
        fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        #[proof]
        fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        #[proof]
        fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        #[proof]
        fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        #[proof]
        fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }

        #[proof]
        fn correct_tr4(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4(pre, post));
            ensures(rel_tr4(pre, post));
        }

        #[proof]
        fn rev_tr4(pre: Y::State, post: Y::State) {
            requires(rel_tr4(pre, post));
            ensures(Y::State::tr4(pre, post));
        }

        #[proof]
        fn correct_tr4_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4_strong(pre, post));
            ensures(rel_tr4_strong(pre, post));
        }

        #[proof]
        fn rev_tr4_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr4_strong(pre, post));
            ensures(Y::State::tr4_strong(pre, post));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] relation_codegen_opt_general IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,
            }

            readonly!{
                ro() {
                    guard storage_opt >= (Option::<int>::None);
                }
            }

            transition!{
                tr1() {
                    have opt >= (Option::<int>::None);
                }
            }

            transition!{
                tr2() {
                    add opt += (Option::<int>::None);
                    deposit storage_opt += (Option::<int>::None);
                }
            }

            transition!{
                tr3() {
                    remove opt -= (Option::<int>::None);
                    withdraw storage_opt -= (Option::<int>::None);
                }
            }
        }}

        #[spec]
        fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        #[spec]
        fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        #[spec]
        fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        #[spec]
        fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        #[spec]
        fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        #[spec]
        fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        #[proof]
        fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        #[proof]
        fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        #[proof]
        fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        #[proof]
        fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        #[proof]
        fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        #[proof]
        fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        #[proof]
        fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        #[proof]
        fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        #[proof]
        fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        #[proof]
        fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        #[proof]
        fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        #[proof]
        fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nondet_tokenizing IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Z {
            fields {
                #[sharding(variable)]
                pub v1: int,

                #[sharding(variable)]
                pub v2: int,

                #[sharding(not_tokenized)]
                pub nt: int,

                #[sharding(constant)]
                pub c: int,
            }

            init!{
                initialize() {
                    init v1 = 0;
                    init v2 = 1;
                    init nt = 2;
                    init c = 3;
                }
            }

            transition!{
                tr1() {
                    update nt = pre.nt + 1; // this is ok because the exchange fn ignores this line
                    update v1 = pre.v1 + 2;
                }
            }

            transition!{
                tr2() {
                    // v1 should be passed in as tokens, v2 read nondeterministically
                    birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
                    update v1 = x;
                }
            }

            transition!{
                tr3() {
                    // v1, v2 both passed in as tokens
                    birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
                    update v1 = x + 4 * pre.v2;
                }
            }
        }}

        #[proof]
        fn go() {
            #[proof] let (instance, mut v1, v2) = Z::Instance::initialize();
            assert(equal(v1.instance, instance));
            assert(equal(v2.instance, instance));
            assert(equal(v1.value, 0));
            assert(equal(v2.value, 1));
            assert(equal(instance.c(), 3));

            #[proof] instance.tr1(&mut v1);
            assert(equal(v1.instance, instance));
            assert(equal(v1.value, 2));

            #[spec] let old_v1_value = v1.value;
            #[proof] let (birds_eye_v2, birds_eye_nt) = instance.tr2(&mut v1);
            assert(equal(v1.instance, instance));
            assert(equal(v1.value,
                birds_eye_nt.value() + instance.c() + old_v1_value - birds_eye_v2.value()));

            #[spec] let old_v1_value = v1.value;
            #[proof] let birds_eye_nt = instance.tr3(&mut v1, &v2);
            assert(equal(v1.instance, instance));
            assert(equal(v1.value, birds_eye_nt.value() + instance.c() + old_v1_value + 3 * v2.value));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pre_in_init IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    update t = pre.t;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "no previous state to refer to")
}

test_verify_one_file! {
    #[test] self_in_transition IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = self.t;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "`self` is meaningless")
}

test_verify_one_file! {
    #[test] post_in_transition IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = post.t;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot refer directly to `post`")
}

test_verify_one_file! {
    #[test] test_let_pattern IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields { #[sharding(variable)] pub t: (int, int) }

            init!{
                initialize() {
                    init t = (2, 2);
                }
            }

            transition!{
                tr() {
                    let (a, b) = pre.t;
                    update t = (a + 1, b + 1);
                }
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                self.t.0 == self.t.1
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr)]
            fn tr_inductive(pre: Self, post: Self) { }
        }}
    } => Ok(())
}

test_verify_one_file! {
    #[test] super_error IMPORTS.to_string() + code_str! {
        struct Bar { }

        state_machine!{ X {
            fields { pub t: int }

            transition!{
                // this is disallowed because the macro would try to copy the path into
                // an inner module
                tr(foo: super::Bar) {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "`super::` path not allowed here")
}

test_verify_one_file! {
    #[test] if_let_fail IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    if let x = 5 {
                        assert(x == 5);
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "do not support if-let conditionals")
}

test_verify_one_file! {
    #[test] if_let_fail_with_else IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    if let x = 5 {
                        assert(x == 5);
                    } else {
                        assert(true);
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "do not support if-let conditionals")
}

test_verify_one_file! {
    #[test] if_let_fail_with_chain IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            readonly!{
                tr() {
                    if true && let x = 5 {
                        assert(x == 5);
                    } else {
                        assert(true);
                    }
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "do not support if-let conditionals")
}

test_verify_one_file! {
    #[test] use_self_type IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(variable)]
                pub x: int,

                #[sharding(variable)]
                pub recursing: Option<Box<Self>>,
            }

            init!{
                ini(t: Self) {
                    let r: Self = t;
                    init x = r.x;
                    init recursing = t.recursing;
                }
            }

            #[spec] #[verifier(publish)]
            pub fn add1(x: int) -> int {
                x + 1
            }

            transition!{
                tr(a: int) {
                    update x = Self::add1(a);
                }
            }

            transition!{
                tr2(y: Option<Box<Self>>) {
                    let t: Option<Box<Self>> = y;
                    update recursing = t;
                }
            }

            transition!{
                tr3() {
                    update recursing = Option::<Box<Self>>::None;
                }
            }

        }}

        pub fn foo() {
            #[proof] let (inst, mut x_tok, mut r_tok) = Y::Instance::ini(
                Y::State { x: 5, recursing: Option::None }
            );
            inst.tr(19, &mut x_tok);
            assert(x_tok.value == 20);

            inst.tr2(Option::<Box<Y::State>>::None, &mut r_tok);
            assert(equal(Option::<Box<Y::State>>::None, r_tok.value));

            inst.tr3(&mut r_tok);
            assert(equal(Option::<Box<Y::State>>::None, r_tok.value));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] bind_codegen IMPORTS.to_string() + code_str! {

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(map)]
                pub map: Map<int, u64>,

                #[sharding(storage_map)]
                pub storage_map: Map<int, u64>,
            }

            init!{
                initialize() {
                    init opt = Option::Some(2);
                    init map = Map::<int,u64>::empty().insert(1, 5);
                    init storage_map = Map::<int,u64>::empty().insert(1, 6);
                }
            }

            #[invariant]
            pub fn maps_eq(&self) -> bool {
                equal(self.map.dom(), self.storage_map.dom())
            }

            #[invariant]
            pub fn maps_6(&self) -> bool {
                forall(|k| self.storage_map.dom().contains(k) >>=
                    self.storage_map.index(k) == 6)
            }

            transition!{
                tr1() {
                    remove opt -= Some(let x);
                    require(x == 2);
                }
            }

            transition!{
                tr2(key: int) {
                    remove map -= [key => let x];
                    require(x == 5);

                    withdraw storage_map -= [key => let y];
                    assert(y == 6);
                }
            }

            readonly!{
                tr3(key: int) {
                    have map >= [key => let x];
                    require(x == 5);

                    guard storage_map >= [key => 6];
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self, key: int) { }
        }}

        #[spec]
        fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(2))
            && equal(post.opt, Option::None)
            && equal(post.map, pre.map)
            && equal(post.storage_map, pre.storage_map)
        }

        #[spec]
        fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, Option::Some(2))
            && equal(post.opt, Option::None)
            && equal(post.map, pre.map)
            && equal(post.storage_map, pre.storage_map)
        }

        #[spec]
        fn rel_tr2(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.map.dom().contains(key)
            && pre.map.index(key) == 5

            && (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              >>= (
                   equal(post.map, pre.map.remove(key))
                && equal(post.storage_map, pre.storage_map.remove(key))
                && equal(post.opt, pre.opt)
              )
           )
        }

        #[spec]
        fn rel_tr2_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.map.dom().contains(key)
            && pre.map.index(key) == 5

            && (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && (
                   equal(post.map, pre.map.remove(key))
                && equal(post.storage_map, pre.storage_map.remove(key))
                && equal(post.opt, pre.opt)
              )
           )
        }

        #[spec]
        fn rel_tr3(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.map.dom().contains(key)
            && pre.map.index(key) == 5

            && (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              >>= (
                   equal(post.map, pre.map)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.opt, pre.opt)
              )
           )
        }

        #[spec]
        fn rel_tr3_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.map.dom().contains(key)
            && pre.map.index(key) == 5

            && (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && (
                   equal(post.map, pre.map)
                && equal(post.storage_map, pre.storage_map)
                && equal(post.opt, pre.opt)
              )
           )
        }

        #[proof]
        fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        #[proof]
        fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        #[proof]
        fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        #[proof]
        fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        #[proof]
        fn correct_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2(pre, post, key));
            ensures(rel_tr2(pre, post, key));
        }

        #[proof]
        fn rev_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2(pre, post, key));
            ensures(Y::State::tr2(pre, post, key));
        }

        #[proof]
        fn correct_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2_strong(pre, post, key));
            ensures(rel_tr2_strong(pre, post, key));
        }

        #[proof]
        fn rev_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2_strong(pre, post, key));
            ensures(Y::State::tr2_strong(pre, post, key));
        }

        #[proof]
        fn correct_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3(pre, post, key));
            ensures(rel_tr3(pre, post, key));
        }

        #[proof]
        fn rev_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3(pre, post, key));
            ensures(Y::State::tr3(pre, post, key));
        }

        #[proof]
        fn correct_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3_strong(pre, post, key));
            ensures(rel_tr3_strong(pre, post, key));
        }

        #[proof]
        fn rev_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3_strong(pre, post, key));
            ensures(Y::State::tr3_strong(pre, post, key));
        }

        fn do_tokens() {
            #[proof] let mut m: Map<int, u64> = Map::proof_empty();
            m.proof_insert(1, 6);
            #[proof] let (inst, opt_token, mut map_tokens) = Y::Instance::initialize(m);

            match opt_token {
                Option::None => { assert(false); }
                Option::Some(opt_token) => {
                    inst.tr1(opt_token);

                    #[proof] let map_token = map_tokens.proof_remove(1);

                    #[proof] let the_guard = inst.tr3(1, &map_token);
                    assert(*the_guard == 6);

                    #[proof] let t = inst.tr2(1, map_token);
                    assert(t == 6);
                }
            };
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] bind_fail_add IMPORTS.to_string() + code_str! {

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    add opt += Some(let x);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "pattern-binding cannot be used in an 'add' statement")
}

test_verify_one_file! {
    #[test] bind_fail_deposit IMPORTS.to_string() + code_str! {

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(storage_option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    deposit opt += Some(let x);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "pattern-binding cannot be used in a 'deposit' statement")
}

test_verify_one_file! {
    #[test] bind_fail_guard IMPORTS.to_string() + code_str! {

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(storage_option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    guard opt >= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "pattern-binding cannot be used in a 'guard' statement")
}
