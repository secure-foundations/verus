#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_with_bitvec_nlarith code! {
        #[proof]
        #[verifier(spinoff_z3)]
        fn test6(x: u32, y: u32, z:u32) {
            requires(x < 0xfff);

            assert_nonlinear_by({
                requires(x < 0xfff);
                ensures(x*x + x == x * (x + 1));
            });
            assert(x*x + x == x * (x + 1));

            assert_bit_vector((x < 0xfff) >>= (x&y < 0xfff));
            assert(x&y < 0xfff);

            assert_nonlinear_by({
                ensures(x*y*z == y*x*z);
            });
        }
    } => Ok(())
}

// From https://github.com/secure-foundations/verus/blob/ad92b2a8908a219ec84c277d2bb701934e9a8d9c/source/rust_verify/tests/adts_generics.rs#L1
test_verify_one_file! {
    #[test] test_box_unbox_struct code! {
        #[derive(Eq, PartialEq)]
        struct Thing<A> {
            a: A,
        }

        #[proof]
        #[verifier(spinoff_z3)]
        fn one(v: int) {
            let t1 = Thing { a: v };
            let t2 = Thing { a: v };
            let a: int = t2.a;
        }

        fn two(v: Thing<u8>) {
            assert(v.a >= 0);
        }
    } => Ok(())
}

// From https://github.com/secure-foundations/verus/blob/826e59f3774927f1cc61dd87e39e015b1ec51abf/source/rust_verify/tests/nonlinear.rs#L46
test_verify_one_file! {
    #[test] test_with_nlarith code! {
        #[verifier(nonlinear)]
        #[verifier(spinoff_z3)]
        #[proof]
        fn lemma_div_pos_is_pos(x: int, d: int) {
            requires([
                0 <= x,
                0 < d,
            ]);
            ensures(0 <= x / d);
        }
    } => Ok(())
}

// From https://github.com/secure-foundations/verus/blob/main/source/rust_verify/example/bitvector_basic.rs
test_verify_one_file! {
    #[test] test_with_bv code! {
        #[verifier(bit_vector)]
        #[verifier(spinoff_z3)]
        #[proof]
        fn bit_or32_auto(){
            ensures([
                forall(|a: u32, b: u32| #[trigger] (a|b) == b|a),
                forall(|a: u32, b: u32, c:u32| #[trigger] ((a|b)|c) == a|(b|c)),
                forall(|a: u32| #[trigger] (a|a) == a),
                forall(|a: u32| #[trigger] (a|0) == a),
                forall(|a: u32| #[trigger] (a| 0xffff_ffffu32) == 0xffff_ffffu32),
            ]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails code! {
        #[proof]
        #[verifier(spinoff_z3)]
        fn test6(b: u32, b2: u32) {
            assert_nonlinear_by({
                ensures(b*b2 == b2*b);
            });

            assert_bit_vector(b<<2 == b*4);
            assert(((b<<2) as int) == (b as int) *4);  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// From https://github.com/secure-foundations/verus/blob/826e59f3774927f1cc61dd87e39e015b1ec51abf/source/rust_verify/tests/nonlinear.rs#L46
test_verify_one_file! {
    #[test] test2_fails code! {
        #[verifier(nonlinear)]
        #[verifier(spinoff_z3)]
        #[proof]
        fn wrong_lemma_2(x: int, y: int, z: int) {
            requires([
                x > y,
                3 <= z,
            ]);
            ensures (y*z > x); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

// From https://github.com/secure-foundations/verus/blob/21a4774a6fb18295fe5bbcd6abb3e19c6df1e851/source/rust_verify/tests/multiset.rs#L63
test_verify_one_file! {
    #[test] multiset_basics code! {
        use crate::pervasive::multiset::*;

        #[proof] #[verifier(spinoff_z3)]
        pub fn commutative<V>(a: Multiset<V>, b: Multiset<V>) {
            ensures(equal(a.add(b), b.add(a)));

            assert(a.add(b).ext_equal(b.add(a)));
        }

        #[proof] #[verifier(spinoff_z3)]
        pub fn associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>) {
            ensures(equal(
                a.add(b.add(c)),
                a.add(b).add(c)));

            assert(a.add(b.add(c)).ext_equal(
                a.add(b).add(c)));
        }

        #[proof] #[verifier(spinoff_z3)]
        pub fn insert2<V>(a: V, b: V) {
            ensures(equal(
                Multiset::empty().insert(a).insert(b),
                Multiset::empty().insert(b).insert(a)));

            assert(
                Multiset::empty().insert(a).insert(b).ext_equal(
                Multiset::empty().insert(b).insert(a)));
        }

        #[proof] #[verifier(spinoff_z3)]
        pub fn insert2_count<V>(a: V, b: V, c: V) {
            requires(!equal(a, b) && !equal(b, c) && !equal(c, a));

            assert(Multiset::empty().insert(a).insert(b).count(a) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(b) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(c) == 0);
        }

        #[proof] #[verifier(spinoff_z3)]
        pub fn add_sub_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
            ensures(equal(a.add(b).sub(b), a));

            assert(a.add(b).sub(b).ext_equal(a));
        }

        #[proof] #[verifier(spinoff_z3)]
        pub fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
            requires(b.le(a));
            ensures(equal(a.sub(b).add(b), a));

            assert(a.sub(b).add(b).ext_equal(a));
            assert(false) // FAILS
        }

    } => Err(err) => assert_one_fails(err)
}
