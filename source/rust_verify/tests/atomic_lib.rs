#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_atomic_u64 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicU64::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0xffff_ffff_ffff_ffff);
            assert(l == 9);
            assert(perm.value == 8);

            let l = at.fetch_sub_wrapping(&mut perm, 0xffff_ffff_ffff_ffff);
            assert(l == 8);
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_u32 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicU32::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0xffff_ffff);
            assert(l == 9);
            assert(perm.value == 8);

            let l = at.fetch_sub_wrapping(&mut perm, 0xffff_ffff);
            assert(l == 8);
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_u16 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicU16::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0xffff);
            assert(l == 9);
            assert(perm.value == 8);

            let l = at.fetch_sub_wrapping(&mut perm, 0xffff);
            assert(l == 8);
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_u8 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicU8::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0xff);
            assert(l == 9);
            assert(perm.value == 8);

            let l = at.fetch_sub_wrapping(&mut perm, 0xff);
            assert(l == 8);
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_i64 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicI64::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0x7fff_ffff_ffff_ffff);
            assert(l == 9);
            assert(perm.value == -(9223372036854775800 as i64));

            let l = at.fetch_sub_wrapping(&mut perm, 0x7fff_ffff_ffff_ffff);
            assert(l == -(9223372036854775800 as i64));
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_i32 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicI32::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0x7fff_ffff);
            assert(l == 9);
            assert(perm.value == -2147483640);

            let l = at.fetch_sub_wrapping(&mut perm, 0x7fff_ffff);
            assert(l == -2147483640);
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_i16 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicI16::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0x7fff);
            assert(l == 9);
            assert(perm.value == -32760);

            let l = at.fetch_sub_wrapping(&mut perm, 0x7fff);
            assert(l == -32760);
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_i8 code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicI8::new(5);

            assert(perm.value == 5);

            let l = at.load(&perm);
            assert(l == 5);

            at.store(&mut perm, 6);
            assert(perm.value == 6);

            let l = at.swap(&mut perm, 9);
            assert(l == 6);
            assert(perm.value == 9);

            let l = at.fetch_add_wrapping(&mut perm, 0x7f);
            assert(l == 9);
            assert(perm.value == -120);

            let l = at.fetch_sub_wrapping(&mut perm, 0x7f);
            assert(l == -120);
            assert(perm.value == 9);

            let l = at.fetch_or(&mut perm, 2);
            assert(l == 9);
            assert_bit_vector((9 as u64 | 2 as u64) == 11 as u64);
            assert(perm.value == 11);

            let l = at.fetch_and(&mut perm, 6);
            assert(l == 11);
            assert_bit_vector((11 as u64 & 6 as u64) == 2 as u64);
            assert(perm.value == 2);

            let l = at.fetch_xor(&mut perm, 3);
            assert(l == 2);
            assert_bit_vector((2 as u64 ^ 3 as u64) == 1 as u64);
            assert(perm.value == 1);

            let l = at.fetch_max(&mut perm, 5);
            assert(l == 1);
            assert(perm.value == 5);

            let l = at.fetch_max(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 5);

            let l = at.fetch_min(&mut perm, 4);
            assert(l == 5);
            assert(perm.value == 4);

            let l = at.fetch_min(&mut perm, 7);
            assert(l == 4);
            assert(perm.value == 4);

            let l = at.into_inner(perm);
            assert(l == 4);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_atomic_bool code! {
        use crate::pervasive::{atomics::*};
        use crate::pervasive::{modes::*};

        pub fn foo() {
            let (at, proof(mut perm)) = PAtomicBool::new(false);

            assert(perm.value == false);

            let l = at.load(&perm);
            assert(l == false);

            at.store(&mut perm, true);
            assert(perm.value == true);

            let l = at.swap(&mut perm, false);
            assert(l == true);
            assert(perm.value == false);

            // fetch_or

            let l = at.fetch_or(&mut perm, false);
            assert(l == false);
            assert(perm.value == false);

            let l = at.fetch_or(&mut perm, true);
            assert(l == false);
            assert(perm.value == true);

            let l = at.fetch_or(&mut perm, false);
            assert(l == true);
            assert(perm.value == true);

            let l = at.fetch_or(&mut perm, true);
            assert(l == true);
            assert(perm.value == true);

            // fetch_and

            let l = at.fetch_and(&mut perm, true);
            assert(l == true);
            assert(perm.value == true);

            let l = at.fetch_and(&mut perm, false);
            assert(l == true);
            assert(perm.value == false);

            let l = at.fetch_and(&mut perm, false);
            assert(l == false);
            assert(perm.value == false);

            let l = at.fetch_and(&mut perm, true);
            assert(l == false);
            assert(perm.value == false);

            // fetch_xor

            let l = at.fetch_xor(&mut perm, false);
            assert(l == false);
            assert(perm.value == false);

            let l = at.fetch_xor(&mut perm, true);
            assert(l == false);
            assert(perm.value == true);

            let l = at.fetch_xor(&mut perm, false);
            assert(l == true);
            assert(perm.value == true);

            let l = at.fetch_xor(&mut perm, true);
            assert(l == true);
            assert(perm.value == false);

            // fetch_nand

            let l = at.fetch_nand(&mut perm, false);
            assert(l == false);
            assert(perm.value == true);

            let l = at.fetch_nand(&mut perm, false);
            assert(l == true);
            assert(perm.value == true);

            let l = at.fetch_nand(&mut perm, true);
            assert(l == true);
            assert(perm.value == false);

            let l = at.fetch_nand(&mut perm, true);
            assert(l == false);
            assert(perm.value == true);

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}