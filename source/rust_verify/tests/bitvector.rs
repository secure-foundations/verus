#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[proof]
        fn test1(b: u32) {
            assert_bit_vector(b & 7 == b % 8);
            assert(b & 7 == b % 8);

            assert_bit_vector(b ^ b == 0);
            assert(b ^ b == 0);

            assert_bit_vector(b & b == b);
            assert(b & b == b);

            assert_bit_vector(b & 0 == 0);
            assert(b & 0 == 0);

            assert_bit_vector(b | b == b);
            assert(b | b == b);

            assert_bit_vector(b & 0xff < 0x100);
            assert(b & 0xff < 0x100);
            //assert(0xff & b < 0x100);  // fails without communtativity

            assert_bit_vector(b<<2 == b*4);
            assert(b<<2 == b*4);

            assert_bit_vector(b>>1 == b/2);
            assert(b>>1 == b/2);

            assert_bit_vector(2*b - b == b);
            assert(2*b - b == b);

            assert_bit_vector(b <= b);
            assert_bit_vector(b >= b);

            assert_bit_vector(b & b & b == b | b | (b ^ b));
            assert(b & b & b == b | b | (b ^ b));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails code! {
        #[proof]
        fn test1(b: u32) {
            assert_bit_vector(b | b > b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2_fails code! {
        #[proof]
        fn test2(b: u32) {
            assert_bit_vector(b + 1 == b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3_fails code! {
        #[proof]
        fn test3(b: u32) {
            assert_bit_vector(b & 0 > 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test4_fails code! {
        #[proof]
        fn test4(b: u32) {
            assert_bit_vector( (b << 2) >> 2 == b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
