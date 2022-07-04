use builtin::*;
use builtin_macros::*;

mod pervasive;
use crate::pervasive::modes::*;
use crate::pervasive::*;

#[verifier(external)]
fn main() {}

verus! {

// proof fn error() {
//     let a: u64 = 0xffff_ffff_ffff_ffff;
//     let b = a as i64;
// 
//     assert(a as int == b as int);
// }

spec fn double_fits_u64(n: int) -> bool {
    double(n) <= 0x7fff_ffff_ffff_ffff
}

spec fn double(n: int) -> int {
    n + n
}

fn double_impl(n: i64) -> (result: i64)
    requires
        double_fits_u64(n),
        n >= 0,
    ensures
        result == double(n),
{
    n + n
}


spec fn triple(n: int) -> int {
    if n >= 0 {
        n + double(n)
    } else {
        n + double(n*-1)
    }
}

proof fn triple_check(n: int) {
    if n < 0 {
        assert(triple(n) == (-n));
    }
}

spec fn triple_fits_i64(n: int) -> bool {
    triple(n) <= 0x7fff_ffff_ffff_ffff
}

fn triple_impl(n: i64) -> (result: i64)
    requires
        triple_fits_i64(n),
    ensures
        result >= triple(n),
{
    if n >= 0 {
        n + double_impl(n) 
    } else {
        // proof {
        //     let a = n as int * -1;
        //     assert(a >= 0);
        //     assert(n + a + a == triple(n));
        //     assert(triple(n) <= 0x7fff_ffff_ffff_ffff);
        //     assert(n + a + a <= 0x7fff_ffff_ffff_ffff);
        //     assert(triple(n) == (-n));
        //     assert((-a) + a + a <= 0x7fff_ffff_ffff_ffff);
        //     assert(a + a <= 0x7fff_ffff_ffff_ffff);
        //     assert(double_fits_u64(n as int * -1));
        // }
        -n
    }
}


fn sum_max(x: i64, y: i64) -> (res: (i64,i64))
    requires
        // TODO(chris) undecipherable parsing error
        // -0x7fff_ffff_ffff_ffff < x as int + y as int,
        // x as int + y as int < 0x7fff_ffff_ffff_ffff,
        (-0x7fff_ffff_ffff_ffff) < (x as int + y as int),
        (x as int + y as int) < 0x7fff_ffff_ffff_ffff,
    ensures
        res.0 == x + y,
        x <= res.1 && y <= res.1,
        res.1 == x || res.1 == y
{
    let s = x + y; 
    if x < y {
        let m = y;
        return (s,m);
    } else {
        let m = x;
        return (s,m);
    }
}


}
