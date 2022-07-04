use builtin::*;
use builtin_macros::*;

mod pervasive;
use crate::pervasive::modes::*;
use crate::pervasive::*;

#[verifier(external)]
fn main() {}

verus! {

spec fn double_fits_u64(n: int) -> bool {
    double(n) <= 0x7fff_ffff_ffff_ffff
}

spec fn double(n: int) -> int {
    n + n
}

fn double_impl(n: i64) -> i64 {
    requires(double_fits_u64(n) && n >= 0);
    ensures(|result: i64| result == double(n));
    n + n
}


spec fn triple(n: int) -> int {
    let r = match n >= 0 {
        True => n + double(n),
        False => n + double(n*-1)
    };
    r
}

spec fn triple_fits_i64(n: int) -> bool {
    triple(n) <= 0x7fff_ffff_ffff_ffff
}

fn triple_impl(n: i64) -> i64 {
    requires(triple_fits_i64(n));
    ensures(|result: i64| result >= triple(n));
    assert(double_fits_u64(n as int));
    let r = match n >= 0 {
        True => n + double_impl(n), 
        False => n + double_impl(n*-1)
    };
    r
}


/* fn sum_max(x: i64, y: i64) -> ((s,m):(i64,i64))
    ensures 
        s == x + y,
        x <= m && y <= m,
        m == x || m == y
{
    let s = x + y; 
    if x < y {
        let m = y;
        return (s,m);
    }else {
        let m = x;
        return (s,m);
    }
} */


}
