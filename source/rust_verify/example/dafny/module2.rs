use builtin::*;
use builtin_macros::*;

mod pervasive;
use crate::pervasive::modes::*;
use crate::pervasive::*;

#[verifier(external)]
fn main() {}

verus! {

fn my_exec_fib(n: u64) -> (result: u64)
{
    requires(fits_u64(n));
    ensures(|result: u64| result == my_spec_fib(n));
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut result: u64 = 1;
    let mut i = 1;
    while i < n
        invariant
            i > 0, i <= n,
            fits_u64(n as nat), fits_u64(i as nat),
            result == my_spec_fib(i), prev == my_spec_fib(i as nat - 1),
    {
        i = i + 1;
        proof {
            
            fib_is_monotonic(i, n);
        }
        let curr = prev + result;
        prev = result;
        result = curr;
    }
    result
}

spec fn fits_u64(n: nat) -> bool {
    my_spec_fib(n) <= 0xffff_ffff_ffff_ffff
}

spec fn my_spec_fib(n: nat) -> nat {
    decreases(n);
    if n < 2 {
        n
    } else {
        my_spec_fib(n-2) + my_spec_fib(n-1)
    }
}

proof fn fib_is_monotonic(i:nat, j: nat) {

    requires(i<=j);
    ensures(my_spec_fib(i) <= my_spec_fib(j));
    decreases(j-i);

    // ----

    if i<2 && j<2 { } else if i==j { }
    else if i==j-1 {
        reveal_with_fuel(my_spec_fib, 2);
        fib_is_monotonic(i, j-1);
    } else {
        fib_is_monotonic(i, j-1);
        fib_is_monotonic(i, j-2);
    }
}

}
