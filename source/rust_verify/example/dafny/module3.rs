
use builtin_macros::*;
use builtin::*;

mod pervasive;
use crate::pervasive::{*, vec::*, seq::*, modes::*};

verus! {

/* fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v.index(i) <= v.index(j),
        exists|i:int| 0 <= i < v.len() && k == v.index(i),
    ensures
        r < v.len(),
        k == v.index(r),
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            i2 < v.len(),
            exists|i:int| i1 <= i <= i2 && k == v.index(i),
            forall|i:int, j:int| 0 <= i <= j < v.len() ==> v.index(i) <= v.index(j),
    {
        let d = i2 - i1;

        let ix = i1 + (i2 - i1) / 2;
        if *v.index(ix) < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }

        assert(i2 - i1 < d);
    }
    i1
} */

proof fn mid_is_between(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        lo <= (lo + hi) / 2 && (lo + hi) / 2 <= hi,
{
    // let mid = (lo + hi) / 2;
    // assert(lo <= hi);
    // assert(lo + lo <= hi + lo); // by math
    // assert(lo * 2 <= lo + hi);
    // assert((lo * 2) / 2 <= (lo + hi) / 2);
    // assert(lo <= mid); // by (nonlinear_arith);
}

spec fn foo(a: int, b: int) -> bool {
    true
}

fn binary_search(v: &Vec<i64>, k: i64) -> (r: isize) 
    requires 
        forall|i:int, j:int| 0 <= i < j < v.len() ==> v.index(i) <= v.index(j),
    ensures 
        0 <= r ==> (r as nat) < v.len() && v.index(r as nat) == k,
        r < 0 ==> forall|i:int| 0 <= i < v.len() ==> (#[trigger] v.index(i as nat)) != k
{
    let mut lo = 0;
    let mut hi = v.len();

    while lo < hi 
        invariant 
            0 <= lo <= hi <= v.len(),
            forall|i:int, j:int| #![trigger foo(i, j)] 0 <= i < j < v.len() ==> v.index(i) <=  v.index(j),
            forall|i:int| 0 <= i < lo ==> v.index(i) != k, 
            forall|i:int| hi <= i < v.len() ==> v.index(i) != k
    {
        let mid = (lo + hi) / 2;
        proof {
            assert(lo >= 0);
            assert(hi >= 0);
            mid_is_between(lo, hi);
            assume(lo <= (lo + hi) / 2); // TODO incompleteness
        }
        if k < *v.index(mid) {
            assert(forall|i:int| hi <= i < v.len() ==> v.index(i) != k);
            assert(mid <= hi);
            let prev_hi: Ghost<usize> = ghost(hi);
            hi = mid;

            assert forall|i:int| hi <= i < v.len() implies v.index(i) != k by {
                if *prev_hi as int <= i {
                    assert(v.index(i) != k);
                } else {
                    assert(k < v.index(hi));
                    assert(foo(hi, i));
                    assert(v.index(hi) <= v.index(i));
                    assert(v.index(i) > k);
                    assert(v.index(i) != k);
                }
            }
        } else if *v.index(mid) < k {
            lo = mid + 1;
            assume(forall|i:int| 0 <= i < lo ==> v.index(i) != k); 
        } else {
            return mid as isize;
        }
    }

    return -1;
}

}

#[verifier(external)]
fn main() {}
