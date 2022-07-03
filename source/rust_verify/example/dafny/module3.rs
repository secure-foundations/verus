
use builtin_macros::*;
use builtin::*;

mod pervasive;
use crate::pervasive::{*, vec::*, seq::*, modes::*};

verus! {

fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
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
        let d: Ghost<usize> = ghost(i2 - i1);

        let ix = i1 + (i2 - i1) / 2;
        if *v.index(ix) < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }

        assert(i2 - i1 < *d);
    }
    i1
}

}

#[verifier(external)]
fn main() {}
