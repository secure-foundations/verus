
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use pervasive::option::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::modes::*;
#[allow(unused_imports)]
use crate::pervasive::{*, seq::*, vec::*, multiset::*};


verus!{

spec fn sorted(v: Seq<u32>) -> bool {
    forall(|i:int, j:int| ((0 <= i) && (i <= j) && (j < v.len())) ==> (v[i] <= v[j]))
}

// v[0..n] is sorted
spec fn sorted_to_n(v: Seq<u32>, n:usize) -> bool {
  n <= v.len() && forall(|i:int, j:int| ((0 <= i) && (i <= j) && (j < n)) ==> (v[i] <= v[j]))
}

fn swap(v: &mut Vec<u32>, i:usize, j:usize) 
    requires 
        i < old(v)@.len(),
        j < old(v)@.len(),
    ensures
        v@[i] == old(v)@[j],
        v@[j] == old(v)@[i],
        v@.len() == old(v)@.len(),
        forall |k:int| (0<= k < v@.len()) && k !=i && k != j ==> v@[k] == old(v)@[k] 
{
    let a = *v.index(i);
    let b = *v.index(j);
    v.set(i, b);
    v.set(j, a);
}

// `multiset_from_seq` is copied from summer_school/chapter-2-3.rs:52
spec fn multiset_from_seq<T>(input: Seq<T>) -> Multiset<T>
{
    decreases(input.len()); // TODO(utaal): when bug fixed, remove len
    // show we CAN build a multiset constructively from a seq
    if input.len()==0 {
        Multiset::empty()
    } else {
        multiset_from_seq(input.drop_last()).insert(input.last())
    }
}

// find smallest element from v[start..], and swap that element with v[start]
#[verifier(external_body)]
fn move_smallest_to_start(v: &mut Vec<u32>, start:usize) 
    requires 
        forall |i:int, j:int| (0 <= i < start) && (start <= j < old(v)@.len()) ==> old(v)@[i] <= old(v)@[j],
        start < old(v)@.len(),
    ensures
        old(v)@.len() == v@.len(),
        forall |i:int| 0 <= i < start ==> v@[i] == old(v)@[i],
        forall |i:int| start < i < v@.len() ==> (v@[start] <= v@[i]),   
        multiset_from_seq(v.view()).ext_equal(multiset_from_seq(old(v).view())),
        forall |i:int, j:int| (0 <= i < start) && (start <= j < old(v)@.len()) ==> v@[i] <= v@[j],
{
  // TODO: find smallest elt, and swap with start
  // let mut min = start;
  // while min < v.len()
  //     invariant 

}

// TODO
// spec fn partitioned(..)

fn selection_sort(v: &mut Vec<u32>) 
  requires 
    old(v)@.len() > 0,
  ensures 
    sorted(v@),
    v@.len() == old(v)@.len(),
    multiset_from_seq(v@).ext_equal(multiset_from_seq(old(v)@)),        // REVIEW: how this get proved when while-loop invariants do not say about this property?
                                                                        // Can I "expand" functions outside of this file(such as ext_equal)?
{
  let mut i:usize = 0;
  let mut j:usize = 0;

  while i < v.len() 
      invariant
          i <= v@.len(),
          sorted_to_n(v@, i),
          forall |k1:int, k2:int| (0 <= k1 < i <= k2 < v@.len()) ==> v@[k1] <= v@[k2],
        //   multiset_from_seq(v@).ext_equal(multiset_from_seq(old(v)@)),
  {
      move_smallest_to_start(v, i);
      i = i + 1;
  }
}



#[verifier(external)]
fn main() {
}

} // verus!