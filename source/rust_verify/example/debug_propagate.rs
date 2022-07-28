// rust_verify/tests/example.rs expect-failures

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
use crate::pervasive::{*, seq::*, vec::*};

// We are performing error localization by expression splitting.
// This is great in that it helps finding the small expression that causes the verification failure.
// When there's one or more nested spec function calls, however, to examine the failing small expression in the original context,
// Verus developers still need to manually replace the formal argument in the splitted expression with the values from the original call site.
// These examples tries to do this work automatically.

// However, sometimes the propagated expressions can get large(e.g. several harmless "&& true")
// To help these situations, we can normalize the expressions before displaying it to the end user.

// We can also consider propagating it to the inner level if it's not readily readable (e.g. match case with inner fields usage --
// -- something like   !(good_msg.is_type(Quit)) ==> good_msg.is_type(Move)==> let x = good_msg.x in let y = good_msg.y in !(x - y == 5))
// which is just a match case  `Message::Move{x, y} => is_good_integer(x-y),`
// we can just use the formal parameter in this cases, while using propagated values for other parameters


verus!{

// example1: show the failing small expression in terms of the call site's value
spec fn is_increasing_and_positive(x:int, y:int, z: int) -> bool 
{
  0 <= x
//^^^^^^  failing assertion: `0 <= spec_index(s1, 0) - spec_index(s2, 0)`
  && x <= y
  && y <= z
}


proof fn test_propagation_1_level() 
{
  let s1 = Seq::new(10, |x:int| 4*x-2);
  let s2 = Seq::new(10, |x:int| 2*x);
  assert(is_increasing_and_positive(s1[0] - s2[0], s1[1] - s2[1], s1[2] - s2[2]));
//^^^^^^ ----------------------------------------------------------------------- 0 <= spec_index(s1, 0) - spec_index(s2, 0) && spec_index(s1, 0) - spec_index(s2, 0) <= spec_index(s1, 1) - spec_index(s2, 1) && spec_index(s1, 1) - spec_index(s2, 1) <= spec_index(s1, 2) - spec_index(s2, 2)
}



// example2: propagating values from the call site to the inner-most spec function
spec fn twice_and_positive(a:int, b:int) -> bool {
  0 < a
//^^^^^ failing assertion: `Forall i , 0 <= i && i < len(view(v1)) ==> 0 < spec_index(view(v1), i)`
  && a <= b
}

spec fn seq_twice(s1: Seq<int>, s2: Seq<int>) -> bool {
  (s1.len() == s2.len()) && (forall |i:int| (0 <= i < s1.len()) ==> twice_and_positive(s1[i], s2[i]))
//                                                                  -------------------------------- 0 < spec_index(view(v1), i) && spec_index(view(v1), i) <= spec_index(view(v2), i)
}

fn test_propagation_2_level() 
{
  let mut v1 = Vec::empty();
  v1.push(0);
  v1.push(1);
  v1.push(2);
  let mut v2 = Vec::empty();
  v2.push(0);
  v2.push(2);
  v2.push(4);
  assert(seq_twice(v1@, v2@));
//^^^^^^ ------------------- len(view(v1)) == len(view(v2)) && Forall i , 0 <= i && i < len(view(v1)) ==> twice_and_positive(spec_index(view(v1), i), spec_index(view(v2), i))
}


// example3: don't replace parameter with argument unless its simplified 









#[verifier(external)]
fn main() {
}
} // verus!