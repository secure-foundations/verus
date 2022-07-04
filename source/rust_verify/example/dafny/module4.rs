use builtin::*;
use builtin_macros::*;

mod pervasive;
use crate::pervasive::{modes::*, seq::*, vec::*, *};
use crate::pervasive::multiset::Multiset;

verus! {

#[derive(Eq, PartialEq, Copy, Clone, Structural)]
#[repr(u64)]
pub enum Colour {
    Red = 1,
    White = 2,
    Blue = 3,
}

spec fn below(c: Colour, d: Colour) -> bool {
    c == Colour::Red || c == d || d == Colour::Blue
}

fn dutch_flag(a: &mut Vec<Colour>)
    ensures
        forall|i:int, j:int| 0 <= i < j < a.len() ==> below(a.index(i), a.index(j)),
        Multiset::from_seq(a.view()) === Multiset::from_seq(old(a).view()),
{
    let mut r:usize = 0;
    let mut w:usize  = 0;
    let b:usize = a.len();

    while w < b
        invariant
            0 <= r <= w <= b <= a.len(),
            forall|i:int| 0 <= i < r ==> a.index(i) == Colour::Red,
            forall|i:int| r <= i < w ==> a.index(i) == Colour::White,
            forall|i:int| b <= i < a.len() ==> a.index(i) == Colour::Blue,
    {
        match a.index(w) {
            Colour::Red => {
                let aw = *a.index(w);
                let ar = *a.index(r);

                a.set(r, aw);
                a.set(w, ar);

                r = r + 1;
                w = w + 1;
            },
            Colour::White => {
                w  = w + 1;
            },
            Colour::Blue => {
                let aw = *a.index(w);
                let ab_1 = *a.index(b-1);

                a.set(b-1, aw);
                a.set(w, ab_1);
            }
        };
    }
}


}

#[verifier(external)]
fn main() {}
