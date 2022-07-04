use builtin::*;
use builtin_macros::*;

mod pervasive;
use crate::pervasive::{modes::*, seq::*, vec::*, *};

#[derive(Eq, PartialEq, Copy, Clone)]
#[repr(u64)]
pub enum Colour {
    Red = 1,
    White = 2,
    Blue = 3,
}

verus! {

#[verifier(external_body)]
spec fn red() -> u64 {
    Colour::Red as u64
}

#[verifier(external_body)]
spec fn white() -> u64 {
    Colour::White as u64
}

#[verifier(external_body)]
spec fn blue() -> u64 {
    Colour::Blue as u64
}

#[verifier(external_body)]
spec fn convert(c: Colour) -> u64 {
    c as u64
}

spec fn below(c: Colour, d: Colour) -> bool {
    let c: u64 = convert(c);
    let d: u64 = convert(d);
    c == red() || c == d || d == blue()
}

// Wait till verus is ready 
/* fn dutch_flag(mut a: Vec<Colour>)
    ensures
        forall|i:int, j:int| 0 <= i < j < a.len() ==> below(a.index(i), a.index(j)),
{
    let mut r:usize = 0;
    let mut w:usize  = 0;
    let b:usize = a.len();

    while w < b
        invariant
            0 <= r <= w <= b <= a.len(),
            forall|i:int| 0 <= i < r ==> convert(a.index(i)) == red(),
            forall|i:int| r <= i < w ==> convert(a.index(i)) == white(),
            forall|i:int| b <= i < a.len() ==> convert(a.index(i)) == blue(),
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
} */


}

#[verifier(external)]
fn main() {}
