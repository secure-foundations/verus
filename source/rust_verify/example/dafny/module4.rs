
use builtin_macros::*;
use builtin::*;

mod pervasive;
use crate::pervasive::{*, vec::*, seq::*, modes::*};

#[derive(Eq, PartialEq, Copy, Clone)]
#[repr(u64)]
pub enum Colour {
    Red = 1, 
    White = 2, 
    Blue = 3
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


fn dutch_flag(a: Vec<Colour>)
    ensures
        forall|i:int, j:int| 0 <= i < j < a.len() ==> below(a.index(i), a.index(j)),
{
    let r = 0;
    let w = 0;
    let b = a.len();

    while w < b 
        invariant 
            0 <= r <= w <= b <= a.len(), 
            forall|i:int| 0 <= i < r ==> convert(a.index(i)) == red(), 
            forall|i:int| r <= i < w ==> convert(a.index(i)) == white(), 
            forall|i:int| b <= i < a.len() ==> convert(a.index(i)) == blue(),
    {
        match a.index(w) {
            Colour::Red => { 
            },
            Colour::White => {}, 
            Colour::Blue => {},
        };
    }
}


}

#[verifier(external)]
fn main() {}
