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

#[verifier(external)]
fn main() {
}

verus!{

// exmaple 0: conjunt
proof fn test_expansion_very_easy() 
{
  let x = 5;
  assert((x >= 0) && (x != 5));
  //                  ^^^^^^^
}


// example1: simple function inline
// 
// TODO: check the span of `&&&`
// spec fn is_good_integer(z: int) -> bool 
// {
//   &&& z >= 0
//   &&& z != 5
// }
spec fn is_good_integer(z: int) -> bool 
{
  z >= 0 && z != 5
//          ^^^^^^
}

proof fn test_expansion_easy() 
{
  let x = 5;
  assert(is_good_integer(x));
}



// example2: simple `match` inline
spec fn is_good_opt(opt: Option<int>) -> bool
{
  match opt {
    Option::Some(k) => k > 10,
    Option::None => true,
  }
}

proof fn test_expansion_match() {
  let x = Option::Some(5);
  let y = Option::Some(4);
  assert(is_good_opt(x));
}



// example3: 2-level failure
spec fn is_good_integer_2(z: int) -> bool 
{
  z >= 0 && z != 5
//          ^^^^^^
}
spec fn is_good_option(opt: Option<int>) -> bool
{
  match opt {
    Option::Some(x) => is_good_integer_2(x),
//                     ^^^^^^^^^^^^^^^^^^^^
    Option::None => true,
  }
}

proof fn test_expansion() {
  let x = Option::Some(5);
  let y = Option::Some(4);
  assert(is_good_option(x));
//^^^^^^ ^^^^^^^^^^^^^^^^^
}

// example4: 3-level failure
#[derive(PartialEq, Eq)] 
pub enum Message {
    Quit(bool),
    Move { x: i32, y: i32 },
    Write(bool),
}

spec fn is_good_integer_3(x: int) -> bool 
{
    x >= 0 && x != 5
//  ^^^^^^^
}

spec fn is_good_message(msg:Message) -> bool {
    match msg {
        Message::Quit(b) => b,
        Message::Move{x, y} => is_good_integer_3( (x as int)  - (y as int)),
//                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        Message::Write(b) => b,
    }
}

spec fn is_good(msg: Message) -> bool {
  is_good_message(msg)
//^^^^^^^^^^^^^^^^^^^^
}

proof fn test_expansion_multiple_call() {
  let x = Message::Move{x: 5, y:6};
  assert(is_good(x));
//^^^^^^ ^^^^^^^^^^
}


// example5: negation
spec fn is_good_integer_5(x: int) -> bool 
{
    !(x < 0 || !(x != 5))
//  |          | ^^^^^^
//  |          This leftmost boolean-not negated the highlighted expression
//  This leftmost boolean-not negated the highlighted expression
}

proof fn test_expansion_negate() 
{
  let x = 5;
  assert(is_good_integer(x));
//^^^^^^ ^^^^^^^^^^^^^^^^^^
}



}