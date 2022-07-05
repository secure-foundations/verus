// rust_verify/tests/example.rs expect-failures

extern crate builtin;
#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;

fn main() {}

// Example1: simple struct
#[derive(PartialEq, Eq)]
struct ValidI64 {
    val: i64,
    is_nan: bool,
}

#[proof]
fn make_positive_integer(n1: i64, n2: i64) -> ValidI64 {
    requires(n1 > 0);       // comment this to make this proof fail
    ensures(|ret:ValidI64| ret.val > 0);

    let num1 = ValidI64{val: n1, is_nan: false};
    let num2 = ValidI64{val: n2, is_nan: false};
    num1   
}



// Example 2: enum
#[derive(PartialEq, Eq)]
pub enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(bool),
}

#[spec]
fn pred_message(msg: Message) -> bool {
    match msg {
        Message::Quit => true,
        Message::Move{x, y} => x > y,
        Message::Write(b) => b,
    }
}

#[exec]
fn max(n1: i32, n2: i32) -> i32 {
    ensures(|ret:i32| (ret >= n1) && (ret >= n2) && ( (ret == n1) || (ret == n2) ));
    if n1 > n2 {n1} else {n2}
}

#[exec]
fn min(n1: i32, n2: i32) -> i32 {
    ensures(|ret:i32| (ret <= n1) && (ret <= n2) && ( (ret == n1) || (ret == n2) ));
    if n1 < n2 {n1} else {n2}
}


#[exec] 
fn update_message(msg: Message) -> Message {
    // ensures(|ret:Message| pred_message(ret));            // uncomment this to make this fail
    match msg {
        Message::Quit => msg,
        Message::Move{x, y} => Message::Move{x: max(x,y), y: min(x,y)},
        Message::Write(b) => Message::Write(true),
    }
}


 
// Example 3: enum + Generic Type
enum Option<T> {
    None,
    Some(T),
}

#[spec]
fn is_some(a: crate::Option<i32>) -> bool {
    match a {
        crate::Option::Some(_) => true,
        crate::Option::None => false,
    }
}

#[spec]
fn is_positive(a: crate::Option<i32>) -> bool {
    match a {
        crate::Option::Some(val) => val > 0,
        crate::Option::None => false,
    }
}

#[exec]
fn minus_one_if_positive(a: crate::Option<i32>) ->  crate::Option<i32> {
    // requires(is_some(a));       // wrong requires
    requires(is_positive(a));      // correct requires
    ensures(|ret: crate::Option<i32>| is_some(ret));

    if let crate::Option::Some(val_a)  = a {
        if val_a <= 0 {
            crate::Option::None
        }
        else {
            crate::Option::Some(val_a - 1)
        }
    } else{
        crate::Option::None
    }
}



// Example 4: tuple of enum with generic type 
#[exec]
fn add_two_int(a: crate::Option<i32>, b: crate::Option<i32>) ->  crate::Option<i32> {
    requires([is_some(a), is_some(b)]);
    ensures(|ret: crate::Option<i32>| is_some(ret));

    if let ( crate::Option::Some(val_a),  crate::Option::Some(val_b)) = (a,b) {
        if val_a != 0 {
            crate::Option::None
        }
        else {
            crate::Option::Some(val_a + val_b)
        }
    } else{
        crate::Option::None
    }
}



// Example 5: Simple tuple
#[proof]
fn test_tuple(x1: i32, x2:i32) -> (u32, u32) {
    requires([
        x1 == 0,       // comment this to make this proof fail
        x2 >= 0,
    ]);
    ensures(|ret:(u32,u32)| ret.0 == 0);
    let tup = (x1 as u32, x2 as u32);
    tup
}



// Example 6: more complex enum
enum ComplexMessage {
    Quit(crate::Option<Message>),
    Move { x: i32, y: i32 },
    Write(bool),
}

#[proof]
fn test_complex_enum(msg: ComplexMessage) {
    match msg {
        ComplexMessage::Quit(crate::Option::Some(Message::Move{x, y})) => {
            assert(x > y);
            assert(true);
        }
        _ => (),
    };
    assert(true);
}


// Example 7: mutable enum
#[exec]
fn test_mutable_enum() -> u32 {
    let mut m:Message = Message::Move{x:0, y:1};
    m = Message::Move{x:3, y:100};
    m = Message::Write(false);
    m = Message::Quit;
    assert(false);
    0   // TODO: last line snap set to 0_entry instead of 3_mutation
}


// #[proof]
// fn test_complex_enum(msg: (ComplexMessage, Message)) {
//     match msg {
//         // TODO: typ param 0, 1
//         (ComplexMessage::Quit(crate::Option::Some(Message::Move{x, y})),  Message::Write(b)) => assert( (x > y) || b),
//         _ => (),
//     };
//     assert(true);
// }


// #[exec]
// fn test_mutable_struct() -> u32 {
//     let mut v = ValidI64{val:0, is_nan: false};
//     v.val = 100;         // TODO: partial assignment
//     assert(false);
//     0   
// }


// Failing example:
// TODO: renaming local variable into something like `x$1@`.  
// #[derive(PartialEq, Eq)] 
// pub enum Message {
//     Quit(bool),
//     Move { x: i32, y: i32 },
//     Write(bool),
// }

// spec fn is_good_message(msg:Message) -> bool {
//     match msg {
//         Message::Quit(b) => b,
//         Message::Move{x, y} => is_good_integer( (x as int)  - (y as int)),
// //                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//         Message::Write(b) => b,
//     }
// }

// // // example: requires
// spec fn is_good_integer(x: int) -> bool 
// {
//   x >= 0 && x != 5
// }

// proof fn test_require_failure(m:Message) -> (good_int: int)
//   requires 
//     is_good_message(m),
//   ensures
//     is_good_integer(good_int),
// {
//     match m {
//         Message::Quit(b) => return 0,
//         Message::Move{x, y} => return ((x as int)  - (y as int)),
//         Message::Write(b) => return 0,
//     }
// }

// proof fn test_10(x:int) {
//   let x = Message::Move{x: 0, y: 5};
//   test_require_failure(x);
//   assert(false);
// }