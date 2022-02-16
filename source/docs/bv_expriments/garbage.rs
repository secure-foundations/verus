#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;
use builtin_macros::*;

#[spec]
#[verifier(external_body)]
pub fn get_bit(bv:u32, loc:u32) -> bool {
    unimplemented!();
}

// (assert
//     (forall ((bv@ Poly) (loc@ Poly)) (!                              ;int2bv
//       (= (get_bit.? bv@ loc@) (= #b1 ((_ extract (%I loc) (%I loc)) (%I bv)) ) )
//       :pattern ((get_bit.? bv@ loc@))
//   )))

#[spec]
#[verifier(external_body)]
pub fn set_bit(bv:u32, loc:u32, bit:bool) -> u32 {
    unimplemented!();
} 
//   (assert
//     (forall ((bv@ Poly) (loc@ Poly) (bit@ Poly)) (!                       ;int2bv ;bool2int                               ;int2bv
//       (= (set_bit.? bv@ loc@ bit@) (concat ((_ extract 31 (+ (%I loc) 1)) (%I bv)) (%B bit) ((_ extract (- (%I loc) 1) 0) (%I bv))) )
//                                   ;bv2int
//       :pattern ((set_bit.? bv@ loc@))
//   )))

#[exec]
fn get_bit_exec(bv:u32, loc:u32) -> bool {
    ensures(|ret:bool| ret == get_bit(bv,loc));
    assert_bit_vector((0x1u32 & (bv>>loc) == 1) == get_bit(bv, loc));
    if 0x1u32 & bv>>loc == 1 {true}
    else {false}
}

#[exec]
fn set_bit_exec(bv:u32, loc:u32, bit:bool) -> u32 {
    ensures(|ret:u32| ret == set_bit(bv,loc,bit));
    assert_bit_vector((if bit { bv | 1u32 << loc } else { bv & (!(1u32 << loc)) }) == set_bit(bv, loc, bit));
    let one = 1u32 << loc;
    if bit {
        bv | one
    }
    else {
        bv & (!one)
    }
}

#[proof]
fn set_bit_property(bv:u32, loc:u32, loc2: u32, bit:bool) -> u32 {
    requires([
        loc < 32,
        loc2 < 32,
        loc != loc2
    ]);
    ensures(|bv2:u32| 
            bv2 == set_bit(bv,loc,bit) &&
            get_bit(bv2, loc2) == get_bit(bv, loc2) &&
            get_bit(bv2, loc) == bit &&
            (bv == bv2 >>= (get_bit(bv,loc) == bit) ) &&
            (bv != bv2 >>= (get_bit(bv,loc) == !bit) )
    );

    #[spec] let bv2 = set_bit(bv, loc, bit);
    assert_bit_vector((bv2 == set_bit(bv, loc, bit) && (loc < 32) && (loc2 < 32) && (loc != loc2)) 
                           >>= get_bit(bv2, loc2) == get_bit(bv, loc2));
    assert_bit_vector((bv2 == set_bit(bv, loc, bit) && (loc < 32))  
                           >>= get_bit(bv2, loc) == bit);
    assert_bit_vector((bv2 == set_bit(bv, loc, bit) && (loc < 32) && bv == bv2)  
                           >>= get_bit(bv, loc) == bit);
    assert_bit_vector((bv2 == set_bit(bv, loc, bit) && (loc < 32) && bv != bv2)  
                           >>= get_bit(bv, loc) == !bit);
    bv2
}


#[derive(Structural, PartialEq, Eq)]
enum Color {
    White,     // 00
    Gray,      // 01
    Black,     // 10
    Undefined, // 11
}

#[spec]
fn color_view(high:bool, low:bool) -> Color {
    if high {if low {Color::White} else {Color::Gray}}
    else {if low {Color::Black} else {Color::Undefined}}
}

#[exec]
fn color_to_bits(c: Color) -> (bool, bool) {
    match c {
        Color::White => (false, false),
        Color::Gray =>  (false, true),
        Color::Black => (true, false),
        Color::Undefined => (true, true),
    }
}

// #[proof]
// fn bucket_element(bucket: u32, i:u32) {
//     requires(i<32);
//     ensures([
//         bucket_view(bucket,15).index(i) == color_view(get_bit(bucket,2*i+1), get_bit(bucket,2*i)) ,
//     ]);
//     reveal_with_fuel(bucket_view, 3);
// }

#[proof]
fn bucket_element(bucket1:u32, bucket2:u32, index:u32){
    requires([
        index < 32,
        bucket_view(bucket1,15).index(index) == bucket_view(bucket2,15).index(index),
    ]);
    ensures(
        get_bit(bucket1, index*2) == get_bit(bucket2, index*2) &&
        get_bit(bucket1, index*2 + 1) == get_bit(bucket2, index*2 + 1)
    )
}

#[spec]
fn bucket_view(bucket: u32, index: u32) -> Seq<Color> {
    decreases(index);
    
    let up_bit:bool = get_bit(bucket, index*2 + 1);
    let low_bit:bool = get_bit(bucket, index*2);
    let c:Color = color_view(up_bit,low_bit);

    if index == 0 {
        seq![c]
    } else {
        seq![c].add(bucket_view(bucket, index-1))
    }
}

// #[exec]
// fn set_color(bucket:u32, high:bool, low:bool , index:u32, #[proof] ghost_bucket:Seq<Color>) -> u32 {
//     requires([
//         index < 16,
//         bucket_view(bucket, 15).ext_equal(ghost_bucket)
//     ]);
//     ensures(|new_bucket: u32| [
//         bucket_view(new_bucket, 15).ext_equal(ghost_bucket.update(index, color_view(high,low))),
//     ]);

//     reveal_with_fuel(bucket_view, 3);  // 15?

//     let bucket1 = set_bit_exec(bucket, 2*index+1, high);
//     let new_bucket = set_bit_exec(bucket1, 2*index, low);
//     assert(bucket_view(bucket,15).index(index) == color_view(high,low));
//     new_bucket
// }

fn main(){}

    // shift is uintshift, hence there is no sementic....  maybe I need `variable support` for assert_bit_vector
    // 1. I can support the  semantics of <<,!, etc.   OR
    // 2. make function mode, and interpret everything as bitvector in bv function mode
    
    // implement forall in assert_bit_vector
    // fix 
    // make gc work
    // bv function mode ?
    // separate process