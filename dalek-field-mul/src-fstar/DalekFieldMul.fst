module DalekFieldMul

module U128 = FStar.UInt128
module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

open Rust

#reset-options "--max_fuel 0"

type is_54bits (x:u64) = U64.(x <^ (1uL <<^ 54ul))

type field_element_32 = array u64 5ul

val mul: self:field_element_32 -> rhs: field_element_32 -> Pure field_element_32
  (requires (
    is_54bits self.(0ul) /\ is_54bits self.(1ul) /\
    is_54bits self.(2ul) /\ is_54bits self.(3ul) /\ is_54bits self.(4ul)
  ))
  (ensures (fun _ -> True))
let mul self rhs =
  let m (x:u64) (y:u64) : Tot u128 = U128.mul_wide x y in
  let a : array u64 5ul = self in
  let b : array u64 5ul = self in
  let b1_19 = U64.(b.(1ul) *%^ 19uL) in
  let b2_19 = U64.(b.(2ul) *%^ 19uL) in
  let b3_19 = U64.(b.(3ul) *%^ 19uL) in
  let b4_19 = U64.(b.(4ul) *%^ 19uL) in
  let c0 : u128 = U128.(
      (m a.(0ul) b.(0ul)) +%^ (m a.(4ul) b1_19) +%^ (m a.(2ul) b3_19) +%^ (m a.(1ul) b4_19)
  ) in
  let c1 : u128 = U128.(
      (m a.(1ul) b.(0ul)) +%^ (m a.(0ul) b.(1ul)) +%^ (m a.(2ul) b3_19) +%^ (m a.(1ul) b4_19)
  ) in
  let c2 : u128 = U128.(
      (m a.(2ul) b.(0ul)) +%^ (m a.(1ul) b.(1ul)) +%^ (m a.(2ul) b3_19) +%^ (m a.(1ul) b4_19)
  ) in
  let c3 : u128 = U128.(
      (m a.(3ul) b.(0ul)) +%^ (m a.(2ul) b.(1ul)) +%^ (m a.(2ul) b3_19) +%^ (m a.(1ul) b4_19)
  ) in
  let c4 : u128 = U128.(
      (m a.(4ul) b.(0ul)) +%^ (m a.(3ul) b.(1ul)) +%^ (m a.(2ul) b3_19) +%^ (m a.(1ul) b4_19)
  ) in
  let _LOW_51_BIT_MASK : u64 = U64.((1uL <<^ 51ul) -%^ 1uL) in
  let out = array_new 5ul 0uL in
  let c1 = U128.((c1 +%^ u64_to_u128 (u128_to_u64 U128.(c0 >>^ 51ul)))) in
  let out = array_update out 0ul U64.((u128_to_u64 c0) &^ _LOW_51_BIT_MASK) in
  let c2 = U128.((c2 +%^ u64_to_u128 (u128_to_u64 U128.(c1 >>^ 51ul)))) in
  let out = array_update out 1ul U64.((u128_to_u64 c1) &^ _LOW_51_BIT_MASK) in
  let c3 = U128.((c3 +%^ u64_to_u128 (u128_to_u64 U128.(c2 >>^ 51ul)))) in
  let out = array_update out 2ul U64.((u128_to_u64 c2) &^ _LOW_51_BIT_MASK) in
  let c4 = U128.((c4 +%^ u64_to_u128 (u128_to_u64 U128.(c3 >>^ 51ul)))) in
  let out = array_update out 3ul U64.((u128_to_u64 c3) &^ _LOW_51_BIT_MASK) in
  let carry : u64 = u128_to_u64 U128.(c4 >>^ 51ul) in
  let out = array_update out 4ul U64.((u128_to_u64 c4) &^ _LOW_51_BIT_MASK) in
  let out = array_update out 0ul U64.(out.(0ul) +%^ carry *%^ 19uL) in
  let out = array_update out 1ul U64.(out.(0ul) >>^ 51ul) in
  let out = array_update out 0ul U64.(out.(0ul) &^ _LOW_51_BIT_MASK) in
  out
