module BloomFilter

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

open Rust
open Spec.BloomFilter

let _BLOOM_HASH_MASK: u32 = 0x00fffffful

let _KEY_SIZE: usize = 12ul

let _ARRAY_SIZE: v:usize{U32.v v = 4096} =
  let value = Usize.(1ul <<^ _KEY_SIZE) in
  assert_norm (value = 4096ul);
  value

let _KEY_MASK: (v:u32{U32.v v = 0xfff}) =
  let value = Usize.((1ul <<^ _KEY_SIZE) -%^ 1ul) in
  assert_norm (value = 0xffful);
  value

type bloom_storage_u8 = {
  counters: array u8 _ARRAY_SIZE;
  ghost_state: spec_bloom_storage_u8
}


let valid_index = i:usize{Usize.(i <^ _ARRAY_SIZE)}

val hash1: u32 -> r:u32{U32.(r <^ _ARRAY_SIZE)}
let hash1 hash =
  let and_value = U32.(hash &^ _KEY_MASK) in
  admit();//TODO: find how to make F* understand
  and_value

val hash2: u32 -> r:u32{U32.(r <^ _ARRAY_SIZE)}
let hash2 hash =
  let and_value = U32.((hash >>^ _KEY_SIZE) &^ _KEY_MASK) in
  admit();
  and_value

let first_slot_index (hash: u32) : r:usize{Usize.(r <^ _ARRAY_SIZE)} =
  hash1 hash

let second_slot_index (hash: u32) : usize =
  hash2 hash

val slot_value: bf:bloom_storage_u8 -> valid_index -> Tot u8
let slot_value bf idx =
  array_index bf.counters idx

val slot_is_empty: bf:bloom_storage_u8 -> valid_index -> Tot bool
let slot_is_empty bf idx =
  slot_value bf idx = 0uy

val first_slot_is_empty : bf:bloom_storage_u8 -> u32 -> Tot bool
let first_slot_is_empty bf hash = slot_is_empty bf (first_slot_index hash)

val second_slot_is_empty : bf:bloom_storage_u8 -> u32 -> Tot bool
let second_slot_is_empty bf hash = slot_is_empty bf (second_slot_index hash)

val might_contain_hash: bf:bloom_storage_u8 -> u32 -> bool
let might_contain_hash bf hash =
  not (first_slot_is_empty bf hash) &&
  not (second_slot_is_empty bf hash)

let valid_incr (bf:bloom_storage_u8) (idx:valid_index) (increment:bool) =
  if not increment then not (slot_is_empty bf idx) else true

val adjust_slot:
  bf:bloom_storage_u8 ->
  idx:valid_index ->
  increment:bool{valid_incr bf idx increment} ->
  Tot (new_bf:bloom_storage_u8)
let adjust_slot bf idx increment =
  let slot = array_index bf.counters idx in
  if slot <> 0xffuy then
    if increment then begin
      { bf with counters = array_update bf.counters idx U8.(slot +^ 1uy) }
    end else
      { bf with counters = array_update bf.counters idx U8.(slot -^ 1uy) }
  else bf

val adjust_first_slot:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  increment:bool{valid_incr bf (first_slot_index hash) increment} ->
  Tot (new_bf:bloom_storage_u8)
let adjust_first_slot bf hash increment =
  adjust_slot bf (first_slot_index hash) increment

val adjust_second_slot:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  increment:bool{valid_incr bf (second_slot_index hash) increment} ->
  Tot (new_bf:bloom_storage_u8)
let adjust_second_slot bf hash increment =
  adjust_slot bf (second_slot_index hash) increment

val insert_hash:
  bf:bloom_storage_u8 ->
  hash: u32 ->
  Tot (new_bf:bloom_storage_u8)
let insert_hash bf hash =
  let bf = adjust_first_slot bf hash true in
  adjust_second_slot bf hash true

val remove_hash:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  Tot (new_bf:bloom_storage_u8)
let remove_hash bf hash =
  (* BEGIN ADDED CODE *)
  (* They never check before substracting in the slots ! Negative overflow might occur *)
  if (first_slot_is_empty bf hash)  then bf else begin
  (* END ADDED CODE*)
    let bf = adjust_first_slot bf hash false in
    (* BEGIN ADDED CODE *)
    if (second_slot_is_empty bf hash) then begin
      adjust_first_slot bf hash true
    end else
      (* END ADDED CODE *)
      adjust_second_slot bf hash false
  end

val is_zeroed: bf:bloom_storage_u8 -> Tot bool
let is_zeroed bf =
  vec_all bf.counters (fun x -> x = 0uy)

val insert_element: bf:bloom_storage_u8 -> element -> Tot bloom_storage_u8
let insert_element bf e =
  let hash_val = hash e in
  (* *) let new_bf = { bf with ghost_state = spec_insert_element bf.ghost_state e } in
  insert_hash bf hash_val

val remove_element: bf:bloom_storage_u8 -> element -> Tot bloom_storage_u8
let remove_element bf e =
  let hash_e = hash e in
  let new_bf = { bf with ghost_state = spec_remove_element bf.ghost_state e } in
  remove_hash new_bf hash_e
