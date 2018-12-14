module BloomFilter

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

open Rust

#reset-options "--max_fuel 0"

let _KEY_SIZE: usize = 12ul

let _ARRAY_SIZE: usize = Usize.(1ul <<^ _KEY_SIZE)

let _KEY_MASK: u32 = Usize.((1ul <<^ _KEY_SIZE) -%^ 1ul)

type bloom_storage_u8 = {
  counters: array u8 _ARRAY_SIZE
}

let valid_index = i:usize{Usize.(i <^ _ARRAY_SIZE)}

val hash1: u32 -> valid_index
let hash1 hash =
  let and_value = U32.(hash &^ _KEY_MASK) in
  (* *) FStar.UInt.logand_mask (U32.v hash) 12;
  and_value

val hash2: u32 -> valid_index
let hash2 hash =
  let middle_value = U32.(hash >>^ _KEY_SIZE) in
  let and_value = U32.(middle_value &^ _KEY_MASK) in
  (* *) FStar.UInt.logand_mask (U32.v middle_value) 12;
  and_value

let first_slot_index (hash: u32) : valid_index =
  hash1 hash

let second_slot_index (hash: u32) : valid_index =
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

val adjust_slot:
  bf:bloom_storage_u8 ->
  idx:valid_index ->
  increment:bool ->
  Tot (new_bf:bloom_storage_u8)
let adjust_slot bf idx increment =
  let slot = array_index bf.counters idx in
  if slot <> 0xffuy then
    if increment then begin
      { bf with counters = array_update bf.counters idx U8.(slot +%^ 1uy) }
    end else
      { bf with counters = array_update bf.counters idx U8.(slot -%^ 1uy) }
  else bf

val adjust_first_slot:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  increment:bool ->
  Tot (new_bf:bloom_storage_u8)
let adjust_first_slot bf hash increment =
  adjust_slot bf (first_slot_index hash) increment

val adjust_second_slot:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  increment:bool ->
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
  let bf = adjust_first_slot bf hash false in
  adjust_second_slot bf hash false

#reset-options "--max_fuel 1"

val bloom_storage_u8_new : unit -> Tot bloom_storage_u8
let bloom_storage_u8_new () = {
  counters = array_new _ARRAY_SIZE 0uy ;
}
