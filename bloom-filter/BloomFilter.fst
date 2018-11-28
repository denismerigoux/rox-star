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

noeq type bloom_storage_u8 = {
  counters: array u8 _ARRAY_SIZE;
  ghost_state: spec_bloom_storage_u8
}


let valid_index (bf: bloom_storage_u8) = i:usize{Usize.(i <^ array_length bf.counters)}

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

val slot_is_empty: bf:bloom_storage_u8 -> valid_index bf -> Tot bool
let slot_is_empty bf idx =
  (array_index bf.counters idx) = 0uy

val first_slot_is_empty : bf:bloom_storage_u8 -> u32 -> Tot bool
let first_slot_is_empty bf hash = slot_is_empty bf (first_slot_index hash)

val second_slot_is_empty : bf:bloom_storage_u8 -> u32 -> Tot bool
let second_slot_is_empty bf hash = slot_is_empty bf (second_slot_index hash)

val adjust_slot:
  bf:bloom_storage_u8 ->
  idx:valid_index bf ->
  increment:bool{if not increment then not (slot_is_empty bf idx) else true } ->
  Tot (new_bf:bloom_storage_u8{
    forall (idx':valid_index bf{idx <> idx'}). (
      array_index new_bf.counters idx' = array_index bf.counters idx'
    )
  })
let adjust_slot bf idx increment =
  let slot = array_index bf.counters idx in
  if slot <> 0xffuy then
    if increment then begin
      let new_counters = array_update bf.counters idx U8.(slot +^ 1uy)  in
      lemma_array_update u8 _ARRAY_SIZE bf.counters idx U8.(slot +^ 1uy);
      { bf with counters = new_counters }
    end else
      { bf with counters = array_update bf.counters idx U8.(slot -^ 1uy) }
  else bf

val adjust_first_slot:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  increment:bool{if not increment then not (first_slot_is_empty bf hash) else true} ->
  Tot bloom_storage_u8
let adjust_first_slot bf hash increment =
  adjust_slot bf (first_slot_index hash) increment

val adjust_second_slot:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  increment:bool{if not increment then not (second_slot_is_empty bf hash) else true} ->
  Tot bloom_storage_u8
let adjust_second_slot bf hash increment =
  adjust_slot bf (second_slot_index hash) increment

val insert_hash: bf:bloom_storage_u8 -> u32 -> Tot bloom_storage_u8
let insert_hash bf hash =
  let bf = adjust_first_slot bf hash true in
  adjust_second_slot bf hash true

val remove_hash: bf:bloom_storage_u8 -> u32 -> Tot bloom_storage_u8
let remove_hash bf hash =
  (* BEGIN ADDED CODE *)
  (* They never check before substracting in the slots ! Negative overflow might occur *)
  if (first_slot_is_empty bf hash) then bf else begin
  (* END ADDED CODE*)
    let bf = adjust_first_slot bf hash false in
    (* BEGIN ADDED CODE *)
    if (second_slot_is_empty bf hash) then adjust_first_slot bf hash true else
    (* END ADDED CODE *)
    adjust_second_slot bf hash false
  end

val might_contain_hash: bf:bloom_storage_u8 -> u32 -> bool
let might_contain_hash bf hash =
  not (first_slot_is_empty bf hash) &&
  not (second_slot_is_empty bf hash)


let is_valid_bloom_filter (bf: bloom_storage_u8) : Tot bool =
  let elements = bf.ghost_state.elements in
  all_elements elements (fun (e, _) ->
    might_contain_hash bf (hash e)
  )

type valid_bloom_storage_u8 = bf:bloom_storage_u8{is_valid_bloom_filter bf}

val is_zeroed: bf:bloom_storage_u8 -> Tot bool
let is_zeroed bf =
  vec_all bf.counters (fun x -> x = 0uy)

val insert_element: bf:valid_bloom_storage_u8 -> element -> Tot valid_bloom_storage_u8
let insert_element bf e =
  let hash_val = hash e in
  let bf = { bf with ghost_state = spec_insert_element bf.ghost_state e } in
  let new_bf = insert_hash bf hash_val in
  (* *)
  let elements = bf.ghost_state.elements in
  all_elements elements (fun (e', _) ->
    let cond = might_contain_hash bf (hash e') in
    if e <> e' then assert(cond) else ();
    cond
  );
  admit();
  new_bf

val remove_element: bf:valid_bloom_storage_u8 -> element -> Tot valid_bloom_storage_u8
let remove_element bf e =
  let hash = hash e in
  let bf = { bf with ghost_state = spec_remove_element bf.ghost_state e } in
  remove_hash bf hash
