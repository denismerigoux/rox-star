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

val slot_is_empty: bf:bloom_storage_u8 -> valid_index -> Tot bool
let slot_is_empty bf idx =
  (array_index bf.counters idx) = 0uy

val first_slot_is_empty : bf:bloom_storage_u8 -> u32 -> Tot bool
let first_slot_is_empty bf hash = slot_is_empty bf (first_slot_index hash)

val second_slot_is_empty : bf:bloom_storage_u8 -> u32 -> Tot bool
let second_slot_is_empty bf hash = slot_is_empty bf (second_slot_index hash)

val might_contain_hash: bf:bloom_storage_u8 -> u32 -> bool
let might_contain_hash bf hash =
  not (first_slot_is_empty bf hash) &&
  not (second_slot_is_empty bf hash)

let modified_only_one_slot
  (old_bf:bloom_storage_u8)
  (new_bf:bloom_storage_u8)
  (idx:valid_index) =
  forall (idx':valid_index{idx <> idx'}).
  array_index new_bf.counters idx' = array_index old_bf.counters idx'

val adjust_slot:
  bf:bloom_storage_u8 ->
  idx:valid_index ->
  increment:bool{if not increment then not (slot_is_empty bf idx) else true } ->
  Tot (new_bf:bloom_storage_u8{
    modified_only_one_slot bf new_bf idx /\
    begin if increment then
      not (slot_is_empty new_bf idx)
    else
      true
    end
  })
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
  increment:bool{if not increment then not (first_slot_is_empty bf hash) else true} ->
  Tot (new_bf:bloom_storage_u8{
    let idx = first_slot_index hash in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then
      not (slot_is_empty new_bf idx)
    else
      true
    end
  })
let adjust_first_slot bf hash increment =
  adjust_slot bf (first_slot_index hash) increment

val adjust_second_slot:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  increment:bool{if not increment then not (second_slot_is_empty bf hash) else true} ->
  Tot (new_bf:bloom_storage_u8{
    let idx = second_slot_index hash in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then
      not (slot_is_empty new_bf idx)
    else
      true
    end
  })
let adjust_second_slot bf hash increment =
  adjust_slot bf (second_slot_index hash) increment

let modified_hash_slots
  (old_bf:bloom_storage_u8)
  (new_bf:bloom_storage_u8)
  (hash:u32) =
  let idx1 = first_slot_index hash in
  let idx2 = second_slot_index hash in
  forall (idx':valid_index{idx' <> idx1 /\ idx' <> idx2}).
  array_index new_bf.counters idx' = array_index old_bf.counters idx'

val insert_hash:
  bf:bloom_storage_u8 ->
  hash: u32 ->
  Tot (new_bf:bloom_storage_u8{
    modified_hash_slots bf new_bf hash /\
    might_contain_hash new_bf hash
  })
let insert_hash bf hash =
  let bf = adjust_first_slot bf hash true in
  adjust_second_slot bf hash true

val remove_hash:
  bf:bloom_storage_u8 ->
  hash:u32 ->
  Tot (new_bf:bloom_storage_u8{modified_hash_slots bf new_bf hash})
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

let lemma_remove_hash_prelim
  (bf: bloom_storage_u8)
  (removed_hash: u32)
  (idx: valid_index)
  : Lemma (requires (
    let new_bf = remove_hash bf removed_hash in
    slot_is_empty new_bf idx /\
    not (slot_is_empty bf idx)
  ))
  (ensures (False)) =
    (* Here we prove by contradiction that
       slot_is_empty bf idx ! *)
    let new_bf = remove_hash bf removed_hash in
    if (first_slot_is_empty bf removed_hash) then
      ()
    else begin
      let bf' = adjust_first_slot bf removed_hash false in
      if (second_slot_is_empty bf' removed_hash) then
	()
      else begin
        let new_bf' = adjust_second_slot bf' removed_hash false in
        assert (new_bf' = new_bf);
	(* Only this case is tricky *)
	if idx <> (first_slot_index removed_hash) &&
	  idx <> (second_slot_index removed_hash)
	then
	  ()
	else
	  admit()//We lack a lemma that says that decrementing an empty bucket will cause it to
	  // remain empty
      end
    end

let lemma_remove_hash1
  (bf: bloom_storage_u8)
  (removed_hash: u32)
  (hash: u32)
  : Lemma (requires (
    first_slot_is_empty (remove_hash bf removed_hash) hash
  ))
  (ensures (first_slot_is_empty bf hash)) =
    if not (first_slot_is_empty bf hash) then
    lemma_remove_hash_prelim bf removed_hash (first_slot_index hash)

let lemma_remove_hash2
  (bf: bloom_storage_u8)
  (removed_hash: u32)
  (hash:u32)
  : Lemma (requires (
    second_slot_is_empty (remove_hash bf removed_hash) hash
  ))
  (ensures (
    second_slot_is_empty bf hash
  )) =
  if not (second_slot_is_empty bf hash) then
    lemma_remove_hash_prelim bf removed_hash (second_slot_index hash)

val is_zeroed: bf:bloom_storage_u8 -> Tot bool
let is_zeroed bf =
  vec_all bf.counters (fun x -> x = 0uy)

let add_only_bloom_filter (bf: bloom_storage_u8) : Tot bool =
  let elements = bf.ghost_state.elements in
  all_elements elements (fun e ->
    might_contain_hash bf (hash e)
  )

let element_invalidation (bf: bloom_storage_u8) =
  (forall (e:element). (
    (not (might_contain_hash bf (hash e))) ==>
      (not (contains bf.ghost_state.elements e))
  ))

let lemma_add_only_bloom_filter
  (bf: bloom_storage_u8)
  : Lemma (ensures (
    add_only_bloom_filter bf <==>
    (forall (e:element{contains bf.ghost_state.elements e}).
      might_contain_hash bf (hash e))
  )) =
    all_elements_lemma
      #element
      bf.ghost_state.elements
      (fun e -> might_contain_hash bf (hash e))

type valid_bloom_storage_u8 = bf:bloom_storage_u8{element_invalidation bf}

type add_only_bloom_storage_u8 = bf:valid_bloom_storage_u8{add_only_bloom_filter bf}

val insert_element: bf:add_only_bloom_storage_u8 -> element -> Tot add_only_bloom_storage_u8
let insert_element bf e =
  let hash_val = hash e in
  (* *) let new_bf = { bf with ghost_state = spec_insert_element bf.ghost_state e } in
  let new_bf = insert_hash bf hash_val in
  (* *) lemma_add_only_bloom_filter bf;
  (* *) lemma_add_only_bloom_filter new_bf;
  new_bf

val remove_element: bf:valid_bloom_storage_u8 -> element -> Tot valid_bloom_storage_u8
let remove_element bf e =
  let hash_e = hash e in
  let new_bf = { bf with ghost_state = spec_remove_element bf.ghost_state e } in
  let new_bf = remove_hash bf hash_e in
  (* *) let inner_lemma
  (* *)   (e':element{not (might_contain_hash new_bf (hash e'))})
  (* *)   : Lemma (ensures (not (contains new_bf.ghost_state.elements e')))
  (* *)   =
  (* *)   let hash_e' = hash e' in
  (* *)   Classical.or_elim
  (* *)     #(first_slot_is_empty new_bf hash_e')
  (* *)     #(second_slot_is_empty new_bf hash_e')
  (* *)     #(fun _ -> first_slot_is_empty bf hash_e' \/
  (* *)       second_slot_is_empty bf hash_e')
  (* *)     (fun _ -> lemma_remove_hash1 bf hash_e hash_e')
  (* *)     (fun _ -> lemma_remove_hash2 bf hash_e hash_e');
  (* *)   ()
  (* *) in
  (* *) Classical.forall_intro inner_lemma;
  new_bf
