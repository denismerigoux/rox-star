module Proof.BloomFilter

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

open Rust
open Spec.BloomFilter
open BloomFilter

(**** Adjust slot properties ****)

#reset-options "--max_fuel 0"

let is_max (bf:bloom_storage_u8) (idx:valid_index) : Tot bool =
 slot_value bf idx = U8.uint_to_t _MAX_U8

let is_almost_max (bf:bloom_storage_u8) (idx:valid_index) : Tot bool =
  slot_value bf idx = U8.(uint_to_t _MAX_U8 -^ 1uy)

let adjust_slot_lemma (bf:bloom_storage_u8) (idx:valid_index)
  (increment:bool) (idx':valid_index): Lemma (ensures (
    let new_bf = adjust_slot bf idx increment in
    if idx' <> idx then
      slot_value new_bf idx' = slot_value bf idx'
    else begin
      if is_max bf idx then
        is_max new_bf idx
      else if increment then
	slot_value new_bf idx = U8.(slot_value bf idx +^ 1uy)
      else if slot_is_empty bf idx then
        is_max new_bf idx
      else
        slot_value new_bf idx = U8.(slot_value bf idx -^ 1uy)
    end
  )) = ()

(**** Insert hash properties ****)

let increase_or_saturate (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8)
  (hash:u32) (idx:valid_index) =
  let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
  if is_max old_bf idx then
    is_max new_bf idx
  else if idx1 <> idx2 then
    if idx = idx1 || idx = idx2 then
      slot_value new_bf idx = U8.(slot_value old_bf idx +^ 1uy)
    else slot_value new_bf idx = slot_value old_bf idx
  else if idx = idx1 then
      if is_almost_max old_bf idx1 then is_max new_bf idx1
      else slot_value new_bf idx = U8.(slot_value old_bf idx +^ 2uy)
  else slot_value new_bf idx = slot_value old_bf idx

let insert_hash_lemma (old_bf: bloom_storage_u8) (hash:u32) (idx:valid_index)
  : Lemma (ensures (
    let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
    let new_bf = insert_hash old_bf hash in
    increase_or_saturate old_bf new_bf hash idx /\
    might_contain_hash new_bf hash
  ))
  = ()

(**** Remove hash properties ****)

let is_almost_min (bf:bloom_storage_u8) (idx:valid_index) : Tot bool =
  slot_value bf idx = 1uy

let decrease_or_saturate (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8)
  (hash:u32) (idx:valid_index) =
  let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
  if is_max old_bf idx then
    is_max new_bf idx
  else if idx1 <> idx2 then
    if idx = idx1 || idx = idx2 then
      if slot_is_empty old_bf idx then
        is_max new_bf idx
      else
        slot_value new_bf idx = U8.(slot_value old_bf idx -^ 1uy)
    else slot_value new_bf idx = slot_value old_bf idx
  else if idx = idx1 then
      if is_almost_min old_bf idx || slot_is_empty old_bf idx then is_max new_bf idx
      else slot_value new_bf idx = U8.(slot_value old_bf idx -^ 2uy)
  else slot_value new_bf idx = slot_value old_bf idx

let remove_hash_lemma (bf: bloom_storage_u8) (hash:u32) (idx:valid_index)
  : Lemma (ensures (
    let new_bf = remove_hash bf hash in
    let idx1 = first_slot_index hash in
    let idx2 = second_slot_index hash in
    decrease_or_saturate bf new_bf hash idx
   ))
  = ()

(**** Insert element properties ****)

let element_invalidation (bf: bloom_storage_u8) (e:element) =
  not (might_contain_hash bf (hash e)) ==> not (contains bf.ghost_state.elements e)

let one_element_count (idx:valid_index) (sum: count) (e_count: (element & count)) : Tot count =
   let (e, count) = e_count in
   let sum = if first_slot_index (hash e) = idx then sum + count else sum in
   if second_slot_index (hash e) = idx then sum + count else sum

let all_elements_counts (bf:bloom_storage_u8) (idx:valid_index) : Tot count =
   List.Tot.Base.fold_left (one_element_count idx) 0 bf.ghost_state.elements

let count_invariant_property (bf:bloom_storage_u8) (idx:valid_index) : Tot bool =
  if is_max bf idx then true else
    all_elements_counts bf idx = U8.v (slot_value bf idx)

let count_invariant (bf:bloom_storage_u8) (idx:valid_index) =
    count_invariant_property bf idx

let insert_element_element_invalidation_lemma (bf:bloom_storage_u8) (e:element) (e':element)
  : Lemma (requires (element_invalidation bf e'))
    (ensures (element_invalidation (insert_element bf e) e'))
  = ()

#reset-options "--max_fuel 2"

let insert_element_all_elements_counts_lemma1 (bf:bloom_storage_u8) (e:element)
  : Lemma (requires (first_slot_index (hash e) <> second_slot_index (hash e)))
    (ensures (let new_bf = insert_element bf e in
       let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
       all_elements_counts new_bf idx1 = all_elements_counts bf idx1 + 1 &&
       all_elements_counts new_bf idx2 = all_elements_counts bf idx2 + 1
    ))
  = admit()

let insert_element_all_elements_counts_lemma2 (bf:bloom_storage_u8) (e:element)
  : Lemma (requires (first_slot_index (hash e) = second_slot_index (hash e)))
    (ensures (let new_bf = insert_element bf e in
       let idx = first_slot_index (hash e) in
       all_elements_counts new_bf idx = all_elements_counts bf idx + 2
    ))
  = admit()

#reset-options "--max_fuel 0"

let insert_element_count_invariant_lemma
  (bf:bloom_storage_u8) (e:element) (idx:valid_index)
  : Lemma (requires (not (is_max bf idx) /\ all_elements_counts bf idx = U8.v (slot_value bf idx)))
    (ensures (let new_bf = insert_element bf e in
      not (is_max new_bf idx) ==> all_elements_counts new_bf idx = U8.v (slot_value new_bf idx)
    ))
  = insert_hash_lemma bf (hash e) idx;
  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  let new_bf = insert_element bf e in
  if idx1 <> idx2 then
    if idx = idx1 || idx = idx2 then
      if is_max new_bf idx then () else insert_element_all_elements_counts_lemma1 bf e
    else ()
  else if idx = idx1 then
      if is_almost_max bf idx1 then ()
      else insert_element_all_elements_counts_lemma2 bf e
  else ()

(**** Remove element properties ****)

let _ = ()
