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

let modified_only_one_slot (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8) (idx:valid_index) =
  forall (idx':valid_index{idx <> idx'}). slot_value new_bf idx' = slot_value old_bf idx'

let adjust_slot_lemma (bf:bloom_storage_u8) (idx:valid_index)
  (increment:bool{valid_incr bf idx increment}) : Lemma (ensures (
    let new_bf = adjust_slot bf idx increment in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then not (slot_is_empty new_bf idx) else true end
  )) = ()

let adjust_first_slot_lemma (bf:bloom_storage_u8) (hash:u32)
  (increment:bool{valid_incr bf (first_slot_index hash) increment}) : Lemma (ensures (
    let new_bf = adjust_first_slot bf hash increment in
    let idx = first_slot_index hash in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then not (slot_is_empty new_bf idx) else true end
  )) = adjust_slot_lemma bf (first_slot_index hash) increment

let adjust_second_slot_lemma (bf:bloom_storage_u8) (hash:u32)
  (increment:bool{valid_incr bf (second_slot_index hash) increment}) : Lemma (ensures (
    let new_bf = adjust_second_slot bf hash increment in
    let idx = second_slot_index hash in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then not (slot_is_empty new_bf idx) else true end
  )) = adjust_slot_lemma bf (second_slot_index hash) increment


(**** Insert hash properties ****)

let modified_hash_slots (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8) (hash:u32) =
  let idx1 = first_slot_index hash in
  let idx2 = second_slot_index hash in
  forall (idx':valid_index{idx' <> idx1 /\ idx' <> idx2}).
  slot_value new_bf idx' = slot_value old_bf idx'

let insert_hash_prelim_lemma (bf: bloom_storage_u8) (idx: valid_index)
  : Lemma (requires (U8.v (slot_value bf idx) < _MAX_U8))
    (ensures (U8.v (slot_value (adjust_slot bf idx true) idx) = U8.v (slot_value bf idx) + 1))
  = ()

let increase_or_saturate (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8) (idx:valid_index) =
  if U8.v (slot_value old_bf idx) = _MAX_U8 then
    U8.v (slot_value new_bf idx) = _MAX_U8
  else
    U8.(slot_value new_bf idx >^ slot_value old_bf idx)

let insert_hash_lemma1 (bf: bloom_storage_u8) (hash:u32)
  : Lemma (ensures (increase_or_saturate bf (insert_hash bf hash) (first_slot_index hash)))
  = let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
  let bf0 = adjust_first_slot bf hash true in
  adjust_first_slot_lemma bf hash true; adjust_second_slot_lemma bf0 hash true;
  if U8.v (slot_value bf idx1) = _MAX_U8 then () else begin
    insert_hash_prelim_lemma bf idx1;
    if idx1 = idx2 then if U8.v (slot_value bf0 idx1) = _MAX_U8 then () else
        insert_hash_prelim_lemma bf0 idx1
    else ()
  end

let insert_hash_lemma2 (bf: bloom_storage_u8) (hash:u32)
  : Lemma (ensures (increase_or_saturate bf (insert_hash bf hash) (second_slot_index hash)))
  = let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
  let bf0 = adjust_first_slot bf hash true in
  adjust_first_slot_lemma bf hash true; adjust_second_slot_lemma bf0 hash true;
  if U8.v (slot_value bf idx2) = _MAX_U8 then () else begin
    insert_hash_prelim_lemma bf idx2;
    if U8.v (slot_value bf0 idx2) = _MAX_U8 then () else
        insert_hash_prelim_lemma bf0 idx2
  end

let insert_hash_lemma (bf:bloom_storage_u8) (hash:u32) : Lemma (ensures (
    let new_bf = insert_hash bf hash in
    let idx1 = first_slot_index hash in
    let idx2 = second_slot_index hash in
    modified_hash_slots bf new_bf hash /\
    might_contain_hash new_bf hash /\
    increase_or_saturate bf new_bf idx1 /\
    increase_or_saturate bf new_bf idx2
  )) = adjust_first_slot_lemma bf hash true;
  let bf0 = adjust_first_slot bf hash true in
  adjust_second_slot_lemma bf0 hash true;
  insert_hash_lemma1 bf hash;
  insert_hash_lemma2 bf hash

(**** Remove hash properties ****)

let remove_hash_prelim_lemma (bf: bloom_storage_u8) (idx: valid_index)
  : Lemma (requires (U8.v (slot_value bf idx) > 0 && U8.v (slot_value bf idx) < _MAX_U8))
    (ensures (U8.v (slot_value (adjust_slot bf idx false) idx) = U8.v (slot_value bf idx) - 1))
  = ()

let decrease_or_saturate (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8) (idx:valid_index) =
  if U8.v (slot_value old_bf idx) = _MAX_U8 then
    U8.v (slot_value new_bf idx) = _MAX_U8
  else if U8.v (slot_value old_bf idx) = 0 then
    U8.v (slot_value new_bf idx) = 0
  else
    U8.(slot_value new_bf idx <^ slot_value old_bf idx)

#reset-options "--z3rlimit 20"

let remove_hash_lemma1 (bf: bloom_storage_u8) (hash:u32)
  : Lemma (ensures (
    let new_bf = remove_hash bf hash in let idx1 = first_slot_index hash in
    if not (first_slot_is_empty bf hash) &&
      not (second_slot_is_empty (adjust_first_slot bf hash false) hash)
    then decrease_or_saturate bf new_bf idx1
    else slot_value bf idx1 = slot_value new_bf idx1
   ))
  = ()

let remove_hash_lemma2 (bf: bloom_storage_u8) (hash:u32)
  : Lemma (ensures (
    let new_bf = remove_hash bf hash in let idx2 = second_slot_index hash in
    if not (first_slot_is_empty bf hash) &&
      not (second_slot_is_empty (adjust_first_slot bf hash false) hash)
    then decrease_or_saturate bf new_bf idx2
    else slot_value bf idx2 = slot_value new_bf idx2
   ))
  = ()

let remove_hash_lemma
  (bf:bloom_storage_u8)
  (hash:u32)
  : Lemma (ensures (
    let new_bf = remove_hash bf hash in
    let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
    modified_hash_slots bf new_bf hash /\ begin
      if not (first_slot_is_empty bf hash) &&
      not (second_slot_is_empty (adjust_first_slot bf hash false) hash)
      then decrease_or_saturate bf new_bf idx1 /\ decrease_or_saturate bf new_bf idx2
      else (slot_value bf idx1 = slot_value new_bf idx1 /\
	slot_value bf idx2 = slot_value new_bf idx2)
    end
  )) =
  remove_hash_lemma1 bf hash;
  remove_hash_lemma2 bf hash;
  if (first_slot_is_empty bf hash) then () else
    let bf0 = adjust_first_slot bf hash false in
    adjust_first_slot_lemma bf hash false;
    if (second_slot_is_empty bf0 hash) then
      adjust_first_slot_lemma bf0 hash true
    else
      adjust_second_slot_lemma bf0 hash false

(**** Insert element properties ****)

let element_invalidation (bf: bloom_storage_u8) =
  (forall (e:element). (
    (not (might_contain_hash bf (hash e))) ==>
      (not (contains bf.ghost_state.elements e))
  ))

let count_invariant_property (bf:bloom_storage_u8) (e:element) : Tot bool =
  let hash_e = hash e in
  let val1 = slot_value bf (first_slot_index hash_e) in
  let val2 = slot_value bf (second_slot_index hash_e) in
  begin if U8.v val1 = _MAX_U8 then true else
    element_count bf.ghost_state.elements e <= U8.v val1
  end && begin if U8.v val2 = _MAX_U8 then true else
    element_count bf.ghost_state.elements e <= U8.v val2
  end

let count_invariant (bf:bloom_storage_u8) =
   (forall (e:element{contains bf.ghost_state.elements e}).
    count_invariant_property bf e)

let valid_bf (bf:bloom_storage_u8) = element_invalidation bf /\ count_invariant bf

let insert_element_lemma (bf:bloom_storage_u8) (e:element)
  : Lemma (requires (valid_bf bf)) (ensures (valid_bf (insert_element bf e)))
  = let new_bf = insert_element bf e in let hash_e = hash e in
  insert_hash_lemma bf hash_e;
  let forall_intro_lemma (e':element{contains new_bf.ghost_state.elements e'})
    : Lemma (ensures (count_invariant_property new_bf e')) =
    assert(count_invariant_property bf e')
  in Classical.forall_intro forall_intro_lemma

(**** Remove element properties ****)


let remove_element_lemma_element_invalidation (bf:bloom_storage_u8) (e:element)
  : Lemma(requires (valid_bf bf)) (ensures (element_invalidation (remove_element bf e))) =
 admit()
