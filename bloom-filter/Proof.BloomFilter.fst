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
  (increment:bool) : Lemma (ensures (
    let new_bf = adjust_slot bf idx increment in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then not (slot_is_empty new_bf idx) else true end
  )) = ()

let adjust_first_slot_lemma (bf:bloom_storage_u8) (hash:u32)
  (increment:bool) : Lemma (ensures (
    let new_bf = adjust_first_slot bf hash increment in
    let idx = first_slot_index hash in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then not (slot_is_empty new_bf idx) else true end
  )) = adjust_slot_lemma bf (first_slot_index hash) increment

let adjust_second_slot_lemma (bf:bloom_storage_u8) (hash:u32)
  (increment:bool) : Lemma (ensures (
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

let decrease_by
  (decr:u8) (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8) (idx:valid_index) =
      if U8.v (slot_value new_bf idx) = _MAX_U8 then
      U8.v (slot_value new_bf idx) = _MAX_U8
    else if U8.(slot_value old_bf idx <^ decr) then
      U8.v (slot_value new_bf idx) = _MAX_U8
    else
      slot_value new_bf idx = U8.(slot_value old_bf idx -^ decr)

let decrease_or_saturate
  (old_bf:bloom_storage_u8) (new_bf:bloom_storage_u8) (idx1 idx2:valid_index)
  =
  if idx1 = idx2 then decrease_by 2uy old_bf new_bf idx1 else
    decrease_by 1uy old_bf new_bf idx1 && decrease_by 1uy old_bf new_bf idx2

let underflow_lemma () : Lemma (ensures (U8.(v (0uy -%^ 1uy)) = _MAX_U8)) =
  assert_norm(U8.(v (0uy -%^ 1uy)) = _MAX_U8)

let remove_hash_prelim_lemma (bf:bloom_storage_u8) (idx:valid_index)
  : Lemma (ensures (decrease_by 1uy bf (adjust_slot bf idx false) idx)) =
  ()

let remove_hash_lemma (bf: bloom_storage_u8) (hash:u32)
  : Lemma (ensures (
    let new_bf = remove_hash bf hash in
    let idx1 = first_slot_index hash in
    let idx2 = second_slot_index hash in
    decrease_or_saturate bf new_bf idx1 idx2
   ))
  = underflow_lemma ();
  let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
  remove_hash_prelim_lemma bf idx1;
  let bf0 = adjust_slot bf idx1 false in
  remove_hash_prelim_lemma bf0 idx2

(**** Insert element properties ****)

let element_invalidation (bf: bloom_storage_u8) =
  (forall (e:element). (
    (not (might_contain_hash bf (hash e))) ==>
      (not (contains bf.ghost_state.elements e))
  ))

let all_elements_counts (bf:bloom_storage_u8) (idx:valid_index) : Tot count =
   List.Tot.Base.fold_left (fun (sum : count) ((e, count) : (element & count)) ->
     let sum = if first_slot_index (hash e) = idx then sum + count else sum in
     if second_slot_index (hash e) = idx then sum + count else sum
   ) 0 bf.ghost_state.elements

let count_invariant_property (bf:bloom_storage_u8) (e:element) : Tot bool =
  let hash_e = hash e in
  let idx1 = first_slot_index hash_e in let idx2 = second_slot_index hash_e in
  let val1 = slot_value bf idx1 in let val2 = slot_value bf idx2 in
  begin if U8.v val1 = _MAX_U8 then true else
    all_elements_counts bf idx1 = U8.v val1
  end && begin if U8.v val2 = _MAX_U8 then true else
    all_elements_counts bf idx2 = U8.v val2
  end

let count_invariant (bf:bloom_storage_u8) =
   (forall (e:element{contains bf.ghost_state.elements e}).
    count_invariant_property bf e)

let valid_bf (bf:bloom_storage_u8) = element_invalidation bf /\ count_invariant bf


let insert_element_lemma_count_invariant_prelim (bf:bloom_storage_u8) (e:element) (idx:valid_index)
  : Lemma (requires (all_elements_counts bf idx = U8.v (slot_value bf idx))) (ensures (
    let new_bf = insert_hash bf (hash e) in
    if U8.v (slot_value new_bf idx) = _MAX_U8 then true else
      all_elements_counts new_bf idx = U8.v (slot_value new_bf idx)
  )) = insert_hash_lemma bf (hash e);admit()

let insert_element_lemma_count_invariant (bf:bloom_storage_u8) (e:element)
  : Lemma (requires (valid_bf bf)) (ensures (valid_bf (insert_element bf e)))
  = let hash_e = hash e in let new_bf = insert_hash bf hash_e in
  insert_hash_lemma bf (hash e);
  let forall_intro_lemma (e':element{contains new_bf.ghost_state.elements e'})
    : Lemma (ensures (count_invariant_property new_bf e')) =
    assert(count_invariant_property bf e');
    let hash_e' = hash e' in
    let idx1_e' = first_slot_index hash_e' in let idx2_e' = second_slot_index hash_e' in
    begin if U8.v (slot_value bf idx1_e') = _MAX_U8 then
      assert(U8.v (slot_value new_bf idx1_e') = _MAX_U8)
    else
      insert_element_lemma_count_invariant_prelim bf e idx1_e'
    end;
     begin if U8.v (slot_value bf idx2_e') = _MAX_U8 then
      assert(U8.v (slot_value new_bf idx2_e') = _MAX_U8)
    else
      insert_element_lemma_count_invariant_prelim bf e idx2_e'
    end
  in Classical.forall_intro forall_intro_lemma

(**** Remove element properties ****)

let lemma1 (bf:bloom_storage_u8) (hash:u32) (idx:valid_index)
  : Lemma (requires (U8.(slot_value bf idx >^ 2uy)))
  (ensures (let new_bf = remove_hash bf hash in
    U8.(slot_value new_bf idx >^ 0uy)
  )) = remove_hash_lemma bf hash

let lemma2 (bf:bloom_storage_u8) (hash:u32) (idx:valid_index)
  : Lemma (requires (
    U8.(slot_value bf idx >^ 1uy) /\ first_slot_index hash <> second_slot_index hash
  )) (ensures (let new_bf = remove_hash bf hash in
    U8.(slot_value new_bf idx >^ 0uy)
  )) = remove_hash_lemma bf hash

let lemma3 (n:nat) : Lemma (requires (n <= 2 /\ n > 1)) (ensures (n = 2)) = ()

#reset-options "--z3rlimit 10"

let remove_element_lemma_element_invalidation
  (bf:bloom_storage_u8) (e:element{contains bf.ghost_state.elements e})
  : Lemma(requires (valid_bf bf)) (ensures (element_invalidation (remove_element bf e))) =
  let new_bf = remove_element bf e in let hash_e = hash e in
  let idx1_e = first_slot_index hash_e in let idx2_e = second_slot_index hash_e in
  let forall_intro_lemma (e':element{contains new_bf.ghost_state.elements e'})
    : Lemma (ensures (might_contain_hash new_bf (hash e'))) =
    let hash_e' = hash e' in if e <> e' then begin
      let idx1_e' = first_slot_index hash_e' in let idx2_e' = second_slot_index hash_e' in
      assert(contains bf.ghost_state.elements e');
      assert(might_contain_hash bf hash_e');
      assert(count_invariant_property bf e');
      let e'_count =  element_count bf.ghost_state.elements e' in
      if e'_count > 2 then begin
	lemma1 bf hash_e idx1_e';lemma1 bf hash_e idx2_e'
      end else if e'_count > 1 then
	if idx1_e = idx2_e then begin
	  lemma3 e'_count;assert(e'_count = 2);admit()
	end else (lemma2 bf hash_e idx1_e';lemma2 bf hash_e idx2_e')
      else begin
        //assert(e'_count = 1);
        admit()
      end
    end else begin
      assert(e = e');
      admit()
    end
  in
  Classical.forall_intro forall_intro_lemma
