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

let modified_only_one_slot
  (old_bf:bloom_storage_u8)
  (new_bf:bloom_storage_u8)
  (idx:valid_index) =
  forall (idx':valid_index{idx <> idx'}).
  slot_value new_bf idx' = slot_value old_bf idx'

let adjust_slot_lemma
  (bf:bloom_storage_u8)
  (idx:valid_index)
  (increment:bool{valid_incr bf idx increment})
  : Lemma (ensures (
    let new_bf = adjust_slot bf idx increment in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then
      not (slot_is_empty new_bf idx)
    else
      true
    end
  )) = ()

let adjust_first_slot_lemma
  (bf:bloom_storage_u8)
  (hash:u32)
  (increment:bool{valid_incr bf (first_slot_index hash) increment})
  : Lemma (ensures (
    let new_bf = adjust_first_slot bf hash increment in
    let idx = first_slot_index hash in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then
      not (slot_is_empty new_bf idx)
    else
      true
    end
  )) = adjust_slot_lemma bf (first_slot_index hash) increment

let adjust_second_slot_lemma
  (bf:bloom_storage_u8)
  (hash:u32)
  (increment:bool{valid_incr bf (second_slot_index hash) increment})
  : Lemma (ensures (
    let new_bf = adjust_second_slot bf hash increment in
    let idx = second_slot_index hash in
    modified_only_one_slot bf new_bf idx /\
    begin if increment then
      not (slot_is_empty new_bf idx)
    else
      true
    end
  )) = adjust_slot_lemma bf (second_slot_index hash) increment


let modified_hash_slots
  (old_bf:bloom_storage_u8)
  (new_bf:bloom_storage_u8)
  (hash:u32) =
  let idx1 = first_slot_index hash in
  let idx2 = second_slot_index hash in
  forall (idx':valid_index{idx' <> idx1 /\ idx' <> idx2}).
  slot_value new_bf idx' = slot_value old_bf idx'

let insert_hash_lemma
  (bf:bloom_storage_u8)
  (hash:u32)
  : Lemma (ensures (
    let new_bf = insert_hash bf hash in
    modified_hash_slots bf new_bf hash /\
    might_contain_hash new_bf hash
  )) =
    adjust_first_slot_lemma bf hash true;
    let bf0 = adjust_first_slot bf hash true in
    adjust_second_slot_lemma bf0 hash true

let remove_hash_lemma
  (bf:bloom_storage_u8)
  (hash:u32)
  : Lemma (ensures (
    let new_bf = remove_hash bf hash in
    modified_hash_slots bf new_bf hash
  )) =
  if (first_slot_is_empty bf hash) then () else
    let bf0 = adjust_first_slot bf hash false in
    adjust_first_slot_lemma bf hash false;
    if (second_slot_is_empty bf0 hash) then
      adjust_first_slot_lemma bf0 hash true
    else
      adjust_second_slot_lemma bf0 hash false

let add_only_bloom_filter
  (bf:bloom_storage_u8)
  : Tot bool =
  let elements = bf.ghost_state.elements in
  all_elements elements (fun e ->
    might_contain_hash bf (hash e)
  )


let element_invalidation (bf: bloom_storage_u8) =
  (forall (e:element). (
    (not (might_contain_hash bf (hash e))) ==>
      (not (contains bf.ghost_state.elements e))
  ))

let count_invariant_property (bf:bloom_storage_u8) (e:element) : Tot bool =
  let hash_e = hash e in
  let val1 = slot_value bf (first_slot_index hash_e) in
  let val2 = slot_value bf (second_slot_index hash_e) in
  begin if U8.v val1 < _MAX_U8 then true else
    element_count bf.ghost_state.elements e <= U8.v val1
  end && begin if U8.v val2 < _MAX_U8 then true else
    element_count bf.ghost_state.elements e <= U8.v val2
  end

let count_invariant (bf:bloom_storage_u8) : Tot bool =
  all_elements #element bf.ghost_state.elements (fun e ->
    count_invariant_property bf e
  )

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

let lemma_count_invariant (bf:bloom_storage_u8)
  : Lemma (ensures (count_invariant bf <==>
    (forall (e:element{contains bf.ghost_state.elements e}).
    count_invariant_property bf e)
  )) =
  all_elements_lemma #element bf.ghost_state.elements
   (fun e -> count_invariant_property bf e)

type valid_bloom_storage_u8 = bf:bloom_storage_u8{element_invalidation bf /\ count_invariant bf}

type add_only_bloom_storage_u8 = bf:valid_bloom_storage_u8{add_only_bloom_filter bf}

let lemma_insert_hash_prelim1 (bf: bloom_storage_u8) (idx: valid_index)
  : Lemma (requires (U8.v (slot_value bf idx) < _MAX_U8))
    (ensures (U8.v (slot_value (adjust_slot bf idx true) idx) = U8.v (slot_value bf idx) + 1))
  = ()

let lemma_insert_hash_prelim2 (bf: bloom_storage_u8) (idx: valid_index)
  : Lemma (requires (U8.v (slot_value bf idx) = _MAX_U8))
    (ensures (U8.v (slot_value (adjust_slot bf idx true) idx) = _MAX_U8))
  = ()

let lemma_insert_hash_non_saturating1 (bf: bloom_storage_u8) (hash:u32)
  : Lemma (requires (
      U8.v (slot_value bf (first_slot_index hash)) < _MAX_U8)
    )
    (ensures (
      U8.v (slot_value (insert_hash bf hash) (first_slot_index hash)) >
	U8.v (slot_value bf (first_slot_index hash))
    )) =
    let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
    lemma_insert_hash_prelim1 bf idx1;
    let bf0 = adjust_first_slot bf hash true in
    adjust_first_slot_lemma bf hash true; adjust_second_slot_lemma bf0 hash true;
    if idx1 = idx2 then begin
      if U8.v (slot_value bf0 idx1) = _MAX_U8 then
        lemma_insert_hash_prelim2 bf0 idx1
      else
        lemma_insert_hash_prelim1 bf0 idx1
    end else ()

let lemma_insert_hash_non_saturating2 (bf: bloom_storage_u8) (hash:u32)
  : Lemma (requires (
      U8.v (slot_value bf (second_slot_index hash)) < _MAX_U8)
    )
    (ensures (
      U8.v (slot_value (insert_hash bf hash) (second_slot_index hash)) >
	U8.v (slot_value bf (second_slot_index hash))
    )) =
    let idx1 = first_slot_index hash in let idx2 = second_slot_index hash in
    lemma_insert_hash_prelim1 bf idx2;
    let bf0 = adjust_first_slot bf hash true in
    adjust_first_slot_lemma bf hash true; adjust_second_slot_lemma bf0 hash true;
    if idx1 = idx2 then begin
      if U8.v (slot_value bf0 idx2) = _MAX_U8 then
        lemma_insert_hash_prelim2 bf0 idx1
      else
        lemma_insert_hash_prelim1 bf0 idx1
    end else ()

(*
 (* *) lemma_count_invariant bf;
  (* *) lemma_count_invariant new_bf;
  let inner_lemma
    (e':element{contains new_bf.ghost_state.elements e'})
    : Lemma (ensures (count_invariant_property new_bf e'))
  =
    let hash_e' = hash e' in
    let idx1_e = first_slot_index (hash e) in
    let idx1_e' = first_slot_index (hash e') in
    let idx2_e = second_slot_index (hash e) in
    let idx2_e' = second_slot_index (hash e') in
    let new_val1 = slot_value new_bf idx1_e' in
    let new_val2 = slot_value new_bf idx2_e'  in
    let old_val1 = slot_value bf idx1_e' in
    let old_val2 = slot_value bf idx2_e' in
    if U8.v old_val1 = _MAX_U8 then () else
    assert(U8.v old_val1 < _MAX_U8);
    begin if idx1_e' = idx1_e || idx1_e' = idx2_e then begin
      Classical.or_elim
        #(idx1_e' = idx1_e)
        #(idx1_e' = idx2_e)
        #(fun _ -> U8.(old_val1 <=^ new_val1))
        (fun _ ->
	  //admit();
	  lemma_insert_hash_prelim bf idx1_e;
	  admit()
	)
        (fun _ ->
	  admit();
	  lemma_insert_hash_prelim bf idx2_e;
	  admit()
	);
       admit()
    end else
      admit()
    end;
    admit()


(*
    begin if U8.v val1 < _MAX_U8 then () else
     begin if idx1_e' = idx1_e || idx1_e' = idx2_e then begin
       if U8.v (slot_value bf idx1_e') < _MAX_U8 then
         admit()
       else
         assert(U8.v (slot_value new_bf idx1_e') = _MAX_U8);
	 assert(U8.v val1 = _MAX_U8 /\ U8.v val1 < _MAX_U8);
	 lemma_contradiction new_bf e' val1;
	 admit()
       end else begin
         assert(slot_value bf idx1_e' = slot_value new_bf idx1_e');
	 assert(count_invariant_property bf e');
	 assert(element_count bf.ghost_state.elements e' <= U8.v val1)
       end
     end
     //assume(element_count new_bf.ghost_state.elements e' <= U8.v val1)
    end;
    begin if U8.v val2 < _MAX_U8 then () else
      assume(element_count new_bf.ghost_state.elements e' <= U8.v val2)
    end
 *)
  in
  (* *) Classical.forall_intro inner_lemma;
  (* *) lemma_add_only_bloom_filter bf;
  (* *) lemma_add_only_bloom_filter new_bf;
  *)
