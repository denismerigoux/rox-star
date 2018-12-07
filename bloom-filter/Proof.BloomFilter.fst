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

(**** Adjust slot properties *)

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

(**** Insert hash properties *)

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

(**** Remove hash properties *)

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

(**** Invariants *)

let element_invalidation (bf: bloom_storage_u8) (e:element) =
  not (might_contain_hash bf (hash e)) ==> not (contains bf.ghost_state.elements e)

#reset-options "--max_fuel 1"

let rec compute_count_sum (idx:valid_index) (l:count_list element) : Tot count (decreases l) =
   match l with
   | [] -> 0
   | (e, count)::tl ->
     let sum = compute_count_sum idx tl in
     let sum = if first_slot_index (hash e) = idx then sum + count else sum in
     if second_slot_index (hash e) = idx then sum + count else sum

let all_elements_counts (bf:bloom_storage_u8) (idx:valid_index) : Tot count =
   compute_count_sum idx bf.ghost_state.elements

#reset-options "--max_fuel 0"

let count_invariant_property (bf:bloom_storage_u8) (idx:valid_index) : Tot bool =
  if is_max bf idx then true else
    all_elements_counts bf idx = U8.v (slot_value bf idx)

let count_invariant (bf:bloom_storage_u8) (idx:valid_index) =
    count_invariant_property bf idx

(**** Insert element properties *)

(***** Element invalidation *)

#reset-options "--max_fuel 1 --z3rlimit 20"

let insert_element_element_invalidation_lemma (bf:bloom_storage_u8) (e:element) (e':element)
  : Lemma (requires (element_invalidation bf e'))
    (ensures (element_invalidation (insert_element bf e) e'))
  = ()

(***** Count invariant *)

let rec compute_count_sum_lemma1 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx1 <> idx2 /\ (idx = idx1 \/ idx = idx2)
  ))
  (ensures (let new_bf = spec_insert_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l + 1
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> compute_count_sum_lemma1 tl e idx

let insert_element_all_elements_counts_lemma1 (bf:bloom_storage_u8) (e:element)
  : Lemma (requires (first_slot_index (hash e) <> second_slot_index (hash e)))
    (ensures (let new_bf = insert_element bf e in
       let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
       all_elements_counts new_bf idx1 = all_elements_counts bf idx1 + 1 &&
       all_elements_counts new_bf idx2 = all_elements_counts bf idx2 + 1
    ))
  =  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  compute_count_sum_lemma1 bf.ghost_state.elements e idx1;
  compute_count_sum_lemma1 bf.ghost_state.elements e idx2

let rec compute_count_sum_lemma2 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx1 = idx2 /\ idx = idx1
  ))
  (ensures (let new_bf = spec_insert_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l + 2
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> compute_count_sum_lemma2 tl e idx

let insert_element_all_elements_counts_lemma2 (bf:bloom_storage_u8) (e:element)
  : Lemma (requires (first_slot_index (hash e) = second_slot_index (hash e)))
    (ensures (let new_bf = insert_element bf e in
       let idx = first_slot_index (hash e) in
       all_elements_counts new_bf idx = all_elements_counts bf idx + 2
    ))
  = compute_count_sum_lemma2 bf.ghost_state.elements e (first_slot_index (hash e))

let rec compute_count_sum_lemma3 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx <> idx1 /\ idx <> idx2
  ))
  (ensures (let new_bf = spec_insert_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> compute_count_sum_lemma3 tl e idx

let insert_element_all_elements_counts_lemma3 (bf:bloom_storage_u8) (e:element) (idx:valid_index)
  : Lemma (requires (
      let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
      idx <> idx1 /\ idx <> idx2
    )) (ensures (let new_bf = insert_element bf e in
      all_elements_counts new_bf idx = all_elements_counts bf idx
    ))
  = compute_count_sum_lemma3 bf.ghost_state.elements e idx

let insert_element_count_invariant_lemma_prelim
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
    else insert_element_all_elements_counts_lemma3 bf e idx
  else if idx = idx1 then
      if is_almost_max bf idx1 then ()
      else insert_element_all_elements_counts_lemma2 bf e
  else insert_element_all_elements_counts_lemma3 bf e idx

let insert_element_count_invariant_lemma (bf:bloom_storage_u8) (e:element) (idx:valid_index)
  : Lemma (requires (count_invariant bf idx))
    (ensures (count_invariant (insert_element bf e) idx))
  = if is_max bf idx then () else insert_element_count_invariant_lemma_prelim bf e idx

(**** Remove element properties *)

(***** Count invariant *)

let remove_element_count_invariant_lemma_prelim
  (bf:bloom_storage_u8) (e:element) (idx:valid_index)
  : Lemma (requires (not (is_max bf idx) /\ all_elements_counts bf idx = U8.v (slot_value bf idx)))
    (ensures (let new_bf = remove_element bf e in
      not (is_max new_bf idx) ==> all_elements_counts new_bf idx = U8.v (slot_value new_bf idx)
    ))
  = insert_hash_lemma bf (hash e) idx;
  admit()

let remove_element_count_invariant_lemma (bf:bloom_storage_u8) (e:element) (idx:valid_index)
  : Lemma (requires (count_invariant bf idx)) (ensures (let new_bf = remove_element bf e in
    count_invariant new_bf idx)) = admit()

(***** Element invalidation *)

let rec compute_sum_lemma4 (l:count_list element) (e':element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e') in let idx2 = second_slot_index (hash e') in
    idx = idx1 \/ idx = idx2
  )) (ensures (compute_count_sum idx l >= element_count l e')) = match l with
  | [] -> ()
  | (e'', count)::tl -> compute_sum_lemma4 tl e' idx

let rec remove_element_same_count_lemma (bf:bloom_storage_u8) (e e':element) : Lemma (requires (e <> e'))
  (ensures (let new_bf = remove_element bf e in
    element_count bf.ghost_state.elements e' = element_count new_bf.ghost_state.elements e'
  )) (decreases bf.ghost_state.elements)
  = match bf.ghost_state.elements with
  | [] -> ()
  | (e'', old_count)::tl ->  remove_element_same_count_lemma
    ({bf with  ghost_state = { bf.ghost_state with elements = tl} }) e e'


let remove_element_element_invalidation_prelim_lemma1
  (bf:bloom_storage_u8) (e e':element) (idx:valid_index)
  : Lemma (requires (
    (idx = first_slot_index (hash e') \/ idx = second_slot_index (hash e')) /\
    element_count bf.ghost_state.elements e' > 0 /\ e <> e' /\
    count_invariant bf idx /\ U8.(slot_value bf idx >^ 0uy)
  )) (ensures (
    let new_bf = remove_element bf e in U8.(slot_value new_bf idx >^ 0uy)
  )) =  let new_bf = remove_element bf e in
  remove_element_count_invariant_lemma bf e idx;
  compute_sum_lemma4 bf.ghost_state.elements e' idx;
  remove_element_same_count_lemma bf e e';
  compute_sum_lemma4 new_bf.ghost_state.elements e' idx

let remove_element_element_invalidation_prelim_lemma2 (bf:bloom_storage_u8) (e:element)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    element_count bf.ghost_state.elements e > 1 /\ count_invariant bf idx1 /\
    count_invariant bf idx2
  )) (ensures (let new_bf = remove_element bf e in
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    U8.(slot_value new_bf idx1 >^ 0uy) /\ U8.(slot_value new_bf idx2 >^ 0uy)
  )) = let new_bf = remove_element bf e in
  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  remove_element_count_invariant_lemma bf e idx1;remove_element_count_invariant_lemma bf e idx2;
  compute_sum_lemma4 new_bf.ghost_state.elements e idx1;
  compute_sum_lemma4 new_bf.ghost_state.elements e idx2

let remove_element_element_invalidation_lemma (bf:bloom_storage_u8) (e e':element)
  : Lemma (requires (
    element_invalidation bf e' /\ count_invariant bf (first_slot_index (hash e')) /\
    count_invariant bf (second_slot_index (hash e'))
  ))
  (ensures (element_invalidation (remove_element bf e) e')) =
  let new_bf = remove_element bf e in
  if contains new_bf.ghost_state.elements e' then begin
    if e <> e' then begin
      let idx1 = first_slot_index (hash e') in let idx2 = second_slot_index (hash e') in
      remove_element_element_invalidation_prelim_lemma1 bf e e' idx1;
      remove_element_element_invalidation_prelim_lemma1 bf e e' idx2
    end else if element_count bf.ghost_state.elements e > 1 then begin
      remove_element_element_invalidation_prelim_lemma2 bf e
    end else ()
  end else ()
