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
 slot_value bf idx = _MAX_U8

let is_almost_max (bf:bloom_storage_u8) (idx:valid_index) : Tot bool =
  slot_value bf idx = U8.(_MAX_U8 -^ 1uy)

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

let element_invalidation (bf: bloom_filter) (e:element) =
  not (might_contain_hash bf.storage (hash e)) ==> not (contains bf.ghost_state.elements e)

#reset-options "--max_fuel 1"

let rec compute_count_sum (idx:valid_index) (l:count_list element) : Tot count (decreases l) =
   match l with
   | [] -> 0
   | (e, count)::tl ->
     let sum = compute_count_sum idx tl in
     let sum = if first_slot_index (hash e) = idx then sum + count else sum in
     if second_slot_index (hash e) = idx then sum + count else sum

let all_elements_counts (bf:bloom_filter) (idx:valid_index) : Tot count =
   compute_count_sum idx bf.ghost_state.elements

#reset-options "--max_fuel 0"

let count_invariant_property (bf:bloom_filter) (idx:valid_index) : Tot bool =
  if is_max bf.storage idx then true else
    all_elements_counts bf idx = U8.v (slot_value bf.storage idx)

let count_invariant (bf:bloom_filter) (idx:valid_index) =
    count_invariant_property bf idx

#reset-options "--max_fuel 1 --z3rlimit 20"

let rec count_sum_component_lemma1 (l:count_list element) (e':element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e') in let idx2 = second_slot_index (hash e') in
    idx = idx1 \/ idx = idx2
  )) (ensures (compute_count_sum idx l >= element_count l e')) = match l with
  | [] -> ()
  | (e'', count)::tl -> count_sum_component_lemma1 tl e' idx

let rec count_sum_component_lemma2 (l:count_list element) (idx:valid_index)
  : Lemma (requires (compute_count_sum idx l > 0))
    (ensures (exists (e:element).
      (idx = first_slot_index (hash e) \/ idx = second_slot_index (hash e)) /\
      element_count l e > 0
    ))
  =  match l with
  | [] -> ()
  | (e, count)::tl ->
    if (idx = first_slot_index (hash e) || idx = second_slot_index (hash e)) && count > 0 then
      ()
    else count_sum_component_lemma2 tl idx

let hash_collision (bf: bloom_filter) (e:element) =
  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  might_contain_hash bf.storage (hash e) ==> (contains bf.ghost_state.elements e \/
    (is_max bf.storage idx1 \/ is_max bf.storage idx2) \/
    (exists (e':element{e' <> e}).
      let idx1' = first_slot_index (hash e') in let idx2' = second_slot_index (hash e') in
      (idx1 = idx1' \/ idx1 = idx2' \/ idx2 = idx1' \/ idx2 = idx2'))
  )

(**** New bloom filter properties *)

(***** Element invalidation *)

let new_bf_element_invalidation_lemma (e':element)
  : Lemma (ensures (element_invalidation (new_bloom_filter ()) e'))
  = ()

(***** Count invariant *)

let new_bf_count_invariant_lemma (idx:valid_index)
  : Lemma (ensures (count_invariant_property (new_bloom_filter ()) idx))
  = ()

(***** Hash collision *)

let new_bf_hash_collision_lemma (e:element)
  : Lemma (ensures (hash_collision (new_bloom_filter ()) e))
  = ()

(**** Insert element properties *)

(***** Element invalidation *)

let insert_element_element_invalidation_lemma (bf:bloom_filter) (e:element) (e':element)
  : Lemma (requires (element_invalidation bf e'))
    (ensures (element_invalidation (insert_element bf e) e'))
  = let new_bf = insert_element bf e in
  if contains new_bf.ghost_state.elements e' then
       if e <> e' then () else ()
  else ()


(***** Count invariant *)

let rec insert_element_compute_count_sum_lemma1 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx1 <> idx2 /\ (idx = idx1 \/ idx = idx2)
  ))
  (ensures (let new_bf = spec_insert_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l + 1
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> insert_element_compute_count_sum_lemma1 tl e idx

let insert_element_all_elements_counts_lemma1 (bf:bloom_filter) (e:element)
  : Lemma (requires (first_slot_index (hash e) <> second_slot_index (hash e)))
    (ensures (let new_bf = insert_element bf e in
       let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
       all_elements_counts new_bf idx1 = all_elements_counts bf idx1 + 1 &&
       all_elements_counts new_bf idx2 = all_elements_counts bf idx2 + 1
    ))
  =  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  insert_element_compute_count_sum_lemma1 bf.ghost_state.elements e idx1;
  insert_element_compute_count_sum_lemma1 bf.ghost_state.elements e idx2

let rec insert_element_compute_count_sum_lemma2 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx1 = idx2 /\ idx = idx1
  ))
  (ensures (let new_bf = spec_insert_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l + 2
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> insert_element_compute_count_sum_lemma2 tl e idx

let insert_element_all_elements_counts_lemma2 (bf:bloom_filter) (e:element)
  : Lemma (requires (first_slot_index (hash e) = second_slot_index (hash e)))
    (ensures (let new_bf = insert_element bf e in
       let idx = first_slot_index (hash e) in
       all_elements_counts new_bf idx = all_elements_counts bf idx + 2
    ))
  = insert_element_compute_count_sum_lemma2 bf.ghost_state.elements e (first_slot_index (hash e))

let rec insert_element_compute_count_sum_lemma3 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx <> idx1 /\ idx <> idx2
  ))
  (ensures (let new_bf = spec_insert_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> insert_element_compute_count_sum_lemma3 tl e idx

let insert_element_all_elements_counts_lemma3 (bf:bloom_filter) (e:element) (idx:valid_index)
  : Lemma (requires (
      let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
      idx <> idx1 /\ idx <> idx2
    )) (ensures (let new_bf = insert_element bf e in
      all_elements_counts new_bf idx = all_elements_counts bf idx
    ))
  = insert_element_compute_count_sum_lemma3 bf.ghost_state.elements e idx

let insert_element_count_invariant_lemma_prelim
  (bf:bloom_filter) (e:element) (idx:valid_index)
  : Lemma (requires (not (is_max bf.storage idx) /\
    all_elements_counts bf idx = U8.v (slot_value bf.storage idx)))
    (ensures (let new_bf = insert_element bf e in
      not (is_max new_bf.storage idx) ==>
      all_elements_counts new_bf idx = U8.v (slot_value new_bf.storage idx)
    ))
  = insert_hash_lemma bf.storage (hash e) idx;
  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  let new_bf = insert_element bf e in
  if idx1 <> idx2 then
    if idx = idx1 || idx = idx2 then
      if is_max new_bf.storage idx then () else insert_element_all_elements_counts_lemma1 bf e
    else insert_element_all_elements_counts_lemma3 bf e idx
  else if idx = idx1 then
      if is_almost_max bf.storage idx1 then ()
      else insert_element_all_elements_counts_lemma2 bf e
  else insert_element_all_elements_counts_lemma3 bf e idx

let insert_element_count_invariant_lemma (bf:bloom_filter) (e:element) (idx:valid_index)
  : Lemma (requires (count_invariant bf idx))
    (ensures (count_invariant (insert_element bf e) idx))
  = if is_max bf.storage idx then () else insert_element_count_invariant_lemma_prelim bf e idx

(***** Hash collision *)

let insert_element_hash_collision_lemma (bf:bloom_filter) (e e':element)
  : Lemma (requires (hash_collision bf e')) (ensures (hash_collision (insert_element bf e) e'))
  = ()

(**** Remove element properties *)

(***** Count invariant *)

let rec remove_element_compute_count_sum_lemma1 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx1 <> idx2 /\ (idx = idx1 \/ idx = idx2) /\ contains l e
  ))
  (ensures (let new_bf = spec_remove_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l - 1
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> if e = e' then () else remove_element_compute_count_sum_lemma1 tl e idx

let remove_element_all_elements_counts_lemma1 (bf:bloom_filter) (e:element)
  : Lemma (requires (
    first_slot_index (hash e) <> second_slot_index (hash e) /\ contains bf.ghost_state.elements e
  )) (ensures (let new_bf = remove_element bf e in
       let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
       all_elements_counts new_bf idx1 = all_elements_counts bf idx1 - 1 &&
       all_elements_counts new_bf idx2 = all_elements_counts bf idx2 - 1
    ))
  =  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  remove_element_compute_count_sum_lemma1 bf.ghost_state.elements e idx1;
  remove_element_compute_count_sum_lemma1 bf.ghost_state.elements e idx2

let rec remove_element_compute_count_sum_lemma2 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx1 = idx2 /\ idx = idx1 /\ contains l e
  ))
  (ensures (let new_bf = spec_remove_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l - 2
  )) (decreases l) = if not (contains l e ) then () else match l with
  | [] -> ()
  | (e', count)::tl -> if e' = e then () else remove_element_compute_count_sum_lemma2 tl e idx

let remove_element_all_elements_counts_lemma2 (bf:bloom_filter) (e:element)
  : Lemma (requires (
    first_slot_index (hash e) = second_slot_index (hash e) /\ contains bf.ghost_state.elements e
  )) (ensures (let new_bf = remove_element bf e in let idx = first_slot_index (hash e) in
       all_elements_counts new_bf idx = all_elements_counts bf idx - 2
    ))
  = remove_element_compute_count_sum_lemma2 bf.ghost_state.elements e (first_slot_index (hash e))

let rec remove_element_compute_count_sum_lemma3 (l:count_list element) (e:element) (idx:valid_index)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    idx <> idx1 /\ idx <> idx2 /\ contains l e
  ))
  (ensures (let new_bf = spec_remove_element ({elements = l}) e in
    compute_count_sum idx new_bf.elements = compute_count_sum idx l
  )) (decreases l) = match l with
  | [] -> ()
  | (e', count)::tl -> if e = e' then () else remove_element_compute_count_sum_lemma3 tl e idx

let remove_element_all_elements_counts_lemma3 (bf:bloom_filter) (e:element) (idx:valid_index)
  : Lemma (requires (
      let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
      idx <> idx1 /\ idx <> idx2 /\ contains bf.ghost_state.elements e
    )) (ensures (let new_bf = remove_element bf e in
      all_elements_counts new_bf idx = all_elements_counts bf idx
    ))
  = remove_element_compute_count_sum_lemma3 bf.ghost_state.elements e idx

#reset-options "--max_fuel 0 --z3rlimit 40"

let remove_element_count_invariant_lemma_prelim
  (bf:bloom_filter) (e:element) (idx:valid_index)
  : Lemma (requires (
      not (is_max bf.storage idx) /\ all_elements_counts bf idx = U8.v (slot_value bf.storage idx) /\
      contains bf.ghost_state.elements e
    ))
    (ensures (let new_bf = remove_element bf e in
      not (is_max new_bf.storage idx) ==>
      all_elements_counts new_bf idx = U8.v (slot_value new_bf.storage idx)
    ))
  = insert_hash_lemma bf.storage (hash e) idx;
   let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
   let new_bf = remove_element bf e in
   if idx1 <> idx2 then
    if idx = idx1 || idx = idx2 then
      if slot_is_empty bf.storage idx then ()
      else if is_max bf.storage idx then ()
      else remove_element_all_elements_counts_lemma1 bf e
    else remove_element_all_elements_counts_lemma3 bf e idx
  else if idx = idx1 then
      if slot_is_empty bf.storage idx1 then ()
      else if is_almost_min bf.storage idx1 then ()
      else remove_element_all_elements_counts_lemma2 bf e
  else remove_element_all_elements_counts_lemma3 bf e idx

#reset-options "--z3rlimit 5"

let remove_element_count_invariant_lemma (bf:bloom_filter) (e:element) (idx:valid_index)
  : Lemma (requires (contains bf.ghost_state.elements e /\ count_invariant bf idx))
    (ensures (let new_bf = remove_element bf e in count_invariant new_bf idx))
  = if is_max bf.storage idx then () else remove_element_count_invariant_lemma_prelim bf e idx

(***** Element invalidation *)

#reset-options "--max_fuel 1"

let rec remove_element_same_count_lemma (bf:bloom_filter) (e e':element)
  : Lemma (requires (e <> e' /\ contains bf.ghost_state.elements e))
  (ensures (let new_bf = remove_element bf e in
    element_count bf.ghost_state.elements e' = element_count new_bf.ghost_state.elements e'
  )) (decreases bf.ghost_state.elements)
  = match bf.ghost_state.elements with
  | [] -> ()
  | (e'', old_count)::tl ->  if e'' = e then () else remove_element_same_count_lemma
    ({bf with  ghost_state = { bf.ghost_state with elements = tl} }) e e'

#reset-options "--max_fuel 0"

let remove_element_element_invalidation_prelim_lemma1
  (bf:bloom_filter) (e e':element) (idx:valid_index)
  : Lemma (requires (
    (idx = first_slot_index (hash e') \/ idx = second_slot_index (hash e')) /\
    contains bf.ghost_state.elements e /\ contains bf.ghost_state.elements e' /\
    e <> e' /\ count_invariant bf idx /\ U8.(slot_value bf.storage idx >^ 0uy)
  )) (ensures (
    let new_bf = remove_element bf e in U8.(slot_value new_bf.storage idx >^ 0uy)
  )) =  let new_bf = remove_element bf e in
  remove_element_count_invariant_lemma bf e idx;
  count_sum_component_lemma1 bf.ghost_state.elements e' idx;
  remove_element_same_count_lemma bf e e';
  count_sum_component_lemma1 new_bf.ghost_state.elements e' idx

let remove_element_element_invalidation_prelim_lemma2 (bf:bloom_filter) (e:element)
  : Lemma (requires (
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    element_count bf.ghost_state.elements e > 1 /\ count_invariant bf idx1 /\
    count_invariant bf idx2
  )) (ensures (let new_bf = remove_element bf e in
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    U8.(slot_value new_bf.storage idx1 >^ 0uy) /\ U8.(slot_value new_bf.storage idx2 >^ 0uy)
  )) = let new_bf = remove_element bf e in
  let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
  remove_element_count_invariant_lemma bf e idx1;remove_element_count_invariant_lemma bf e idx2;
  count_sum_component_lemma1 new_bf.ghost_state.elements e idx1;
  count_sum_component_lemma1 new_bf.ghost_state.elements e idx2

let remove_element_element_invalidation_lemma (bf:bloom_filter) (e e':element)
  : Lemma (requires (
    element_invalidation bf e' /\ count_invariant bf (first_slot_index (hash e')) /\
    count_invariant bf (second_slot_index (hash e')) /\ contains bf.ghost_state.elements e
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

(***** Hash collision *)

#reset-options "--z3rlimit 20"

let remove_element_hash_collision_prelim_lemma1 (bf:bloom_filter) (e:element) (idx:valid_index)
  : Lemma (requires (
    (idx = first_slot_index (hash e) \/ idx = second_slot_index (hash e)) /\
    U8.(slot_value bf.storage idx >^ 0uy) /\ not (is_max bf.storage idx) /\
    count_invariant bf idx /\
    not (contains bf.ghost_state.elements e)
  )) (ensures (exists (e':element{e' <> e}).
    let idx1' = first_slot_index (hash e') in let idx2' = second_slot_index (hash e') in
    idx = idx1' \/ idx = idx2'
  )) = count_sum_component_lemma2 bf.ghost_state.elements idx

let remove_element_hash_collision_lemma (bf:bloom_filter) (e e':element)
  : Lemma (requires (count_invariant bf (first_slot_index (hash e')) /\
    count_invariant bf (second_slot_index (hash e')) /\ hash_collision bf e' /\
    contains bf.ghost_state.elements e))
    (ensures (hash_collision (remove_element bf e) e'))
  = let new_bf = remove_element bf e in
  if not (might_contain_hash new_bf.storage (hash e')) then () else
    let idx1 = first_slot_index (hash e) in let idx2 = second_slot_index (hash e) in
    let idx1' = first_slot_index (hash e') in let idx2' = second_slot_index (hash e') in
    assert (
      U8.(slot_value new_bf.storage idx1' >^ 0uy) \/ U8.(slot_value new_bf.storage idx2' >^ 0uy)
    );
    if contains new_bf.ghost_state.elements e' then () else
    if U8.(slot_value new_bf.storage idx1' >^ 0uy) then
      if is_max new_bf.storage idx1' then () else begin
      remove_element_count_invariant_lemma bf e idx1';
      remove_element_hash_collision_prelim_lemma1 new_bf e' idx1'
    end else if U8.(slot_value new_bf.storage idx2' >^ 0uy) then
      if is_max new_bf.storage idx2' then () else begin
      remove_element_count_invariant_lemma bf e idx2';
      remove_element_hash_collision_prelim_lemma1 new_bf e' idx2'
    end else ()

#reset-options "--z3rlimit 5"

(**** Final displayable properties *)

(*
  This is the full invariant that is preserved by each function manipulating the bloom filter.
  It specifies what means the value returned by might_contain_hash. If it returns no, that means
  the element is truly not contained in the bloom filter. If it returns yes, then three cases arise:
    - either the bloom filter truly contains the element;
    - either one of the slot indexes corresponding to the element's hash have been saturated;
    - or there exists a hash collision with another element.
  The third component of the invariant is a deep specification of the link between the values of
  the slots of the arrays and the number of times you've inserted the corresponding elements in the
  bloom filter. It is not directly useful from a client's perspective but necessary for the proof.
*)
let valid_bf (bf:bloom_filter) = (forall (e':element). element_invalidation bf e') /\
  (forall (e':element). hash_collision bf e') /\
  (forall (idx:valid_index). count_invariant_property bf idx)

let new_bf_correctness () : Lemma (ensures (valid_bf (new_bloom_filter ()))) =
  let new_bf = new_bloom_filter () in
  let f (idx:valid_index) : Lemma (ensures (count_invariant new_bf idx)) =
    new_bf_count_invariant_lemma idx
  in Classical.forall_intro f;
  let g (e':element) : Lemma (ensures (element_invalidation new_bf e')) =
    new_bf_element_invalidation_lemma e'
  in Classical.forall_intro g;
  let h (e':element) : Lemma (ensures (hash_collision new_bf e')) =
    new_bf_hash_collision_lemma e'
  in Classical.forall_intro h

let insert_element_corectness (bf:bloom_filter) (e:element)
  : Lemma (requires (valid_bf bf)) (ensures (valid_bf (insert_element bf e))) =
  let new_bf = insert_element bf e in
  let f (idx:valid_index) : Lemma (ensures (count_invariant new_bf idx)) =
    insert_element_count_invariant_lemma bf e idx
  in Classical.forall_intro f;
  let g (e':element) : Lemma (ensures (element_invalidation new_bf e')) =
    insert_element_element_invalidation_lemma bf e e'
  in Classical.forall_intro g;
  let h (e':element) : Lemma (ensures (hash_collision new_bf e')) =
    insert_element_hash_collision_lemma bf e e'
  in Classical.forall_intro h

let remove_element_corectness (bf:bloom_filter) (e:element)
  : Lemma (requires (valid_bf bf /\ contains bf.ghost_state.elements e))
    (ensures (valid_bf (remove_element bf e))) =
  let new_bf = remove_element bf e in
  let f (idx:valid_index) : Lemma (ensures (count_invariant new_bf idx)) =
    remove_element_count_invariant_lemma bf e idx
  in Classical.forall_intro f;
  let g (e':element) : Lemma (ensures (element_invalidation new_bf e')) =
    remove_element_element_invalidation_lemma bf e e'
  in Classical.forall_intro g;
  let h (e':element) : Lemma (ensures (hash_collision new_bf e')) =
    remove_element_hash_collision_lemma bf e e'
  in Classical.forall_intro h
