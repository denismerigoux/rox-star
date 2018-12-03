module Spec.BloomFilter

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

open Rust
open FStar.List.Tot.Base

assume type element: eqtype

assume val hash: element -> u32

type count = n:nat

let contains (#a:eqtype) (l:list (a & count)) (e:a) : Tot bool =
  existsb (fun (e', _) -> e = e') l

let rec no_duplicates (#a:eqtype) (l:list (a & count)) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | (e, _)::tl -> not (contains tl e) && no_duplicates tl

type count_list (a:eqtype) = (l:list (a & count){no_duplicates l})

let same_elements (#a: eqtype) (l1 l2: count_list a) =
  (forall (e:a). contains l1 e <==> contains l2 e)

val incr_count:
  #a:eqtype ->
  l:count_list a ->
  e : a{contains l e} ->
  Tot (l':count_list a{same_elements l l'}) (decreases l)
let rec incr_count #a l e =
  match l with
  | [] -> l
  | (e', old_count)::tl ->
    if e = e' then
      (e', old_count + 1)::tl
    else
      (e', old_count)::(incr_count tl e)

val element_count: #a:eqtype ->
  l:count_list a ->
  e: a ->
  Tot count (decreases l)
let rec element_count #a l e = match l with
  | [] -> 0
  | (e', count)::tl ->
    if e = e' then count else element_count tl e

val decr_count:
  #a:eqtype ->
  l:count_list a ->
  e : a{contains l e} ->
  Tot (l':count_list a{
      same_elements l l'
  }) (decreases l)
let rec decr_count #a l e =
  match l with
  | [] -> l
  | (e', old_count)::tl ->
    if e = e' then
      if old_count = 0 then
      (* We saturate at 0 *)
        (e', old_count)::tl
      else
        (e', old_count - 1)::tl
    else
      (e', old_count)::(decr_count tl e)

type spec_bloom_storage_u8 = {
   elements: (l:(count_list element){no_duplicates l})
}

let rec all_elements
  (#a:eqtype)
  (l:count_list a)
  (f:a -> bool)
  : Tot (b:bool) (decreases l) =
  match l with
  | [] -> true
  | (hd,_)::tl -> if f hd then all_elements tl f else false

let rec all_elements_lemma1
  (#a:eqtype)
  (l: count_list a)
  (f:a -> bool)
  : Lemma (ensures (
    all_elements #a l f ==>
      (forall (e:a{contains l e}). f e)
    )) (decreases l)
  =
  if not (all_elements #a l f) then () else
  match l with
  | [] -> ()
  | (e_hd,_)::tl ->
    assert (not (contains tl e_hd));
    if not (f e_hd) then assert(false) else begin
      let inner_lemma
	(e:a{contains l e})
	: Lemma (ensures (f e)) =
	assert (e = e_hd \/ contains tl e);
	Classical.or_elim
	  #(e = e_hd)
	  #(contains tl e)
	  #(fun _ -> f e)
	  (fun _ -> assert (e = e_hd))
	  (fun _ -> assert (contains tl e);
	    all_elements_lemma1 #a tl f
	  )
      in
      Classical.forall_intro inner_lemma
    end

let rec all_elements_lemma2
  (#a:eqtype)
  (l: count_list a)
  (f:a -> bool)
  : Lemma (ensures (
    (forall (e:a{contains l e}). f e) ==>
      all_elements #a l f
    )) (decreases l)
  =
  let rec inner_lemma
    (_ : (forall (e:a{contains l e}). f e))
    : Lemma (ensures (all_elements #a l f))
    = match l with
    | [] -> ()
    | (hd, _)::tl -> all_elements_lemma2 #a tl f
  in
  Classical.impl_intro
    #((forall (e:a{contains l e}). f e))
    #(all_elements #a l f)
    inner_lemma


let rec all_elements_lemma
  (#a:eqtype)
  (l: count_list a)
  (f:a -> bool)
  : Lemma (ensures (
    all_elements #a l f <==>
      (forall (e:a{contains l e}). f e)
    )) (decreases l)
  =
  all_elements_lemma1 #a l f;
  all_elements_lemma2 #a l f

val spec_insert_element:
  bf:spec_bloom_storage_u8 ->
  e:element ->
  Tot spec_bloom_storage_u8
let spec_insert_element bf e =
  if contains bf.elements e then
    { bf with elements = incr_count bf.elements e }
  else
    { bf with elements = (e,1)::bf.elements }

let lemma_spec_insert_element
  (bf:spec_bloom_storage_u8)
  (e:element)
  : Lemma (ensures (
    let new_bf = spec_insert_element bf e in
    (forall(e':element{e' <> e}).
      (contains bf.elements e' <==> contains new_bf.elements e'))
    /\ contains new_bf.elements e
  )) =
  ()


val spec_remove_element:
  bf:spec_bloom_storage_u8 ->
  e:element ->
  Tot spec_bloom_storage_u8
let spec_remove_element bf e =
  if contains bf.elements e  then
    { bf with elements = decr_count bf.elements e }
  else
    bf

let lemma_spec_remove_element
  (bf:spec_bloom_storage_u8)
  (e:element)
  : Lemma (ensures (
    let new_bf = spec_remove_element bf e in
    same_elements bf.elements new_bf.elements
  )) =
  ()
