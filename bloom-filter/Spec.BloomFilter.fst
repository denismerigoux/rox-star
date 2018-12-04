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
  existsb (fun ((e', n) : a & count) -> e = e' && n > 0) l

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

let same_elements_except (#a:eqtype) (l1 l2: count_list a) (e:a) =
   (forall (e':a{e' <> e}). contains l1 e' <==> contains l2 e')

val decr_count:
  #a:eqtype ->
  l:count_list a ->
  e : a{contains l e} ->
  Tot (l':count_list a{
      if element_count l e > 1 then
        same_elements l l'
      else
        same_elements_except l l' e /\ not (contains l' e)
  }) (decreases l)
let rec decr_count #a l e =
  match l with
  | [] -> l
  | (e', old_count)::tl ->
    if e = e' then
      (e', old_count - 1)::tl
    else
      (e', old_count)::(decr_count tl e)

type spec_bloom_storage_u8 = {
   elements: (l:(count_list element){no_duplicates l})
}

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
  e:element{contains bf.elements e} ->
  Tot spec_bloom_storage_u8
let spec_remove_element bf e =
    { bf with elements = decr_count bf.elements e }

let lemma_spec_remove_element
  (bf:spec_bloom_storage_u8)
  (e:element{contains bf.elements e})
  : Lemma (ensures (
    let new_bf = spec_remove_element bf e in
    if element_count bf.elements e > 1 then
      same_elements bf.elements new_bf.elements
    else
      same_elements_except bf.elements new_bf.elements e /\
      not (contains new_bf.elements e)
  )) =
  ()
