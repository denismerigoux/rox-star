module Spec.BloomFilter

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

open Rust
open BloomFilter
open FStar.List.Tot.Base

assume type element: eqtype

assume val hash: element -> u32

type count = n:nat

#reset-options "--max_fuel 1"

let contains (#a:eqtype) (l:list (a & count)) (e:a) : Tot bool =
  existsb (fun ((e', n) : a & count) -> e = e' && n > 0) l

let rec no_duplicates (#a:eqtype) (l:list (a & count)) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | (e, _)::tl -> not (contains tl e) && no_duplicates tl

type count_list (a:eqtype) = (l:list (a & count){no_duplicates l})

let same_elements (#a: eqtype) (l1 l2: count_list a) =
  (forall (e:a). contains l1 e <==> contains l2 e)

val element_count: #a:eqtype ->
  l:count_list a ->
  e: a ->
  Tot (c:count{c > 0 <==> contains #a l e}) (decreases l)
let rec element_count #a l e = match l with
  | [] -> 0
  | (e', count)::tl ->
    if e = e' then count else element_count tl e

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

let same_elements_except (#a:eqtype) (l1 l2: count_list a) (e:a) =
   (forall (e':a{e' <> e}). contains l1 e' <==> contains l2 e')

val decr_count:
  #a:eqtype ->
  l:count_list a ->
  e : a{contains l e} ->
  Tot (l':count_list a{
      if element_count l e > 1 then
        same_elements l l' /\ element_count l' e = element_count l e - 1
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


val spec_remove_element:
  bf:spec_bloom_storage_u8 ->
  e:element{contains bf.elements e} ->
  Tot spec_bloom_storage_u8
let spec_remove_element bf e =
    { bf with elements = decr_count bf.elements e }

type bloom_filter = {
  storage: bloom_storage_u8;
  ghost_state: spec_bloom_storage_u8
}

val new_bloom_filter: unit -> Tot bloom_filter
let new_bloom_filter () = {
  storage = bloom_storage_u8_new ();
  ghost_state = { elements = [] }
}

val insert_element: bf:bloom_filter -> e:element -> Tot bloom_filter
let insert_element bf e =
  let hash_val = hash e in
  (* *) let new_bf = { bf with ghost_state = spec_insert_element bf.ghost_state e } in
  { new_bf with storage = insert_hash new_bf.storage hash_val }

val remove_element:
  bf:bloom_filter ->
  e:element{contains bf.ghost_state.elements e} ->
  Tot bloom_filter
let remove_element bf e =
  let hash_e = hash e in
  (* *) let new_bf = { bf with ghost_state = spec_remove_element bf.ghost_state e } in
  { new_bf with storage = remove_hash new_bf.storage hash_e }
