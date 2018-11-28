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

type count = n:nat{n > 0}

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
  Tot nat (decreases l)
let rec element_count #a l e = match l with
  | [] -> 0
  | (e', count)::tl ->
    if e = e' then count else element_count tl e

val decr_count:
  #a:eqtype ->
  l:count_list a ->
  e : a{contains l e} ->
  Tot (l':count_list a{
    if element_count l e > 1 then
      same_elements l l'
    else begin
      not (contains l' e) /\
      (forall (e':a{e' <> e}). contains l e' <==> contains l' e')
    end
  }) (decreases l)
let rec decr_count #a l e =
  match l with
  | [] -> l
  | (e', old_count)::tl ->
    if e = e' && old_count = 1 then
      tl
    else if e = e' && old_count > 1 then
      (e', old_count - 1)::tl
    else
      (e', old_count)::(decr_count tl e)

noeq type spec_bloom_storage_u8 = {
   elements: (l:(count_list element){no_duplicates l})
}

let rec all_elements
  (#a:eqtype)
  (l:count_list a)
  (f:((a & count) -> bool))
  : Tot bool (decreases l) =
  match l with
  | [] -> true
  | hd::tl -> if f hd then all_elements tl f else false


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
  e:element ->
  Tot spec_bloom_storage_u8
let spec_remove_element bf e =
  if contains bf.elements e  then
    { bf with elements = decr_count bf.elements e }
  else
    bf
