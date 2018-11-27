module Spec.BloomFilter

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

open Rust

assume type element: eqtype

assume val hash: element -> u32

noeq type spec_bloom_storage_u8 = {
   map: FStar.Map.t element nat;
   elements: list element
}

val spec_insert_element:
  bf:spec_bloom_storage_u8 ->
  e:element ->
  Tot spec_bloom_storage_u8
let spec_insert_element bf e =
  if FStar.Map.contains bf.map e then
    let old_count = FStar.Map.sel bf.map e in
    let new_map = FStar.Map.upd bf.map e (old_count + 1) in
    if old_count = 0 then
      { map = new_map; elements = e::bf.elements}
    else
      {bf with map = new_map }
  else
    { map = FStar.Map.upd bf.map e 1; elements = e::bf.elements }

let rec list_remove (#a:eqtype) (l:list a) (e:a) : Tot (list a) (decreases l)=
  match l with
  | [] -> l
  | hd::tl ->
    let new_tl = list_remove tl e in
    if hd = e then new_tl else hd::new_tl

val spec_remove_element:
  bf:spec_bloom_storage_u8 ->
  e:element ->
  Tot spec_bloom_storage_u8
let spec_remove_element bf e =
  if FStar.Map.contains bf.map e then
    let old_count = FStar.Map.sel bf.map e in
    if old_count = 0 then bf else
      { map = FStar.Map.upd bf.map e (old_count - 1); elements = list_remove bf.elements e }
  else
    bf
