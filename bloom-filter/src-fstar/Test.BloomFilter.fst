module Test.BloomFilter

open Rust
open BloomFilter
open Spec.BloomFilter

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32


let hash (i:usize) : All.ML u32 =
  let hash : u32 = i in
  let hash = U32.(hash ^^ (hash <<^ U32.uint_to_t 12)) in
  let hash = U32.(hash ^^ (0xa5d8f52cul >>^ (i %^ 0xfful)) +%^ (hash &^ 0x589dcul)) in
  let hash = U32.(hash -%^ (hash |^ (hash <<^ U32.uint_to_t 4))) in
  hash

let print_bool (b:bool) : All.ML unit =
   if b then IO.print_string "true" else IO.print_string "false"

let test () : All.ML unit =
  IO.print_string "Beginning bloom filter test.\n";
  let bf = new_bloom_filter () in
  let bf = { bf with storage =  iter_range_ml 0ul 1000ul (fun i bf ->
     let bf = insert_hash bf (hash i) in
     bf
  ) bf.storage } in
  iter_range_ml 0ul 1000ul (fun i () ->
    assert_eq #bool "1"
      print_bool
      (might_contain_hash bf.storage (hash i))
      true
  ) ();
  let bf = { bf with storage = iter_range_ml 0ul 100ul (fun i bf ->
    let bf = remove_hash bf (hash i) in
    bf
  ) bf.storage } in
  iter_range_ml 100ul 1000ul (fun i () ->
    assert_eq #bool "2"
      print_bool
      (might_contain_hash bf.storage (hash i))
      true
  ) ();
  IO.print_string "End of test. If nothing appeared then it passed !\n"


let _ = test ()
