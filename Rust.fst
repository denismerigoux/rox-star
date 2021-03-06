module Rust

module U128 = FStar.UInt128
module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

#reset-options "--max_fuel 1"

(*** Integers *)

(**** Types and max values *)

type u128 = U128.t
let _MAX_U128 = U128.uint_to_t (FStar.UInt.max_int 128)

type u64 = U64.t
let _MAX_U64 = U64.uint_to_t (FStar.UInt.max_int 64)

type usize = Usize.t
let _MAX_USIZE = Usize.uint_to_t (FStar.UInt.max_int 32)

type u32 = U32.t
let _MAX_U32 = U32.uint_to_t (FStar.UInt.max_int 32)

type u8 = U8.t
let _MAX_U8 = U8.uint_to_t (FStar.UInt.max_int 8)

type i64 = I64.t
let _MAX_I64 = I64.int_to_t (FStar.Int.max_int 64)
let _MIN_I64 = I64.int_to_t (FStar.Int.min_int 64)

type isize = Isize.t
let _MAX_ISIZE = Isize.int_to_t (FStar.Int.max_int 32)
let _MIN_ISIZE = Isize.int_to_t (FStar.Int.min_int 32)


type i32 = I32.t
let _MAX_I32 = I32.int_to_t (FStar.Int.max_int 32)
let _MIN_I32 = I32.int_to_t (FStar.Int.min_int 32)

(**** Casts and basic functions *)

let isize_to_usize_safe (x:isize{Isize.(x >=^ 0l)}) : Tot usize = Usize.uint_to_t (Isize.v x)
let usize_to_isize_safe (x:usize{Usize.v x <= Isize.v _MAX_ISIZE}) : Tot isize =
  Isize.int_to_t (Usize.v x)

let u32_to_u64 (x:u32) : u64 = U64.uint_to_t (U32.v x)
let u64_to_u128 (x:u64) : u128 = U128.uint_to_t (U64.v x)

let u128_to_u64 (x:u128) : u64 = U64.uint_to_t (U128.v x % U64.v _MAX_U64)

let max_isize (x y:isize) = Isize.(if x >=^ y then x else y)
let min_isize (x y:isize) = Isize.(if x >=^ y then y else x)

let max_usize (x y:usize) = Usize.(if x >=^ y then x else y)
let min_usize (x y:usize) = Usize.(if x >=^ y then y else x)

(*** Strings *)

type rust_string = s:string{FStar.String.strlen s <= Usize.v _MAX_USIZE}

let string_length (s:rust_string) : Tot usize = Usize.uint_to_t (FStar.String.strlen s)

open FStar.Seq

(*** Vectors *)

let vec (a : Type0) = l:(seq a){length l <= Usize.v _MAX_USIZE}

val vec_length : #a:Type0 -> vec a -> Tot usize
let vec_length #a v = Usize.uint_to_t (length v)

val vec_empty : #a:Type0 -> unit -> Tot (r:(vec a){vec_length r = 0ul})
let vec_empty #a () = empty

let vec_idx (#a: Type0) (s:vec a) = idx:usize{Usize.(idx <^ vec_length s)}

val vec_index : #a:Type0 -> s:vec a -> i:vec_idx s -> Tot a
let vec_index #a v i = index #a v (Usize.v i)

val vec_push : #a:Type0 -> s:vec a{length s + 1 <= Usize.v _MAX_USIZE} -> new_val:a -> vec a
let vec_push #a s new_val = s @| (create 1 new_val)

let vec_push_lemma1 (#a:eqtype) (s:vec a{length s + 1 <= Usize.v _MAX_USIZE}) (new_val:a)
  (idx:vec_idx s)
  : Lemma (ensures (vec_index (vec_push s new_val) idx = vec_index s idx))
  [SMTPat (vec_index (vec_push s new_val) idx)]  = ()

let vec_push_lemma2 (#a:eqtype) (s:vec a{length s + 1 <= Usize.v _MAX_USIZE}) (new_val:a)
  : Lemma (ensures (vec_index (vec_push s new_val) (vec_length s)) = new_val)
  [SMTPat (vec_index (vec_push s new_val) (vec_length s))] = ()

let vec_push_lemma3 (#a:eqtype) (s:vec a{length s + 1 <= Usize.v _MAX_USIZE}) (new_val:a)
  : Lemma (ensures (vec_length (vec_push s new_val) = Usize.(vec_length s +^ 1ul)))
  [SMTPat (vec_length (vec_push s new_val))] = ()

val vec_update : #a:Type0 -> s:vec a -> idx:vec_idx s -> new_val:a -> Tot (vec a)
let vec_update #a s idx new_val = upd #a s (Usize.v idx) new_val

let vec_update_lemma1 (#a:eqtype) (s:vec a) (idx idx':vec_idx s) (new_val:a)
  : Lemma (requires (idx <> idx'))
    (ensures (vec_index (vec_update s idx new_val) idx' = vec_index s idx'))
  [SMTPat (vec_index (vec_update s idx new_val) idx')]
  = ()

let vec_update_lemma2 (#a:eqtype) (s:vec a) (idx:vec_idx s) (new_val:a)
  : Lemma (ensures (vec_index (vec_update s idx new_val) idx = new_val))
  [SMTPat (vec_index (vec_update s idx new_val) idx)]
  = ()

(*** Arrays *)

let array (a : Type0) (len: usize) = l:(seq a){length l = Usize.v len}

val array_new: #a:Type0 -> len:usize -> v:a -> Tot (arr:array a len)
let array_new #a len v = create #a (Usize.v len) v

val array_length : #a:Type0 -> #len:usize -> array a len -> Tot usize
let array_length #a #len array = len

let arr_idx (#a:Type0) (#len:usize) (arr:array a len) = idx:usize{Usize.(idx <^ len)}

val array_index : #a:Type0 -> #len:usize -> arr:array a len -> i:arr_idx arr -> Tot a
let array_index #a #len arr i = index #a arr (Usize.v i)

val op_Array_Access: #a:Type0 -> #len:usize -> arr:array a len -> i:arr_idx arr -> Tot a
let op_Array_Access = array_index

val array_update : #a:eqtype -> #len:usize -> arr:array a len -> i:arr_idx arr -> new_value:a ->
  Tot (new_arr:array a len)
let array_update #a #len arr i new_value = vec_update #a arr i new_value

let array_update_lemma1 (#a:eqtype) (#len:usize) (s:array a len) (idx idx':arr_idx s) (new_val:a)
  : Lemma (requires (idx <> idx'))
    (ensures (array_index (array_update s idx new_val) idx' = array_index s idx'))
  [SMTPat (array_index (array_update s idx new_val) idx')]
  = ()

let array_update_lemma2 (#a:eqtype) (#len:usize) (s:array a len) (idx:arr_idx s) (new_val:a)
  : Lemma (ensures (array_index (array_update s idx new_val) idx = new_val))
  [SMTPat (array_index (array_update s idx new_val) idx)]
  = ()

(*** Iterators *)

let iter (a: Type0) = vec a
val array_to_iter : #a:eqtype -> #len:usize -> array a len -> iter a
let array_to_iter #a #len arr = arr

val vec_to_iter : #a:eqtype -> vec a -> iter a
let vec_to_iter #a s = s

val iter_collect : #a:eqtype -> iter a -> vec a
let iter_collect #a it = it

private val repeat_left:
    lo:nat
  -> hi:nat{lo <= hi}
  -> a:(i:nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:nat{lo <= i /\ i < hi} -> a i -> a (i + 1))
  -> acc:a lo
  -> Tot (a hi) (decreases (hi - lo))
private let rec repeat_left lo hi a f acc =
  if lo = hi then acc
  else repeat_left (lo + 1) hi a f (f lo acc)

val iter_foldl : #b:Type -> #a:Type ->
  s:vec b ->
  init:a ->
  f:(a ->  b -> Tot a) ->
  Tot a
let iter_foldl #b #a s x f =
  let len = vec_length s in
  if len = 0ul then x else
    repeat_left 0 (Usize.v len)
    (fun _ -> a )
    (fun i acc -> f acc (vec_index s (Usize.uint_to_t i)))
    x

val vec_all : #b:Type -> vector:vec b -> f:(b -> bool) -> Tot bool (decreases vector)
let rec vec_all #b vector f = let len = vec_length vector in
    repeat_left 0 (Usize.v len)
    (fun _ -> bool)
    (fun i acc -> acc && f (vec_index vector (Usize.uint_to_t i)))
    true


private val enumerate_aux :
  #a:eqtype ->
  tot:nat{tot <= Usize.v _MAX_USIZE} ->
  s:(iter a){length s <= tot} ->
  Tot (r:(iter (a & usize)){length r = length s})
  (decreases (length s))
private let rec enumerate_aux #a tot s =
  let len = length s in
  if len = 0 then empty else
    let hd = index s 0 in let tl = slice s 1 len in
    (create 1 (hd, Usize.uint_to_t (tot - len))) @| (enumerate_aux tot tl)

private let rec enumerate_aux_lemma
  (#a:eqtype)
  (tot:nat{tot <= Usize.v _MAX_USIZE})
  (s:(vec a){length s <= tot})
  (i:usize{Usize.v i < tot})
  : Lemma (ensures (
    let r = enumerate_aux tot s in
    if Usize.v i < tot - length s then true else
      let rel_i = Usize.uint_to_t (Usize.v i - tot + length s) in
      vec_index r rel_i = (vec_index s rel_i, i)
  )) (decreases (length s)) =
  let len = length s in if len = 0 then () else
  let tl = slice s 1 len in enumerate_aux_lemma #a tot tl i

val enumerate: #a:eqtype -> vec a -> Tot (vec (a & usize))
let enumerate #a s = enumerate_aux (length s) s

let enumerate_lemma1 (#a:eqtype) (s:iter a) (idx:vec_idx s)
  : Lemma (ensures (vec_index (iter_collect (enumerate s)) idx = (vec_index s idx, idx)))
  [SMTPat (vec_index (iter_collect (enumerate s)) idx)] = enumerate_aux_lemma (length s) s idx

val iter_range: #a:Type -> low:usize -> high:usize{Usize.(low <=^ high)} ->
  f:(i:usize{Usize.(low <=^ i) /\ Usize.(i <^ high)} -> a -> a) -> init:a ->
  Tot a
let iter_range #a low high f init = if low = high then init else repeat_left
    (Usize.v low) (Usize.(v (high -^ 1ul)))
    (fun _ -> a )
    (fun i acc -> f (Usize.uint_to_t i) acc)
    init

(*** Sugars *)

(**** Option type *)

let unwrap_or (#a:Type) (x:option a) (d:a) : a = match x with
  | Some x -> x
  | None -> d

let is_some (#a:Type) (x:option a) : bool = match x with
  | Some _ -> true
  | None -> false

let is_none (#a:Type) (x:option a) : bool = not (is_some x)

(*** Testing *)

let assert_eq (#a:eqtype) (id:string) (printing: (a -> All.ML unit)) (x y:a) : All.ML unit =
  if x = y then () else begin
    IO.print_string "assertion [";
    IO.print_string id;
    IO.print_string "] failed: ";
    printing x;
    IO.print_string " != ";
    printing y;
    IO.print_string "\n"
  end

private val repeat_left_ml:
    lo:nat
  -> hi:nat{lo <= hi}
  -> a:(i:nat{lo <= i /\ i <= hi} -> Type)
  -> f:(i:nat{lo <= i /\ i < hi} -> a i -> All.ML (a (i + 1)))
  -> acc:a lo
  -> All.ML (a hi) (decreases (hi - lo))
private let rec repeat_left_ml lo hi a f acc =
  if lo = hi then acc
  else repeat_left_ml (lo + 1) hi a f (f lo acc)


val iter_range_ml: #a:Type -> low:usize -> high:usize{Usize.(low <=^ high)} ->
  f:(i:usize{Usize.(low <=^ i) /\ Usize.(i <^ high)} -> a -> All.ML a) -> init:a ->
  All.ML a
let iter_range_ml #a low high f init = if low = high then init else
  repeat_left_ml
    (Usize.v low) (Usize.(v (high -^ 1ul)))
    (fun _ -> a )
    (fun i acc -> f (Usize.uint_to_t i) acc)
    init
