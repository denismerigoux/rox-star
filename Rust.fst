module Rust

module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

type u64 = U64.t
let _MAX_U64 = FStar.UInt.max_int 64

type usize = Usize.t
let _MAX_USIZE = FStar.UInt.max_int 32

type u32 = U32.t
let _MAX_U32 = FStar.UInt.max_int 32

type u8 = U8.t
let _MAX_U8 = FStar.UInt.max_int 8

type i64 = I64.t
let _MAX_I64 = FStar.Int.max_int 64
let _MIN_I64 = FStar.Int.min_int 64

type isize = Isize.t
let _MAX_ISIZE = FStar.Int.max_int 32
let _MIN_ISIZE = FStar.Int.min_int 32

type i32 = I32.t
let _MAX_I32 = FStar.Int.max_int 32
let _MIN_I32 = FStar.Int.min_int 32

let vec (a : Type0) = l:(list a){List.Tot.Base.length l <= _MAX_USIZE}
let array (a : Type0) (len: usize) = l:(list a){List.Tot.Base.length l = Usize.v len}

val vec_length : #a:Type0 -> vec a -> Tot usize
let vec_length #a v = Usize.uint_to_t (List.Tot.Base.length v)

val array_length : #a:Type0 -> #len:usize -> array a len -> Tot usize
let array_length #a #len array = len

val vec_fold : #a:Type0 -> #b:Type0 -> (a -> b -> Tot a) -> a -> v:vec b -> Tot a (decreases v)
let vec_fold #a #b f x v = List.Tot.Base.fold_left f x v

val vec_index : #a:Type0 -> vector:vec a -> i:usize{Usize.(i <^ vec_length vector)} -> Tot a
let vec_index #a v i = List.Tot.Base.index #a v (Usize.v i)

val array_index :
  #a:Type0 ->
  #len:usize ->
  arr:array a len ->
  i:usize{Usize.(i <^ array_length arr)} ->
  Tot a
let array_index #a #len arr i = List.Tot.Base.index #a arr (Usize.v i)

val array_update :
  #a: Type0 ->
  #len: usize ->
  arr: array a len ->
  i:usize{Usize.(i <^ array_length arr)} ->
  new_value:a ->
  Tot (array a len) (decreases arr)
let rec array_update #a #len arr i new_value =
   if i = 0ul then
     (new_value :: (List.Tot.Base.tl arr))
   else  (List.Tot.Base.hd arr)::(
     let tail = List.Tot.Base.tl arr in
     array_update #a #(Usize.(len -^ 1ul)) tail Usize.(i -^ 1ul) new_value
   )

val enumerate : #a:eqtype -> v:vec a ->
  Tot (vec (a & i:int))
let enumerate #a v = List.Tot.Base.mapi (fun i e -> (e,i)) v

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

val vec_foldl :
  #b:Type ->
  vector:vec b ->
  a:(i:usize{Usize.(i <=^ vec_length vector)} -> Type) ->
  a 0ul ->
  f:( i:usize{Usize.(i <^ vec_length vector)} -> b -> a i -> Tot (a Usize.(i +^ 1ul))) ->
  Tot (a (vec_length vector))
let vec_foldl #b vector a x f =
  let len = vec_length vector in
  if len = 0ul then x else
    repeat_left 0 (Usize.v len)
    (fun (i:nat{0 <= i /\ i <= Usize.v len}) -> a (Usize.uint_to_t i))
    (fun i acc -> f (Usize.uint_to_t i) (List.Tot.Base.index vector i) acc)
    x

val vec_all : #b:Type -> vector:vec b -> f:(b -> bool) -> Tot bool (decreases vector)
let rec vec_all #b vector f = match vector with
  | [] -> true
  | hd::tl -> if f hd then vec_all tl f else false
