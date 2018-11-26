module Rust

let vec (a : Type0) = list a

val length : #a:Type0 -> vec a -> Tot nat
let length #a v = List.Tot.Base.length v

val fold : #a:Type0 -> #b:Type0 -> (a -> b -> Tot a) -> a -> v:vec b -> Tot a (decreases v)
let fold #a #b f x v = List.Tot.Base.fold_left f x v

val index : #a:Type0 -> v:vec a -> i:nat{i < length v} -> Tot a
let index #a v i = List.Tot.Base.index #a v i

val enumerate : #a:eqtype -> v:vec a ->
  Tot (vec (a & i:int))
let enumerate #a v = List.Tot.Base.mapi (fun i e -> (e,i)) v

val foldl :
  #b:Type ->
  v:vec b{length v > 0} ->
  a:(i:nat{i < length v} -> Type) ->
  a 0 ->
  f:( i:nat{i < length v - 1} -> b -> a i -> Tot (a (i+1))) ->
  Tot (a (length v - 1)) (decreases v)
let foldl #b v a x f =
  Lib.LoopCombinators.repeat_left 0 ((length v - 1))
    a
    (fun i acc -> f i (List.Tot.Base.index v i) acc)
    x
