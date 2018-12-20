module Test.TextInput

open TextInput
open Rust


let input : text =
  let v = vec_empty () in
  assert_norm (FStar.String.strlen "abc" = 3);
  let v = vec_push v "abc" in
  assert_norm (FStar.String.strlen "de" = 2);
  let v = vec_push v "de" in
  assert_norm (FStar.String.strlen "f" = 1);
  let v = vec_push v "f" in
  assert_norm (number_of_lines v = 3ul);
  v

let _  =
  admit();
  let input = selection_new input in
  let input = adjust_horizontal input 3l NotSelected in
  let input = adjust_vertical input 1l Selected in
  ()
