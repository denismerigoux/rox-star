module Test.TextInput

open TextInput
open Rust


let input : text =
  let v = vec_empty () in
  let v = vec_push v "abc" in
  let v = vec_push v "de" in
  let v = vec_push v "f" in
  v

let test () : All.ML unit =
  IO.print_string "Beginning test.\n";
  let input = selection_new input in
  let input = adjust_horizontal input 3l NotSelected in
  assert_eq "1" (IO.print_uint32) input.edit_point.line 0ul;
  assert_eq "2" (IO.print_uint32) input.edit_point.index 3ul;
  let input = adjust_vertical input 1l Selected in
  assert_eq "3" (IO.print_uint32) input.edit_point.line 1ul;
  assert_eq "4" (IO.print_uint32) input.edit_point.index 2ul;
  let input = adjust_vertical input (-1l) NotSelected in
  assert_eq "5" (IO.print_uint32) input.edit_point.line 0ul;
  assert_eq "6" (IO.print_uint32) input.edit_point.index 2ul;
  let input = adjust_vertical input 2l NotSelected in
  assert_eq "7" (IO.print_uint32) input.edit_point.line 2ul;
  assert_eq "8" (IO.print_uint32) input.edit_point.index 1ul;
  let input = adjust_vertical input (-1l) NotSelected in
  assert_eq "9" (IO.print_uint32) input.edit_point.line 1ul;
  assert_eq "10" (IO.print_uint32) input.edit_point.index 1ul;
  let input = adjust_horizontal input 2l NotSelected in
  assert_eq "11" (IO.print_uint32) input.edit_point.line 2ul;
  assert_eq "12" (IO.print_uint32) input.edit_point.index 0ul;
  IO.print_string "End of test. If no failed assertion then passed!\n"

let _ = test ()
