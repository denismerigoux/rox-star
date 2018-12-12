module TextInput

open Rust
module U64 = FStar.UInt64
module Usize = FStar.UInt32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Isize = FStar.Int32
module I32 = FStar.Int32

#reset-options "--max_fuel 0"

type selection_status =
  | Selected
  | NotSelected

type selection_direction =
  | Forward
  | Backward
  | Unspecified

type direction =
  | DForward
  | DBackward

type small_usize = x:usize{Usize.v x + 1 <= Isize.v _MAX_ISIZE }

let abs_isize (x: isize{Isize.(x >^ _MIN_ISIZE)}) : usize =
  Isize.(if x >=^ 0l then isize_to_usize_safe x else isize_to_usize_safe (neg_isize x))

type text_point = {
  line: small_usize;
  index: small_usize;
}
val point_lte : text_point -> text_point -> Tot bool
let point_lte p1 p2 =
  Usize.(p1.line <^ p2.line) ||
  Usize.((p1.line = p2.line && p1.index <=^ p2.index))

type selection_state = {
  start: text_point;
  final: text_point;
  direction: selection_direction
}

type dom_string = s:rust_string{Usize.v (string_length s) + 1 < Isize.v _MAX_ISIZE}

let dom_string_len (s:dom_string) : Tot usize = string_length s

let number_of_lines (t:vec dom_string) : Tot usize = vec_length t

type text = t:vec dom_string{Usize.v (number_of_lines t) + 1 <= Isize.v _MAX_ISIZE}

val line_len : text:text -> i:vec_idx text -> Tot usize
let line_len t i =  dom_string_len (vec_index t i)

type text_input = {
  lines: text;
  edit_point: text_point;
  selection_origin: option text_point;
  selection_direction: selection_direction;
  max_length: option usize;
  min_length: option usize;
}

let assert_edit_order (input: text_input) : Tot bool =
  begin match input.selection_origin with
    | Some(start) ->
      Usize.(start.line <^ (number_of_lines input.lines)) &&
      Usize.(start.index <=^ (line_len input.lines start.line)) &&
      begin match input.selection_direction with
	| Unspecified | Forward -> point_lte start input.edit_point
	| Backward -> point_lte input.edit_point start
      end
    | None -> true
  end

val assert_ok_selection : text_input -> Tot bool
let assert_ok_selection input =
  assert_edit_order input &&
  Usize.(input.edit_point.line <^ (number_of_lines input.lines)) &&
  Usize.(input.edit_point.index <=^ (line_len input.lines input.edit_point.line))

type selection = input:text_input{assert_ok_selection input}

type valid_text_point (input:selection) = p:text_point{
  Usize.(p.line <^ number_of_lines input.lines) &&
  Usize.(p.index <=^ (line_len input.lines p.line))
}

val current_line_length :
  input:text_input{Usize.(input.edit_point.line <^ number_of_lines input.lines)} ->
  usize
let current_line_length input = line_len input.lines input.edit_point.line

val clear_selection : selection -> Tot selection
let clear_selection input =
  { input with
    selection_origin = None;
    selection_direction = Unspecified;
  }

val select_all : selection -> Tot selection
let select_all input =
  let last_line = Usize.(number_of_lines input.lines -^ 1ul) in
  { input with
    selection_origin = Some({ line = 0ul; index = 0ul });
    edit_point = { line = last_line; index = line_len input.lines last_line};
    selection_direction = Forward;
  }

val selection_origin_or_edit_point : input:selection -> Tot (valid_text_point input)
let selection_origin_or_edit_point input = match input.selection_origin with
  | Some o -> o
  | None -> input.edit_point

val selection_start : input:selection -> Tot (valid_text_point input)
let selection_start input = match input.selection_direction with
  | Unspecified | Forward -> selection_origin_or_edit_point input
  | Backward -> input.edit_point

val selection_end : input:selection -> Tot (valid_text_point input)
let selection_end input = match input.selection_direction with
  | Unspecified | Forward -> input.edit_point
  | Backward -> selection_origin_or_edit_point input

val adjust_selection_for_horizontal_change :
  selection ->
  direction ->
  selection_status ->
  Tot (selection * bool)
let adjust_selection_for_horizontal_change input adjust select =
  match (select, input.selection_origin) with
  | (Selected, None) -> (input, input.selection_origin = Some(input.edit_point))
  | (NotSelected, Some(_)) ->
    let new_edit_point = match adjust with
      | DBackward -> selection_start input
      | DForward -> selection_end input
    in
    ({ input with
      edit_point = new_edit_point
    }, true)
  | _ -> (input, false)

val adjust_horizontal_to_limit : selection -> direction -> selection_status -> text_input
let adjust_horizontal_to_limit input direction select =
  let (input, adjust) = adjust_selection_for_horizontal_change input direction select in
  if adjust then
    input
  else match direction with
    | DBackward -> { input with edit_point = { line = 0ul; index = 0ul; } }
    | DForward -> { input with edit_point = {
        line = Usize.((number_of_lines input.lines) -^ 1ul);
	index = line_len input.lines Usize.((number_of_lines input.lines) -^ 1ul)
      } }

val clear_selection_to_limit : selection -> direction -> selection
let clear_selection_to_limit input direction =
  let input = clear_selection input in
  adjust_horizontal_to_limit input direction NotSelected


val update_selection_direction : text_input -> text_input
let update_selection_direction input =
  { input with
    selection_direction = match input.selection_origin with
     | None -> Forward
     | Some(origin) -> if point_lte input.edit_point origin then Backward else Forward
  }

#reset-options "--z3rlimit 20"

val adjust_vertical :
  input:selection ->
  adjust:isize{(Isize.v adjust) + (Usize.v input.edit_point.line) + 1 <= Isize.v _MAX_ISIZE} ->
  selection_status ->
  selection
let adjust_vertical input adjust select =
  let input = match (select, input.selection_origin) with
    | (Selected, None) -> { input with selection_origin = Some(input.edit_point) }
    | (Selected, Some _) -> input
    | (NotSelected, _) -> clear_selection input
  in
  assert (Usize.(input.edit_point.line <^ number_of_lines input.lines));
  let target_line : isize = Isize.((usize_to_isize_safe input.edit_point.line) +^ adjust) in
  if Isize.(target_line <^ 0l) then
    let zero_point =  { line = 0ul; index = 0ul } in
    let input = { input with edit_point = zero_point } in
    (* BEGIN ADDED CODE *)
    (* If there is a forward selection, we need to put the start at 0 *)
    let input = match (input.selection_origin, input.selection_direction) with
     | (Some _, Unspecified) | (Some _, Forward) ->
       { input with selection_origin = Some(zero_point) }
     | _ -> input
    in
    (* END ADDED CODE*)
    input
  else if Usize.((isize_to_usize_safe target_line) >=^ number_of_lines input.lines) then begin
    let input = { input with edit_point = { input.edit_point with
      line = Usize.((number_of_lines input.lines) -^ 1ul);
    } } in
    let input = { input with edit_point = { input.edit_point with
      index = current_line_length input;
    } } in
    (* BEGIN ADDED CODE *)
    (* We also have to update the selection origin here *)
    let input = match (input.selection_origin, input.selection_direction) with
      | (Some origin, Backward) ->
	if point_lte origin input.edit_point then
	  { input with selection_origin = Some(input.edit_point) }
	else input
      | _ -> input
    in
    (* END ADDED CODE *)
    input
  end else begin
    let target_line_length =  line_len input.lines (isize_to_usize_safe target_line) in
    let col = if Usize.(input.edit_point.index <^ target_line_length)
      then input.edit_point.index
      else target_line_length
    in
    let input =
    { input with edit_point = {
      line = isize_to_usize_safe target_line;
      index = col
    } } in
    (* BEGIN ADDED CODE *)
    (* As well as here *)
    let input = match (input.selection_origin, input.selection_direction) with
      | (None, _) -> input
      | (Some origin, Forward) | (Some origin, Unspecified) ->
	if point_lte input.edit_point origin then
	   { input with selection_origin = Some(input.edit_point) }
	else input
     | (Some origin, Backward) ->
       	if point_lte origin input.edit_point then
	   { input with selection_origin = Some(input.edit_point) }
	else input
    in
    (* END ADDED CODE *)
    input
  end

#reset-options "--z3rlimit 50"

val perform_horizontal_adjustment :
  input:selection ->
  adjust:isize{
    Isize.(adjust >^ _MIN_ISIZE)
  } ->
  selection_status ->
  Tot selection
  (decreases (Usize.v (abs_isize adjust)))
let rec perform_horizontal_adjustment input adjust select =
  let input = if Isize.(adjust <^ 0l) then begin
    (* BEGIN ADDED CODE *)
    (* F* does not understand without the assertion *)
    let neg_val = neg_isize adjust in
    assert(Isize.(neg_val >=^ 0l));
    (* END ADDED CODE *)
    let adjust_abs = isize_to_usize_safe neg_val in
    let remaining = input.edit_point.index in
    if Usize.(adjust_abs >^ remaining) && Usize.(input.edit_point.line >^ 0ul) then
      let input = adjust_vertical input (-1l) select in
      let input =
	{ input with edit_point = { input.edit_point with index = current_line_length input }}
      in
      assert (assert_edit_order input);
      (* BEGIN CHANGED CODE *)
      (* Could not prove mutually recursive function termination so inlined other function here *)
      //adjust_horizontal input I.(adjust +^ ((u_to_i remaining) +^ 1l)) select
      let new_adjust = Isize.(adjust +^ ((usize_to_isize_safe remaining) +^ 1l)) in
      let direction = if Isize.(adjust >=^ 0l) then DForward else DBackward in
      let (input, done) = adjust_selection_for_horizontal_change input direction select in
      (* Again F* does not seem to understand without the assertions... *)
      assert(Isize.(adjust <^ new_adjust));
      assert(Isize.(new_adjust <=^ 0l));
      assert(Usize.(abs_isize new_adjust <^ abs_isize adjust));
      if done then input else perform_horizontal_adjustment input new_adjust select
      (* END CHANGED CODE*)
    else
      { input with edit_point = { input.edit_point with index =
        isize_to_usize_safe
	  (max_isize 0l Isize.((usize_to_isize_safe input.edit_point.index) +^ adjust))
      } }
  end else begin
    let remaining = Usize.((current_line_length input) -^ input.edit_point.index) in
    if
      Usize.((isize_to_usize_safe adjust) >^ remaining) &&
      Usize.(number_of_lines input.lines >^ input.edit_point.line +^ 1ul)
    then
      let input = adjust_vertical input 1l select in
      let input =
	{ input with edit_point = { input.edit_point with index = 0ul }}
      in
      (* BEGIN CHANGED CODE *)
      (* Could not prove mutually recursive function termination so inlined other function here *)
      //adjust_horizontal input I.(adjust -^ (u_to_i remaining) -^ 1l) select
      let adjust = Isize.(adjust -^ (usize_to_isize_safe remaining) -^ 1l) in
      let direction = if Isize.(adjust >=^ 0l) then DForward else DBackward in
      let (input, done) = adjust_selection_for_horizontal_change input direction select in
      if done then input else perform_horizontal_adjustment input adjust select
      (* END CHANGED CODE*)
    else { input with
      edit_point = { input.edit_point with
	index = min_usize (current_line_length input)
	  Usize.(input.edit_point.index +^ (isize_to_usize_safe adjust))
      }
    }
  end in
  update_selection_direction input

val adjust_horizontal :
  input:selection ->
  adjust:isize{Isize.(adjust >^ _MIN_ISIZE)} ->
  selection_status ->
  Tot selection
  (decreases (abs_isize adjust))
let adjust_horizontal input adjust select =
  let direction = if Isize.(adjust >=^ 0l) then DForward else DBackward in
  let (input, done) = adjust_selection_for_horizontal_change input direction select in
  if done then input else perform_horizontal_adjustment input adjust select

val adjust_horizontal_to_line_end : selection -> direction -> selection_status -> Tot selection
let adjust_horizontal_to_line_end input dir status =
  let (input, done) = adjust_selection_for_horizontal_change input dir status in
  if done then input else
    let shift : isize =
      let current_line = vec_index input.lines input.edit_point.line in
      match dir with
	| DBackward -> Isize.(0l -^ (usize_to_isize_safe input.edit_point.index))
	| DForward -> usize_to_isize_safe
	  Usize.((line_len input.lines input.edit_point.line) -^ input.edit_point.index)
    in
    perform_horizontal_adjustment input shift status
