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

let is_valid_text_point (self:text_point) (input:selection) =
  Usize.(self.line <^ number_of_lines input.lines) &&
  Usize.(self.index <=^ (line_len input.lines self.line))

type valid_text_point (input:selection) = p:text_point{is_valid_text_point p input}

val current_line_length :
  self:text_input{Usize.(self.edit_point.line <^ number_of_lines self.lines)} ->
  usize
let current_line_length self = line_len self.lines self.edit_point.line

val clear_selection : selection -> Tot selection
let clear_selection self =
  let input = { self with selection_origin = None} in
  let input = { self with selection_direction = Unspecified} in
  self

val select_all : selection -> Tot selection
let select_all self =
  let last_line = Usize.(number_of_lines self.lines -^ 1ul) in
  let self = { self with selection_origin = Some({ line = 0ul; index = 0ul }) } in
  let self =
    { self with edit_point = { line = last_line; index = line_len self.lines last_line} }
   in let self = { self with selection_direction = Forward } in
   self

val selection_origin_or_edit_point : self:selection -> Tot (valid_text_point self)
let selection_origin_or_edit_point self =
  unwrap_or self.selection_origin self.edit_point

val selection_start : self:selection -> Tot (valid_text_point self)
let selection_start self = match self.selection_direction with
  | Unspecified | Forward -> selection_origin_or_edit_point self
  | Backward -> self.edit_point

val selection_end : self:selection -> Tot (valid_text_point self)
let selection_end self = match self.selection_direction with
  | Unspecified | Forward -> self.edit_point
  | Backward -> selection_origin_or_edit_point self

let has_selection (self:selection) : Tot bool =
  is_some self.selection_origin

val adjust_selection_for_horizontal_change :
  selection ->
  direction ->
  selection_status ->
  Tot (selection * bool)
let adjust_selection_for_horizontal_change self adjust select =
  if select = Selected then
    let self = if is_none self.selection_origin then
      let self = { self with selection_origin = Some (self.edit_point) } in
      self
    else self in
    (self, false)
  else
    let self = if has_selection self then
      let self = { self with edit_point = match adjust with
      | DBackward -> selection_start self
      | DForward -> selection_end self
      } in
      let self = clear_selection self in
      self
    else self in
    (self, true)

val adjust_horizontal_to_limit : selection -> direction -> selection_status -> text_input
let adjust_horizontal_to_limit self direction select =
  let (self, adjust) = adjust_selection_for_horizontal_change self direction select in
  if adjust then
    self
  else match direction with
    | DBackward -> let self = { self with  edit_point = { self.edit_point with line = 0ul } } in
      let self = { self with edit_point = { self.edit_point with index = 0ul } } in
      self
    | DForward -> let self = { self with edit_point = { self.edit_point with
        line = Usize.((number_of_lines self.lines) -^ 1ul) } } in
        let self = { self with edit_point = { self.edit_point with
	index = line_len self.lines Usize.((number_of_lines self.lines) -^ 1ul) } } in
	self

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
