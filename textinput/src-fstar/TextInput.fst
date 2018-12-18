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
  Isize.(if x >=^ 0l then isize_to_usize_safe x else isize_to_usize_safe (Isize.(0l -^ x)))

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
  let last_line = Usize.(number_of_lines self.lines -%^ 1ul) in
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
        line = Usize.((number_of_lines self.lines) -%^ 1ul) } } in
        let self = { self with edit_point = { self.edit_point with
	index = line_len self.lines Usize.((number_of_lines self.lines) -%^ 1ul) } } in
	self

val clear_selection_to_limit : selection -> direction -> selection
let clear_selection_to_limit self direction =
  let self = clear_selection self in
  adjust_horizontal_to_limit self direction NotSelected


val update_selection_direction : text_input -> text_input
let update_selection_direction input =
  { input with
    selection_direction = match input.selection_origin with
     | None -> Forward
     | Some(origin) -> if point_lte input.edit_point origin then Backward else Forward
  }

#reset-options "--z3rlimit 20"

val adjust_vertical :
  self:selection ->
  adjust:isize{(Isize.v adjust) + (Usize.v self.edit_point.line) + 1 <= Isize.v _MAX_ISIZE} ->
  selection_status ->
  selection
let adjust_vertical self adjust select =
  let self = if select = Selected then
    if is_none self.selection_origin then
      let self = { self with selection_origin = Some (self.edit_point) } in
      self
    else self
  else clear_selection self in
  assert (Usize.(self.edit_point.line <^ number_of_lines self.lines));
  let target_line : isize = Isize.((usize_to_isize_safe self.edit_point.line) +^ adjust) in
  if Isize.(target_line <^ 0l) then
    let self = { self with edit_point = { self.edit_point with line = 0ul } } in
    let self = { self with edit_point = { self.edit_point with index = 0ul } } in
    let self =
      if is_some self.selection_origin &&
        (self.selection_direction = Unspecified || self.selection_direction = Forward)
      then
	let self = { self with selection_origin = Some (self.edit_point) } in
	self
      else self
    in self
  else if Usize.((isize_to_usize_safe target_line) >=^ number_of_lines self.lines) then begin
    let self = { self with edit_point = { self.edit_point with
      line = Usize.((number_of_lines self.lines) -%^ 1ul);
    } } in
    let self = { self with edit_point = { self.edit_point with
      index = current_line_length self;
    } } in
    let self = if is_some self.selection_origin && self.selection_direction = Backward then
      let self = { self with selection_origin = Some (self.edit_point) } in
      self
    else self in
    self
  end else begin
    let target_line_length =  line_len self.lines (isize_to_usize_safe target_line) in
    let col = min_usize self.edit_point.index target_line_length in
    let self = { self with edit_point = { self.edit_point with
      line = isize_to_usize_safe target_line } } in
    let self = { self with edit_point = { self.edit_point with index = col } } in
    let self = match self.selection_origin with
    | Some origin -> if
      ((self.selection_direction = Unspecified || self.selection_direction = Forward) &&
        point_lte self.edit_point origin) ||
      (self.selection_direction = Backward && point_lte origin self.edit_point) then
      let self = { self with selection_origin = Some self.edit_point } in
      self else self
    | None -> self
    in self
  end

#reset-options "--z3rlimit 50"

val perform_horizontal_adjustment :
  self:selection ->
  adjust:isize{
    Isize.(adjust >^ _MIN_ISIZE)
  } ->
  selection_status ->
  Tot selection
  (decreases (Usize.v (abs_isize adjust)))
let rec perform_horizontal_adjustment self adjust select =
  let self = if Isize.(adjust <^ 0l) then begin
    let neg_val = Isize.(0l -^ adjust) in
    let adjust_abs = isize_to_usize_safe neg_val in
    let remaining = self.edit_point.index in
    if Usize.(adjust_abs >^ remaining) && Usize.(self.edit_point.line >^ 0ul) then
      let self = adjust_vertical self (-1l) select in
      let self =
	{ self with edit_point = { self.edit_point with index = current_line_length self }}
      in
      let adjust = Isize.(adjust +^ ((usize_to_isize_safe remaining) +^ 1l)) in
      let direction = if Isize.(adjust >=^ 0l) then DForward else DBackward in
      let (self, done) = adjust_selection_for_horizontal_change self direction select in
      if done then self else perform_horizontal_adjustment self adjust select
    else
      let self =  { self with edit_point = { self.edit_point with index =
        isize_to_usize_safe
	  (max_isize 0l Isize.((usize_to_isize_safe self.edit_point.index) +^ adjust))
      } } in
      self
  end else begin
    let remaining = Usize.((current_line_length self) -^ self.edit_point.index) in
    if
      Usize.((isize_to_usize_safe adjust) >^ remaining) &&
      Usize.(number_of_lines self.lines >^ self.edit_point.line +^ 1ul)
    then
      let self = adjust_vertical self 1l select in
      let self =
	{ self with edit_point = { self.edit_point with index = 0ul }}
      in
      let adjust = Isize.(adjust -^ (usize_to_isize_safe remaining) -^ 1l) in
      let direction = if Isize.(adjust >=^ 0l) then DForward else DBackward in
      let (self, done) = adjust_selection_for_horizontal_change self direction select in
      if done then self else perform_horizontal_adjustment self adjust select
    else let self = { self with
      edit_point = { self.edit_point with
	index = min_usize (current_line_length self)
	  Usize.(self.edit_point.index +^ (isize_to_usize_safe adjust))
      }
    } in self
  end in
  update_selection_direction self

val adjust_horizontal :
  self:selection ->
  adjust:isize{Isize.(adjust >^ _MIN_ISIZE)} ->
  selection_status ->
  Tot selection
  (decreases (abs_isize adjust))
let adjust_horizontal self adjust select =
  let direction = if Isize.(adjust >=^ 0l) then DForward else DBackward in
  let (self, done) = adjust_selection_for_horizontal_change self direction select in
  if done then self else perform_horizontal_adjustment self adjust select

val adjust_horizontal_to_line_end : selection -> direction -> selection_status -> Tot selection
let adjust_horizontal_to_line_end self dir status =
  let (self, done) = adjust_selection_for_horizontal_change self dir status in
  if not done then
    let shift : isize =
      match dir with
	| DBackward -> Isize.(0l -^ (usize_to_isize_safe self.edit_point.index))
	| DForward -> usize_to_isize_safe
	  Usize.((line_len self.lines self.edit_point.line) -^ self.edit_point.index)
    in
    perform_horizontal_adjustment self shift status
  else self
