module TextInput

open FStar.List.Tot.Base
module U = FStar.UInt32
module I = FStar.Int32

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

type usize = U.t
type isize = I.t

let max_usize = UInt.max_int U.n
let max_isize = Int.max_int I.n

let u_to_i (x: usize{U.v x <= max_isize}) = I.int_to_t (U.v x)
let i_to_u (x: isize{I.v x >= 0}) = U.uint_to_t (I.v x)
let max_int (x y : isize) = I.(if x >=^ y then x else y)
let min_uint (x y : usize) = U.(if x <=^ y then x else y)
let abs_int (x: isize) : nat = I.(if x >=^ 0l then v x else - v x)

type small_usize = x:usize{ U.v x + 1 <= max_isize }

type text_point = {
  line: small_usize;
  index: small_usize;
}
val point_lte : text_point -> text_point -> Tot bool
let point_lte p1 p2 =
  U.(p1.line <^ p2.line) ||
  U.((p1.line =^ p2.line && p1.index <=^ p2.index))

type selection_state = {
  start: text_point;
  final: text_point;
  direction: selection_direction
}

type line_string = s:string{FStar.String.strlen s + 1 <= Int.max_int 32}


let text_total_chars (text:list line_string) =
  fold_left (fun acc (line : line_string) -> acc + 1 + FStar.String.strlen line) 0 text

type text = t:list line_string{length t + 1 <= max_isize && text_total_chars t <= max_isize}

val text_length : text -> Tot usize
let text_length text = U.uint_to_t (length text)

val line_length : text:text -> i:usize{U.(i <^ (text_length text))} -> Tot usize
let line_length t i = U.uint_to_t (FStar.String.strlen (index t (U.v i)))

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
      U.(start.line <^ (text_length input.lines)) &&
      U.(start.index <=^ (line_length input.lines start.line)) &&
      begin match input.selection_direction with
	| Unspecified | Forward -> point_lte start input.edit_point
	| Backward -> point_lte input.edit_point start
      end
    | None -> true
  end

val assert_ok_selection : text_input -> Tot bool
let assert_ok_selection input =
  assert_edit_order input &&
  U.(input.edit_point.line <^ (text_length input.lines)) &&
  U.(input.edit_point.index <=^ (line_length input.lines input.edit_point.line))

type selection = input:text_input{assert_ok_selection input}

type valid_text_point (input:selection) = p:text_point{
  U.(p.line <^ text_length input.lines) &&
  U.(p.index <=^ (line_length input.lines p.line))
}

val current_line_length :
  input:text_input{U.v input.edit_point.line < U.v (text_length input.lines)} ->
  usize
let current_line_length input = line_length input.lines input.edit_point.line

val clear_selection : selection -> Tot selection
let clear_selection input =
  { input with
    selection_origin = None;
    selection_direction = Unspecified;
  }

val select_all : selection -> Tot selection
let select_all input =
  let last_line = U.(text_length input.lines -^ 1ul) in
  { input with
    selection_origin = Some({ line = 0ul; index = 0ul });
    edit_point = { line = last_line; index = line_length input.lines last_line};
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
        line = U.((text_length input.lines) -^ 1ul);
	index = line_length input.lines U.((text_length input.lines) -^ 1ul)
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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val adjust_vertical :
  input:selection ->
  adjust:isize{(I.v adjust) + (U.v input.edit_point.line) + 1 <= max_isize} ->
  selection_status ->
  selection
let adjust_vertical input adjust select =
  let input = match (select, input.selection_origin) with
    | (Selected, None) -> { input with selection_origin = Some(input.edit_point) }
    | (Selected, Some _) -> input
    | (NotSelected, _) -> clear_selection input
  in
  assert (U.(input.edit_point.line <^ text_length input.lines));
  let target_line : isize = I.((u_to_i input.edit_point.line) +^ adjust) in
  if I.(target_line <^ 0l) then
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
  else if U.((i_to_u target_line) >=^ text_length input.lines) then begin
    let input = { input with edit_point = { input.edit_point with
      line = U.((text_length input.lines) -^ 1ul);
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
    let target_line_length =  line_length input.lines (i_to_u target_line) in
    let col = if U.(input.edit_point.index <^ target_line_length)
      then input.edit_point.index
      else target_line_length
    in
    let input =
    { input with edit_point = {
      line = i_to_u target_line;
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

val perform_horizontal_adjustment :
  input:selection ->
  adjust:isize{(I.v adjust) + (U.v input.edit_point.index) + 1 <= max_isize} ->
  selection_status ->
  Tot selection
  (decreases (abs_int adjust))
let rec perform_horizontal_adjustment input adjust select =
  let input = if I.(adjust <^ 0l) then begin
    let adjust_abs = U.uint_to_t (- (I.v adjust)) in
    let remaining = input.edit_point.index in
    if U.(adjust_abs >^ remaining) && U.(input.edit_point.line >^ 0ul) then
      let input = adjust_vertical input (-1l) select in
      let input =
	{ input with edit_point = { input.edit_point with index = current_line_length input }}
      in
      assert (assert_edit_order input);
      (* BEGIN CHANGED CODE *)
      (* Could not prove mutually recursive function termination so inlined other function here *)
      //adjust_horizontal input I.(adjust +^ ((u_to_i remaining) +^ 1l)) select
      let adjust = I.(adjust +^ ((u_to_i remaining) +^ 1l)) in
      let direction = if I.(adjust >=^ 0l) then DForward else DBackward in
      let (input, done) = adjust_selection_for_horizontal_change input direction select in
      if done then input else perform_horizontal_adjustment input adjust select
      (* END CHANGED CODE*)
    else
      { input with edit_point = { input.edit_point with index =
        i_to_u (max_int 0l I.((u_to_i input.edit_point.index) +^ adjust))
      } }
  end else begin
    let remaining = U.((current_line_length input) -^ input.edit_point.index) in
    if
      U.((i_to_u adjust) >^ remaining) &&
      U.(text_length input.lines >^ input.edit_point.line +^ 1ul)
    then
      let input = adjust_vertical input 1l select in
      let input =
	{ input with edit_point = { input.edit_point with index = 0ul }}
      in
      (* BEGIN CHANGED CODE *)
      (* Could not prove mutually recursive function termination so inlined other function here *)
      //adjust_horizontal input I.(adjust -^ (u_to_i remaining) -^ 1l) select
      let adjust = I.(adjust -^ (u_to_i remaining) -^ 1l) in
      let direction = if I.(adjust >=^ 0l) then DForward else DBackward in
      let (input, done) = adjust_selection_for_horizontal_change input direction select in
      if done then input else perform_horizontal_adjustment input adjust select
      (* END CHANGED CODE*)
    else { input with
      edit_point = { input.edit_point with
	index = min_uint (current_line_length input) U.(input.edit_point.index +^ (i_to_u adjust))
      }
    }
  end in
  update_selection_direction input

val adjust_horizontal :
  input:selection ->
  adjust:isize{(I.v adjust) + (U.v input.edit_point.index) + 1 <= max_isize} ->
  selection_status ->
  Tot selection
  (decreases (abs_int adjust))
let adjust_horizontal input adjust select =
  let direction = if I.(adjust >=^ 0l) then DForward else DBackward in
  let (input, done) = adjust_selection_for_horizontal_change input direction select in
  if done then input else perform_horizontal_adjustment input adjust select

val adjust_horizontal_to_line_end : selection -> direction -> selection_status -> Tot selection
let adjust_horizontal_to_line_end input dir status =
  let (input, done) = adjust_selection_for_horizontal_change input dir status in
  if done then input else
    let shift : isize =
      let current_line = index input.lines (U.v input.edit_point.line) in
      match dir with
	| DBackward -> I.(0l -^ (u_to_i input.edit_point.index))
	| DForward -> u_to_i U.((line_length input.lines input.edit_point.line) -^ input.edit_point.index)
    in
    perform_horizontal_adjustment input shift status

let decr (x:nat{x > 0}) : nat = x - 1

type offset (t:text) = n:small_usize{U.v n <= text_total_chars t}

val offset_to_text_point :
  input:selection ->
  abs_point:offset input.lines ->
  Tot (valid_text_point input)
let offset_to_text_point input abs_point =
  let len = text_length input.lines in
  let last_line_idx = U.(len -^ 1ul) in
  let (| line, index, _, _ |) = fold_left (fun
    ((| line, index, i, acc|) :
      ( (line:small_usize{U.(line <^ len)})
	& small_usize
	& (i:nat{U.v line <= i && i < U.v len})
	& (acc:small_usize)
      ))
    (text_line : line_string) ->
    assert U.(line <^ text_length input.lines);
    if i <> U.v last_line_idx then
      let line_end = U.uint_to_t (FStar.String.strlen text_line) in
      let new_acc = U.(acc +^ line_end +^ 1ul) in
      assume (U.v new_acc + 1 <= max_isize);
      if U.(abs_point >=^ new_acc) && U.(index >^ line_end) then begin
	(| U.(line +^ 1ul), U.(index -^ (line_end +^ 1ul)), i + 1, new_acc |)
      end else
	(| line, index, i + 1, new_acc |)
    else (| line, index, i, acc |)
  ) (| 0ul, abs_point, 0, 0ul |) (input.lines)
  in
  admit();
  { line; index }

(* BEGIN CHANGED CODE *)
val offset_to_text_point_alt :
  input:selection ->
  abs_point:offset input.lines ->
  Tot (valid_text_point input)
let offset_to_text_point_alt input abs_point =
  let total_length = U.uint_to_t (text_total_chars input.lines) in
  let total_lines = text_length input.lines in
  let (| stopped, remainder, line, index |) = fold_left (fun
    ((| stopped, remainder, line, index|) :
      (stopped: bool)
      & (remainder:small_usize)
      & (line:small_usize{U.(line <^ total_lines)})
      & (index:small_usize{stopped ==> U.(index <=^ line_length input.lines line)})
    )
    (text_line:line_string) ->
    let line_length = U.uint_to_t (FStar.String.strlen text_line) in
    if U.(remainder >^ line_length) then
      let new_line = if U.(line >=^ (total_lines -^ 1ul)) then line else U.(line +^ 1ul) in
      (| false, U.(remainder -^ line_length -^ 1ul), new_line, index |)
    else begin
      assume (text_line = FStar.List.Tot.index input.lines (U.v line));
      (| true, 0ul, line, remainder |)
    end
  ) (| false, abs_point, 0ul, 0ul |) input.lines
  in
  if stopped then begin
    { line; index }
  end else
    { line = U.(total_lines -^ 1ul); index = line_length input.lines U.(total_lines -^ 1ul) }
(* END CHANGED CODE *)

let offset_to_text_point_monotonicity
  (input:selection)
  (x: offset input.lines)
  (y: offset input.lines{U.(x <=^ y)})
  : Lemma (ensures
    (point_lte (offset_to_text_point_alt input x) (offset_to_text_point_alt input y))
  )
  =
  let point_x = offset_to_text_point_alt input x in
  let point_y = offset_to_text_point_alt input y in
  (* How to prove the monotonicity of the function ? *)
  assume U.(point_x.line <=^ point_y.line);
  if U.(point_x.line =^ point_y.line) then
    assume U.(point_x.index <=^ point_y.index);
  ()

val set_selection_range:
  input:selection ->
  start:offset input.lines ->
  final:offset input.lines ->
  selection_direction ->
  selection
let set_selection_range input start final dir =
  let text_end = U.uint_to_t (text_total_chars input.lines) in
  let final : offset input.lines = if U.(final >^ text_end) then text_end else final in
  let start : offset input.lines = if U.(start >^ final) then final else start in
  assert U.(start <=^ final);
  let start_p =  offset_to_text_point_alt input start in
  let final_p = offset_to_text_point_alt input final in
  offset_to_text_point_monotonicity input start final;
  let input = { input with selection_direction = dir } in
  match dir with
  | Unspecified | Forward ->
    { input with
      selection_origin = Some(start_p);
      edit_point = final_p;
    }
  | Backward ->
    { input with
      selection_origin = Some(final_p);
      edit_point = start_p;
    }