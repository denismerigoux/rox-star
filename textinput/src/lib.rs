/// This code is  inspired by Servo's bloom filter implementation
/// contained in the file
/// [`servo/script/textinput.rs`](https://github.com/servo/servo/blob/master/components/script/textinput.rs)

extern crate rox_star_lib;

use std::marker::PhantomData;
use rox_star_lib::RoxVec;

#[derive(Clone, Copy, PartialEq)]
pub enum SelectionStatus {
    Selected,
    NotSelected,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SelectionDirection {
    Forward,
    Backward,
    Unspecified,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum Direction {
    Forward,
    Backward,
}

//#[refinement |x| => x.to_nat() <= std::isize::MAX.to_nat()) ]
type SmallUsize = usize;

//#[fstar_prefix "noeq"]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct TextPoint {
    /// 0-based line number
    pub line: SmallUsize,
    /// 0-based column number
    pub index: SmallUsize,
}

impl TextPoint {
    fn lte(&self, other: &TextPoint) -> bool {
        self.line < other.line || (self.line == other.line && self.index <= other.index)
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct SelectionState {
    start: TextPoint,
    end: TextPoint,
    direction: SelectionDirection,
}

//#[assume]
type Pointer = *const ();

//#[refinement (fun s -> s.0.len().to_nat() < std::isize::MAX.to_nat() )]
pub struct DOMString(String, PhantomData<Pointer>);

impl DOMString {
    fn len(&self) -> usize {
        let DOMString(s,_) = &self;
        s.len()
    }
}

fn number_of_lines(t: &RoxVec<DOMString>) -> usize {
    t.len()
}

//#[refinement (fun t -> number_of_lines(t).to_nat() <= std::isize::MAX.to_nat() ]
type Text = RoxVec<DOMString>;

fn line_len(t: &Text, i: usize) -> usize {
    t[i].len()
}

pub struct TextInput {
    /// Current text input content, split across lines without trailing '\n'
    lines: RoxVec<DOMString>,

    /// Current cursor input point
    edit_point: TextPoint,

    /// The current selection goes from the selection_origin until the edit_point. Note that the
    /// selection_origin may be after the edit_point, in the case of a backward selection.
    selection_origin: Option<TextPoint>,
    selection_direction: SelectionDirection,
}

impl TextInput {
    // Check that the selection is valid.
    fn assert_edit_order(&self) -> bool {
        if let Some(begin) = self.selection_origin {
            begin.line < self.lines.len()
                && begin.index <= self.lines[begin.line].len()
                && (match self.selection_direction {
                    SelectionDirection::Unspecified | SelectionDirection::Forward => {
                        begin.lte(&self.edit_point)
                    }
                    SelectionDirection::Backward => self.edit_point.lte(&begin),
                })
        } else {
            true
        }
    }

    fn assert_ok_selection(&self) -> bool {
        self.assert_edit_order()
            && self.edit_point.line < self.lines.len()
            && self.edit_point.index <= self.lines[self.edit_point.line].len()
    }
}

type Selection = TextInput;

impl TextPoint {
    fn is_valid_text_point(&self, input: &TextInput) -> bool {
        self.line < number_of_lines(&input.lines) && self.index <= line_len(&input.lines, self.line)
    }
}

type ValidTextPoint = TextPoint;

impl TextInput {
    fn current_line_length(&self) -> usize {
        line_len(&self.lines, self.edit_point.line)
    }
}

impl Selection {
    pub fn clear_selection(&mut self) {
        self.selection_origin = None;
        self.selection_direction = SelectionDirection::Unspecified;
    }

    pub fn select_all(&mut self) {
        let last_line = number_of_lines(&self.lines) - 1;
        self.selection_origin = Some(TextPoint { line: 0, index: 0 });
        self.edit_point = TextPoint {
            line: last_line,
            index: line_len(&self.lines, last_line),
        };
        self.selection_direction = SelectionDirection::Forward;
    }

    fn selection_origin_or_edit_point(&self) -> ValidTextPoint {
        self.selection_origin.unwrap_or(self.edit_point)
    }

    pub fn selection_start(&self) -> ValidTextPoint {
        match self.selection_direction {
            SelectionDirection::Unspecified | SelectionDirection::Forward => {
                self.selection_origin_or_edit_point()
            }
            SelectionDirection::Backward => self.edit_point,
        }
    }

    pub fn selection_end(&self) -> ValidTextPoint {
        match self.selection_direction {
            SelectionDirection::Unspecified | SelectionDirection::Forward => self.edit_point,
            SelectionDirection::Backward => self.selection_origin_or_edit_point(),
        }
    }

    /// Whether or not there is an active selection (the selection may be zero-length)
    #[inline]
    pub fn has_selection(&self) -> bool {
        self.selection_origin.is_some()
    }

    fn adjust_selection_for_horizontal_change(
        &mut self,
        adjust: Direction,
        select: SelectionStatus,
    ) -> bool {
        if select == SelectionStatus::Selected {
            if self.selection_origin.is_none() {
                self.selection_origin = Some(self.edit_point);
            }
            false
        } else {
            if self.has_selection() {
                self.edit_point = match adjust {
                    Direction::Backward => self.selection_start(),
                    Direction::Forward => self.selection_end(),
                };
                self.clear_selection();
            }
            true
        }
    }

    pub fn adjust_horizontal_to_limit(&mut self, direction: Direction, select: SelectionStatus) {
        if self.adjust_selection_for_horizontal_change(direction, select) {
            ()
        } else {
            match direction {
                Direction::Backward => {
                    self.edit_point.line = 0;
                    self.edit_point.index = 0;
                }
                Direction::Forward => {
                    self.edit_point.line = &self.lines.len() - 1;
                    self.edit_point.index = line_len(&self.lines, number_of_lines(&self.lines) - 1);
                }
            }
        }
    }

    pub fn clear_selection_to_limit(&mut self, direction: Direction) {
        self.clear_selection();
        self.adjust_horizontal_to_limit(direction, SelectionStatus::NotSelected);
    }

    fn update_selection_direction(&mut self) {
        self.selection_direction = if let Some(origin) = self.selection_origin {
            if self.edit_point.lte(&origin) {
                SelectionDirection::Backward
            } else {
                SelectionDirection::Forward
            }
        } else {
            SelectionDirection::Forward
        }
    }

    pub fn adjust_vertical(&mut self, adjust: isize, select: SelectionStatus) {
        if select == SelectionStatus::Selected {
            if self.selection_origin.is_none() {
                self.selection_origin = Some(self.edit_point);
            }
        } else {
            self.clear_selection();
        }

        assert!(self.edit_point.line < number_of_lines(&self.lines));

        let target_line: isize = self.edit_point.line as isize + adjust;

        if target_line < 0 {
            self.edit_point.line = 0;
            self.edit_point.index = 0;
            if self.selection_origin.is_some()
                && (self.selection_direction == SelectionDirection::Unspecified
                    || self.selection_direction == SelectionDirection::Forward)
            {
                self.selection_origin = Some(TextPoint { line: 0, index: 0 });
            }
        } else if target_line as usize >= number_of_lines(&self.lines) {
            self.edit_point.line = self.lines.len() - 1;
            self.edit_point.index = self.current_line_length();
            if self.selection_origin.is_some()
                && (self.selection_direction == SelectionDirection::Backward)
            {
                self.selection_origin = Some(self.edit_point);
            }
        } else {
            let target_line_length = line_len(&self.lines, target_line as usize);
            let col = std::cmp::min(self.edit_point.index, target_line_length);
            self.edit_point.line = target_line as usize;
            self.edit_point.index = col;
            if let Some(origin) = self.selection_origin {
                if ((self.selection_direction == SelectionDirection::Unspecified
                    || self.selection_direction == SelectionDirection::Forward)
                    && self.edit_point.lte(&origin))
                    || (self.selection_direction == SelectionDirection::Backward
                        && origin.lte(&self.edit_point))
                {
                    self.selection_origin = Some(self.edit_point);
                }
            }
        }
    }

    fn perform_horizontal_adjustment(&mut self, adjust: isize, select: SelectionStatus) {
        if adjust < 0 {
            let remaining = self.edit_point.index;
            let neg_val = -adjust;
            let adjust_abs = neg_val as usize;
            if adjust_abs as usize > remaining && self.edit_point.line > 0 {
                self.adjust_vertical(-1, select);
                self.edit_point.index = self.current_line_length();
                let adjust = adjust + remaining as isize + 1;
                let direction = if adjust >= 0 {
                    Direction::Forward
                } else {
                    Direction::Backward
                };
                let done = self.adjust_selection_for_horizontal_change(direction, select);
                if !done {
                    self.perform_horizontal_adjustment(adjust, select);
                }
            } else {
                self.edit_point.index =
                    std::cmp::max(0, self.edit_point.index as isize + adjust) as usize;
            }
        } else {
            let remaining = self.current_line_length() - self.edit_point.index;
            if adjust as usize > remaining && self.lines.len() > self.edit_point.line + 1 {
                self.adjust_vertical(1, select);
                self.edit_point.index = 0;
                // one shift is consumed by the change of line, hence the -1
                let adjust = adjust - remaining as isize - 1;
                let direction = if adjust >= 0 {
                    Direction::Forward
                } else {
                    Direction::Backward
                };
                let done = self.adjust_selection_for_horizontal_change(direction, select);
                if !done {
                    self.perform_horizontal_adjustment(adjust, select);
                }
            } else {
                self.edit_point.index = std::cmp::min(
                    self.current_line_length(),
                    self.edit_point.index + adjust as usize,
                );
            }
        }
        self.update_selection_direction();
    }

    pub fn adjust_horizontal(&mut self, adjust: isize, select: SelectionStatus) {
        let direction = if adjust >= 0 {
            Direction::Forward
        } else {
            Direction::Backward
        };
        if self.adjust_selection_for_horizontal_change(direction, select) {
            return;
        }
        self.perform_horizontal_adjustment(adjust, select);
    }

    pub fn adjust_horizontal_to_line_end(&mut self, direction: Direction, select: SelectionStatus) {
        let done = self.adjust_selection_for_horizontal_change(direction, select);
        if !done {
            let shift: isize = {
                match direction {
                    Direction::Backward => -(self.edit_point.index as isize),
                    Direction::Forward => {
                        (line_len(&self.lines, self.edit_point.line) - self.edit_point.index)
                            as isize
                    }
                }
            };
            self.perform_horizontal_adjustment(shift, select);
        }
    }
}
