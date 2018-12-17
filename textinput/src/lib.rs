/// This code is  inspired by Servo's bloom filter implementation
/// contained in the file
/// [`servo/script/textinput.rs`](https://github.com/servo/servo/blob/master/components/script/textinput.rs)
use std::marker::PhantomData;

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

/// The direction in which to delete a character.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum Direction {
    Forward,
    Backward,
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct TextPoint {
    /// 0-based line number
    pub line: usize,
    /// 0-based column number in UTF-8 bytes
    pub index: usize,
}

#[derive(Clone, Copy, PartialEq)]
pub struct SelectionState {
    start: TextPoint,
    end: TextPoint,
    direction: SelectionDirection,
}

pub struct DOMString(String, PhantomData<*const ()>);

impl DOMString {
    fn len(&self) -> usize {
        self.0.len()
    }
}

fn number_of_lines(t: &Vec<DOMString>) -> usize {
    t.len()
}

type Text = Vec<DOMString>;

fn line_len(t: &Text, i: usize) -> usize {
    t[i].len()
}

pub struct TextInput {
    /// Current text input content, split across lines without trailing '\n'
    lines: Vec<DOMString>,

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
                        begin <= self.edit_point
                    }
                    SelectionDirection::Backward => self.edit_point <= begin,
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
                    self.edit_point.index = line_len (&self.lines, number_of_lines(&self.lines) - 1);
                }
            }
        }
    }
}
