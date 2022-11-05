use std::fs::File;
use utf8_chars::BufReadCharsExt;
use std::collections::VecDeque;
use std::io::BufReader;

pub trait CharStream {
    // Stores a char, returned on first next()
    fn put_front(&mut self, ch: char);

    // Reads next char
    fn next(&mut self) -> Option<char>;

    // Reads next char but skips newspace
    fn skip(&mut self) -> Option<char> {
        while let Some(ch) = self.next() {
            if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' { continue; }
            return Some(ch)
        }
        None
    }
}

pub struct FileStream {
    buf: BufReader<File>,
    next: Option<char>,
}

impl CharStream for FileStream {
    fn put_front(&mut self, ch: char) {
        assert!(self.next.is_none());
        self.next = Some(ch);
    }

    fn next(&mut self) -> Option<char> {
        if let Some(ch) = self.next {
            self.next = None;
            return Some(ch)
        }

        if let Ok(x) = self.buf.read_char_raw() {
            x
        } else {
            None
        }
    }
}

impl FileStream {
    pub fn new(file: File) -> FileStream {
        let buf = BufReader::new(file);
        Self{ buf, next: None }
    }
}

pub struct StringStream {
    chars: VecDeque<char>,
    next: Option<char>,
}

impl CharStream for StringStream {
    fn put_front(&mut self, ch: char) {
        assert!(self.next.is_none());
        self.next = Some(ch);
    }

    fn next(&mut self) -> Option<char> {
        if let Some(ch) = self.next {
            self.next = None;
            return Some(ch)
        }
        self.chars.pop_front()
    }
}

impl StringStream {
    pub fn new(s: &str) -> StringStream {
        let chars: VecDeque<_> = s.chars().collect();
        Self{ chars, next: None }
    }
}
