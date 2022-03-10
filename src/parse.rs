use std::collections::VecDeque;
use std::fmt;
use std::io;
use std::io::{Error, ErrorKind};

pub struct Stream<'a> {
    chars: VecDeque<u8>,
    line_num: i32,
    stream: &'a mut dyn io::Read,
}

fn is_whitespace(c: u8) -> bool {
    c == b' ' || c == b'\n' || c == b'\t'
}

fn is_digit(c: u8) -> bool {
    c >= b'0' && c <= b'9'
}

fn unexpected(c: u8) -> Error {
    return Error::new(ErrorKind::InvalidInput, format!("unexpected character: {}", c as char))
}

#[derive(Debug)]
pub enum Ast {
    Fixnum(i32),
    Bool(bool),
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ast::Fixnum(n) => f.write_str(&String::from(format!("{}", n))),
            Ast::Bool(b) => {
                if *b {
                    f.write_str("#t")
                } else {
                    f.write_str("#f")
                }
            }
        }
    }
}

impl Stream<'_> {
    pub fn new<'a>(stream: &'a mut dyn io::Read) -> Stream {
        Stream {
            chars: VecDeque::new(),
            line_num: 0,
            stream,
        }
    }

    pub fn read_sexp(&mut self) -> io::Result<Ast> {
        self.eat_whitespace()?;

        let c = self.read_char()?;
        if is_digit(c) || c == b'-' {
            self.unread_char(c);
            let n = self.read_num()?;
            Ok(Ast::Fixnum(n))
        } else if c == b'#' {
            self.unread_char(c);
            let b = self.read_bool()?;
            Ok(Ast::Bool(b))
        } else {
            Err(unexpected(c))
        }
    }

    fn read_bool(&mut self) -> io::Result<bool> {
        // expecting a '#'
        self.expect(b'#')?;

        let b = self.read_char()?;
        if b == b't' {
            Ok(true)
        } else if b == b'f' {
            Ok(false)
        } else {
            Err(unexpected(b))
        }
    }

    fn expect(&mut self, c: u8) -> io::Result<u8> {
        let input = self.read_char()?;

        if input == c {
            Ok(c)
        }
        else {
            Err(unexpected(input))
        }
    }

    fn read_num(&mut self) -> io::Result<i32> {
        let mut acc = String::new();
        let mut c = self.read_char()?;
        if c == b'-' {
            acc.push(c as char);
            c = self.read_char()?;
        }

        while is_digit(c) {
            acc.push(c as char);
            c = self.read_char()?;
        }

        self.unread_char(c);
        Ok(acc.parse().unwrap())
    }

    pub fn read_char(&mut self) -> io::Result<u8> {
        match self.chars.pop_front() {
            Some(c) => Ok(c),
            None => {
                let mut buf = [0];
                self.stream.read(&mut buf[..])?;
                if buf[0] == b'\n' {
                    self.line_num += 1;
                }
                Ok(buf[0])
            }
        }
    }

    pub fn eat_whitespace(&mut self) -> io::Result<()> {
        let mut c = self.read_char()?;
        while is_whitespace(c) {
            c = self.read_char()?;
        }

        Ok(self.unread_char(c))
    }

    pub fn unread_char(&mut self, c: u8) -> () {
        if c == b'\n' {
            self.line_num -= 1;
        }
        self.chars.push_front(c);
    }
}
