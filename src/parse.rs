use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::VecDeque;
use std::fmt;
use std::io;
use std::io::{Error, ErrorKind};
use std::rc::Rc;
use std::str;

use regex::Regex;

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

fn is_alpha(c: u8) -> bool {
    let re = Regex::new(r"[a-zA-Z]").unwrap();

    re.is_match(str::from_utf8(&[c]).unwrap())
}

fn unexpected(c: u8) -> Error {
    return Error::new(
        ErrorKind::InvalidInput,
        format!("unexpected character: {}", c as char),
    );
}

#[derive(Debug)]
pub enum Obj {
    Fixnum(i32),
    Bool(bool),
    Local(String),
    Nil,
    Pair(Rc<RefCell<Obj>>, Rc<RefCell<Obj>>),
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Obj::Fixnum(n) => f.write_str(&format!("{}", n)),
            Obj::Bool(b) => {
                if *b {
                    f.write_str("#t")
                } else {
                    f.write_str("#f")
                }
            }
            Obj::Local(l) => f.write_str(l),
            Obj::Nil => f.write_str("nil"),
            Obj::Pair(_, _) => {
                let mut res = String::from("");

                if self.is_list() {
                    res.push_str(&self.print_list());
                } else {
                    res.push_str(&self.print_pair());
                }

                f.write_str(&format!("({})", res))
            }
        }
    }
}

impl PartialEq for Obj {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Obj::Fixnum(l) => {
                if let Obj::Fixnum(r) = other {
                    l == r
                } else {
                    false
                }
            }
            Obj::Bool(l) => {
                if let Obj::Bool(r) = other {
                    l == r
                } else {
                    false
                }
            }
            Obj::Local(l) => {
                if let Obj::Local(r) = other {
                    l == r
                } else {
                    false
                }
            }
            Obj::Nil => matches!(other, Obj::Nil),
            Obj::Pair(lcar, lcdr) => {
                if let Obj::Pair(rcar, rcdr) = other {
                    lcar.borrow().eq(&rcar.borrow()) && lcdr.borrow().eq(&rcdr.borrow())
                } else {
                    false
                }
            },
        }
    }
}

impl Obj {
    pub fn is_list(&self) -> bool {
        match self {
            Obj::Nil => true,
            Obj::Pair(_, r) => r.borrow().is_list(),
            _ => false,
        }
    }

    fn print_list(&self) -> String {
        match self {
            Obj::Pair(l, rp) => {
                let child_ref = rp.borrow();
                let l_ref = l.borrow();
                match &*child_ref {
                    Obj::Nil => format!("{}", l_ref),
                    r => format!("{} {}", l_ref, r.print_list()),
                }
            }
            _ => panic!("Inconceivable!"),
        }
    }

    fn print_pair(&self) -> String {
        match self {
            Obj::Pair(l, r) => format!("{} . {}", l.borrow(), r.borrow()),
            _ => panic!("Inconceivable!"),
        }
    }

    pub fn to_vec(&self) -> Vec<Rc<RefCell<Obj>>> {
        match self {
            Obj::Pair(car, cdr) => {
                let mut res = vec![car.clone()];
                let mut tail = cdr.borrow().to_vec();
                res.append(&mut tail);
                res
            }
            Obj::Nil => Vec::new(),
            _ => unreachable!(),
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

    pub fn read_sexp(&mut self) -> io::Result<Rc<RefCell<Obj>>> {
        self.eat_whitespace()?;

        let c = self.read_char()?;
        if is_digit(c) || c == b'-' {
            self.unread_char(c);
            self.read_num()
                .map(|n| Rc::new(RefCell::new(Obj::Fixnum(n))))
        } else if c == b'#' {
            self.unread_char(c);
            self.read_bool()
                .map(|b| Rc::new(RefCell::new(Obj::Bool(b))))
        } else if is_alpha(c) {
            self.unread_char(c);
            self.read_id().map(|l| Rc::new(RefCell::new(Obj::Local(l))))
        } else if c == b'(' {
            self.read_list()
        } else {
            Err(unexpected(c))
        }
    }

    fn read_list(&mut self) -> io::Result<Rc<RefCell<Obj>>> {
        self.eat_whitespace()?;

        let c = self.read_char()?;
        if c == b')' {
            Ok(Rc::new(RefCell::new(Obj::Nil)))
        } else {
            self.unread_char(c);
            let car = self.read_sexp()?;
            let cdr = self.read_list()?;

            Ok(Rc::new(RefCell::new(Obj::Pair(car, cdr))))
        }
    }

    fn read_id(&mut self) -> io::Result<String> {
        let re = Regex::new(r"^[a-zA-Z][a-zA-Z0-9_]*$").unwrap();

        self.expect_pattern(&re)
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

    fn expect_pattern(&mut self, re: &Regex) -> io::Result<String> {
        let mut c = self.read_char()?;
        let mut input = String::new();
        input.push(c as char);

        while re.is_match(&input) {
            c = self.read_char()?;
            input.push(c as char);
        }

        self.unread_char(input.pop().unwrap() as u8);
        if input.is_empty() {
            Err(unexpected(c))
        } else {
            Ok(input)
        }
    }

    fn expect(&mut self, c: u8) -> io::Result<u8> {
        let input = self.read_char()?;

        if input == c {
            Ok(c)
        } else {
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
