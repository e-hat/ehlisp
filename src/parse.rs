use std::cmp::PartialEq;
use std::collections::VecDeque;
use std::fmt;
use std::io;
use std::io::{Error, ErrorKind};
use std::str;

use regex::Regex;

use crate::ast::Ast;
use crate::eval::{Env, Result as EvalResult};
use crate::gc::{Gc, GcGraphNode, GcHandle};

// Stream that is parsed from
pub struct Stream<'a> {
    chars: VecDeque<u8>,
    line_num: i32,
    stream: &'a mut dyn io::Read,
}

// Random parsing helpers
fn is_whitespace(c: u8) -> bool {
    c == b' ' || c == b'\n' || c == b'\t'
}

fn try_digit_start(c: u8, stream: &mut Stream) -> io::Result<bool> {
    if is_digit(c) {
        Ok(true)
    } else if c == b'-' {
        let next = stream.read_char()?;
        stream.unread_char(next);
        Ok(is_digit(next))
    } else {
        Ok(false)
    }
}

fn is_digit(c: u8) -> bool {
    c >= b'0' && c <= b'9'
}

fn is_id_viable(c: u8) -> bool {
    let re = Regex::new(r"[^\s\d\(\)]").unwrap();

    re.is_match(str::from_utf8(&[c]).unwrap())
}

fn unexpected(c: u8) -> Error {
    return Error::new(
        ErrorKind::InvalidInput,
        format!("unexpected character: {}", c as char),
    );
}

// S-expression data type.
// Obj::Primitive and Obj::Closure are never actually constructed directly in the parser. These
// only appear during evaluation.
pub enum Obj {
    Fixnum(i32),
    Bool(bool),
    Local(String),
    Nil,
    Pair(GcHandle<Obj>, GcHandle<Obj>),
    Primitive(
        String,
        fn(Vec<GcHandle<Obj>>, &mut Gc) -> EvalResult<GcHandle<Obj>>,
    ),
    Quote(GcHandle<Obj>),
    Closure {
        formal_args: Vec<String>,
        rhs: GcHandle<Ast>,
        env: Env,
    },
}

impl GcGraphNode for Obj {
    fn neighbors(&self) -> Vec<Box<dyn GcGraphNode>> {
        let res: Vec<Box<dyn GcGraphNode>> = Vec::new();
        res
    }
}

impl Stream<'_> {
    pub fn new<'a>(stream: &'a mut dyn io::Read) -> Stream<'a> {
        Stream {
            chars: VecDeque::new(),
            line_num: 0,
            stream,
        }
    }

    pub fn read_sexp(&mut self, gc: &mut Gc) -> io::Result<GcHandle<Obj>> {
        self.eat_whitespace()?;

        let c = self.read_char()?;
        if try_digit_start(c, self)? {
            self.unread_char(c);
            self.read_num().map(|n| gc.new_obj(Obj::Fixnum(n)))
        } else if c == b'#' {
            self.unread_char(c);
            self.read_bool().map(|b| gc.new_obj(Obj::Bool(b)))
        } else if c == b'\'' {
            self.read_sexp(gc).map(|q| gc.new_obj(Obj::Quote(q)))
        } else if is_id_viable(c) {
            self.unread_char(c);
            self.read_id().map(|l| gc.new_obj(Obj::Local(l)))
        } else if c == b'(' {
            self.read_list(gc)
        } else {
            Err(unexpected(c))
        }
    }

    fn read_list(&mut self, gc: &mut Gc) -> io::Result<GcHandle<Obj>> {
        self.eat_whitespace()?;

        let c = self.read_char()?;
        if c == b')' {
            Ok(gc.new_obj(Obj::Nil))
        } else {
            self.unread_char(c);
            let car = self.read_sexp(gc)?;
            let cdr = self.read_list(gc)?;

            Ok(gc.new_obj(Obj::Pair(car, cdr)))
        }
    }

    fn read_id(&mut self) -> io::Result<String> {
        let re = Regex::new(r"^[^\s\d\(\)]*$").unwrap();

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
            Obj::Primitive(name, _) => f.write_str(&format!("#<primitive:{}>", name)),
            Obj::Quote(inner) => f.write_str(&format!("'{}", inner.get().borrow())),
            Obj::Closure { .. } => f.write_str("#<closure>"),
        }
    }
}

impl fmt::Debug for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&format!("{}", self))
    }
}

// For testing purposes. This compares the values inside the S-expressions, not their pointers.
// Also, this is not at all related to evaluation. For example, if x = 5, then Obj::Local("x") and
// Obj::Fixnum(5) would NOT be equal. An Obj::Local can't be equal to an Obj::Fixnum.
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
                    lcar.get().borrow().eq(&rcar.get().borrow())
                        && lcdr.get().borrow().eq(&*rcdr.get().borrow())
                } else {
                    false
                }
            }
            Obj::Primitive(_, _) => false,
            Obj::Quote(self_inner) => {
                if let Obj::Quote(other_inner) = other {
                    &*self_inner.get().borrow() == &*other_inner.get().borrow()
                } else {
                    false
                }
            }
            Obj::Closure {
                formal_args,
                rhs,
                env,
            } => {
                if let Obj::Closure {
                    formal_args: formal_args_other,
                    rhs: rhs_other,
                    env: env_other,
                } = other
                {
                    formal_args == formal_args_other
                        && &*rhs.get().borrow() == &*rhs_other.get().borrow()
                        && env == env_other
                } else {
                    false
                }
            }
        }
    }
}

impl Obj {
    // Maybe this could be more ergonomic if there was a `try_list` function, that would return
    // Option<Vec<wrap_t!(Obj)>> that would return Some if the Sexp was a valid list, None
    // otherwise.
    pub fn is_list(&self) -> bool {
        match self {
            Obj::Nil => true,
            Obj::Pair(_, r) => r.get().borrow().is_list(),
            _ => false,
        }
    }

    fn print_list(&self) -> String {
        match self {
            Obj::Pair(l, rp) => {
                let rp_handle = rp.get();
                let child_ref = rp_handle.borrow();
                let l_handle = l.get();
                let l_ref = l_handle.borrow();
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
            Obj::Pair(l, r) => format!("{} . {}", l.get().borrow(), r.get().borrow()),
            _ => panic!("Inconceivable!"),
        }
    }

    pub fn to_vec(&self) -> Vec<GcHandle<Obj>> {
        match self {
            Obj::Pair(car, cdr) => {
                let mut res = vec![car.clone()];
                let mut tail = cdr.get().borrow().to_vec();
                res.append(&mut tail);
                res
            }
            Obj::Nil => Vec::new(),
            _ => unreachable!(),
        }
    }

    pub fn from_vec(items: &Vec<GcHandle<Obj>>, gc: &mut Gc) -> GcHandle<Obj> {
        if items.len() == 0 {
            gc.new_obj(Obj::Nil)
        } else {
            let head = gc.new_obj(Obj::Nil);
            let mut tail = head.clone();
            for obj in items {
                let new_tail = gc.new_obj(Obj::Nil);
                let new = Obj::Pair(obj.clone(), new_tail.clone());
                tail.get().replace(new);
                tail = new_tail.clone();
            }

            head
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::assert;
    use std::cell::RefCell;
    use std::rc::Rc;

    use crate::gc::{Gc, GcHandle, GcData};
    use crate::handle;

    macro_rules! test_case {
        ($name:ident, $input:expr, $expected:expr) => {
            #[test]
            fn $name() {
                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);

                let mut gc = Gc::new();

                let res = stream.read_sexp(&mut gc);
                assert!(!res.is_err());
                assert_eq!(&*res.unwrap().get().borrow(), &$expected);
            }
        };
    }

    test_case!(fixnum_positive, "1", Obj::Fixnum(1));
    test_case!(fixnum_negative, "-1", Obj::Fixnum(-1));

    test_case!(bool_true, "#t", Obj::Bool(true));
    test_case!(bool_false, "#f", Obj::Bool(false));

    test_case!(
        local,
        "+-/\\whatever_^%$#@!&*[]{}:;'\"\n",
        Obj::Local(String::from("+-/\\whatever_^%$#@!&*[]{}:;'\""))
    );

    test_case!(nil, "()", Obj::Nil);

    test_case!(
        quote,
        "'a'\n",
        Obj::Quote(handle!(Obj::Local("a'".to_string())))
    );
}
