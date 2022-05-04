use std::cell::RefCell;
use std::cmp::PartialEq;
use std::fmt;
use std::rc::Rc;

use crate::parse::Obj;

#[derive(Debug)]
pub enum Ast {
    Literal(Rc<RefCell<Obj>>),
    Var(String),
    If {
        pred: Rc<RefCell<Ast>>,
        cons: Rc<RefCell<Ast>>,
        alt: Rc<RefCell<Ast>>,
    },
    And {
        l: Rc<RefCell<Ast>>,
        r: Rc<RefCell<Ast>>,
    },
    Or {
        l: Rc<RefCell<Ast>>,
        r: Rc<RefCell<Ast>>,
    },
    Apply {
        l: Rc<RefCell<Ast>>,
        r: Rc<RefCell<Ast>>,
    },
    Call {
        f: Rc<RefCell<Ast>>,
        args: Vec<Rc<RefCell<Ast>>>,
    },
    DefAst(Def),
}

#[derive(Debug)]
pub enum Def {
    Val { name: String, rhs: Rc<RefCell<Ast>> },
    Ast(Rc<RefCell<Ast>>),
}

type Error = String;
pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ast::Literal(obj) => f.write_str(&format!("{}", obj.borrow())),
            Ast::Var(name) => f.write_str(&format!("var: {}", name)),
            Ast::If { pred, cons, alt } => f.write_str(&format!(
                "if {}\nthen\n{}\nelse\n{}",
                pred.borrow(),
                cons.borrow(),
                alt.borrow()
            )),
            Ast::And { l, r } => f.write_str(&format!("( {} ) and ( {} )", l.borrow(), r.borrow())),
            Ast::Or { l, r } => f.write_str(&format!("( {} ) or ( {} )", l.borrow(), r.borrow())),
            Ast::Apply { l, r } => f.write_str(&format!("( {} ) apply ( {} )", l.borrow(), r.borrow())),
            Ast::Call { f: func, args } => {
                let mut arg_str = String::from(" ");
                for arg in args {
                    arg_str.push_str(&format!("{} ", arg.borrow()));
                }
                f.write_str(&format!("call ( {} ) ({})", func.borrow(), arg_str))
            }
            Ast::DefAst(def) => f.write_str(&format!("def {}", def)),
        }
    }
}

impl fmt::Display for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Def::Val { name, rhs } => f.write_str(&format!("let {} = {}", name, rhs.borrow())),
            Def::Ast(ast) => f.write_str(&format!("{}", ast.borrow())),
        }
    }
}

impl Ast {
    pub fn from_sexp(sexp: Rc<RefCell<Obj>>) -> Result<Rc<RefCell<Ast>>> {
        match &*sexp.borrow() {
            Obj::Fixnum(_) => Ok(Rc::new(RefCell::new(Ast::Literal(sexp.clone())))),
            Obj::Bool(_) => Ok(Rc::new(RefCell::new(Ast::Literal(sexp.clone())))),
            Obj::Local(name) => Ok(Rc::new(RefCell::new(Ast::Var(name.to_string())))),
            Obj::Nil => Ok(Rc::new(RefCell::new(Ast::Literal(sexp.clone())))),
            Obj::Primitive(f, _) => Err(format!("Unexpected Primitive sexp '{}'", f)),
            Obj::Pair(_, _) => {
                if sexp.borrow().is_list() {
                    let items = sexp.borrow().to_vec();
                    // A previous pattern match proved that this sexp is NOT Obj::Nil
                    // Therefore items.len() >= 1
                    let x = if let Obj::Local(first_word) = &*items[0].borrow() {
                        match first_word.as_str() {
                            "if" => {
                                if items.len() != 4 {
                                    Err("expected form (if (pred) (cons) (alt))".to_string())
                                } else {
                                    Ok(Rc::new(RefCell::new(Ast::If {
                                        pred: Ast::from_sexp(items[1].clone())?,
                                        cons: Ast::from_sexp(items[2].clone())?,
                                        alt: Ast::from_sexp(items[3].clone())?,
                                    })))
                                }
                            }
                            "and" => {
                                if items.len() != 3 {
                                    Err("expected form (and (l) (r))".to_string())
                                } else {
                                    Ok(Rc::new(RefCell::new(Ast::And {
                                        l: Ast::from_sexp(items[1].clone())?,
                                        r: Ast::from_sexp(items[2].clone())?,
                                    })))
                                }
                            }
                            "or" => {
                                if items.len() != 3 {
                                    Err("expected form (or (l) (r))".to_string())
                                } else {
                                    Ok(Rc::new(RefCell::new(Ast::Or {
                                        l: Ast::from_sexp(items[1].clone())?,
                                        r: Ast::from_sexp(items[2].clone())?,
                                    })))
                                }
                            }
                            "val" => {
                                if items.len() != 3 {
                                    Err("expected form (val (name) (expr))".to_string())
                                } else {
                                    if let Obj::Local(name) = &*items[1].borrow() {
                                        Ok(Rc::new(RefCell::new(Ast::DefAst(Def::Val {
                                            name: name.to_string(),
                                            rhs: Ast::from_sexp(items[2].clone())?,
                                        }))))
                                    } else {
                                        Err("expected `name` to be a string in form (val (name) (expr))".to_string())
                                    }
                                }
                            }
                            "apply" => {
                                if items.len() != 3 || !items[2].borrow().is_list() {
                                    Err("expected form (apply (fnexpr) (args list))".to_string())
                                } else {
                                    Ok(Rc::new(RefCell::new(Ast::Apply {
                                        l: Ast::from_sexp(items[1].clone())?.clone(),
                                        r: Ast::from_sexp(items[2].clone())?.clone(),
                                    })))
                                }
                            }
                            _ => {
                                let mut args = Vec::new();
                                args.reserve(items.len());
                                for arg in items[1..].into_iter() {
                                    args.push(Ast::from_sexp(arg.clone())?);
                                }
                                Ok(Rc::new(RefCell::new(Ast::Call {
                                    f: Ast::from_sexp(items[0].clone())?,
                                    args,
                                })))
                            }
                        }
                    } else {
                        let mut args = Vec::new();
                        args.reserve(items.len() - 1);
                        for arg in items[1..].into_iter() {
                            args.push(Ast::from_sexp(arg.clone())?);
                        }
                        Ok(Rc::new(RefCell::new(Ast::Call {
                            f: Ast::from_sexp(items[0].clone())?,
                            args,
                        })))
                    };
                    x
                } else {
                    // TODO: How does this work?
                    Ok(Rc::new(RefCell::new(Ast::Literal(sexp.clone()))))
                }
            }
        }
    }
}

impl PartialEq for Ast {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Ast::Literal(l) => {
                if let Ast::Literal(r) = other {
                    l == r
                } else {
                    false
                }
            }
            Ast::Var(l) => {
                if let Ast::Var(r) = other {
                    l == r
                } else {
                    false
                }
            }
            Ast::If {
                pred: lpred,
                cons: lcons,
                alt: lalt,
            } => {
                if let Ast::If {
                    pred: rpred,
                    cons: rcons,
                    alt: ralt,
                } = other
                {
                    lpred == rpred && lcons == rcons && lalt == ralt
                } else {
                    false
                }
            }
            Ast::And { l: ll, r: lr } => {
                if let Ast::And { l: rl, r: rr } = other {
                    ll == rl && lr == rr
                } else {
                    false
                }
            }
            Ast::Or { l: ll, r: lr } => {
                if let Ast::Or { l: rl, r: rr } = other {
                    ll == rl && lr == rr
                } else {
                    false
                }
            }
            Ast::Apply { l: ll, r: lr } => {
                if let Ast::Apply { l: rl, r: rr } = other {
                    ll == rl && lr == rr
                } else {
                    false
                }
            }
            Ast::Call { f: lf, args: largs } => {
                if let Ast::Call { f: rf, args: rargs } = other {
                    lf == rf && largs == rargs
                } else {
                    false
                }
            }
            Ast::DefAst(l) => {
                if let Ast::DefAst(r) = other {
                    l == r
                } else {
                    false
                }
            }
        }
    }
}

impl PartialEq for Def {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Def::Val {
                name: lname,
                rhs: lrhs,
            } => {
                if let Def::Val {
                    name: rname,
                    rhs: rrhs,
                } = other
                {
                    lname == rname && lrhs == rrhs
                } else {
                    false
                }
            }
            Def::Ast(l) => {
                if let Def::Ast(r) = other {
                    l == r
                } else {
                    false
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::assert;

    use crate::parse::*;
    use crate::wrap;

    macro_rules! gen_test_case {
        ($name:ident, $input:expr, $expected:expr) => {
            #[test]
            fn $name() {
                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);

                let parse_res = stream.read_sexp().unwrap();
                let res = Ast::from_sexp(parse_res);
                assert!(!res.is_err());
                assert_eq!(res.unwrap(), $expected);
            }
        };
    }

    macro_rules! lit_wrap {
        ($x:expr) => {
            wrap!(Ast::Literal(wrap!($x)))
        };
    }

    gen_test_case!(fixnum, "0", lit_wrap!(Obj::Fixnum(0)));
    gen_test_case!(boolean, "#t", lit_wrap!(Obj::Bool(true)));
    gen_test_case!(nil, "()", lit_wrap!(Obj::Nil));

    gen_test_case!(local, "hello\n", wrap!(Ast::Var("hello".to_string())));

    gen_test_case!(
        val,
        "(val x 5)",
        wrap!(Ast::DefAst(Def::Val {
            name: "x".to_string(),
            rhs: lit_wrap!(Obj::Fixnum(5)),
        }))
    );
    gen_test_case!(
        conditional,
        "(if #t 5 6)",
        wrap!(Ast::If {
            pred: lit_wrap!(Obj::Bool(true)),
            cons: lit_wrap!(Obj::Fixnum(5)),
            alt: lit_wrap!(Obj::Fixnum(6)),
        })
    );
    gen_test_case!(
        and,
        "(and #t #f)",
        wrap!(Ast::And {
            l: lit_wrap!(Obj::Bool(true)),
            r: lit_wrap!(Obj::Bool(false)),
        })
    );
    gen_test_case!(
        or,
        "(or #t #f)",
        wrap!(Ast::Or {
            l: lit_wrap!(Obj::Bool(true)),
            r: lit_wrap!(Obj::Bool(false)),
        })
    );
    gen_test_case!(
        apply,
        "(apply f ())",
        wrap!(Ast::Apply {
            l: wrap!(Ast::Var("f".to_string())),
            r: lit_wrap!(Obj::Nil),
        })
    );
    gen_test_case!(
        call_with_fixnum_first,
        "(1 2 3)",
        wrap!(Ast::Call {
            f: lit_wrap!(Obj::Fixnum(1)),
            args: vec![lit_wrap!(Obj::Fixnum(2)), lit_wrap!(Obj::Fixnum(3))],
        })
    );
    gen_test_case!(
        call,
        "(f 1 2)",
        wrap!(Ast::Call {
            f: wrap!(Ast::Var("f".to_string())),
            args: vec![lit_wrap!(Obj::Fixnum(1)), lit_wrap!(Obj::Fixnum(2))],
        })
    );
}
