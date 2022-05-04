use std::cell::RefCell;
use std::cmp::PartialEq;
use std::fmt;
use std::rc::Rc;

use crate::parse::Obj;
use crate::{wrap, wrap_t};

#[derive(Debug)]
pub enum Ast {
    Literal(wrap_t!(Obj)),
    Var(String),
    If {
        pred: wrap_t!(Ast),
        cons: wrap_t!(Ast),
        alt: wrap_t!(Ast),
    },
    And {
        l: wrap_t!(Ast),
        r: wrap_t!(Ast),
    },
    Or {
        l: wrap_t!(Ast),
        r: wrap_t!(Ast),
    },
    Apply {
        l: wrap_t!(Ast),
        r: wrap_t!(Ast),
    },
    Call {
        f: wrap_t!(Ast),
        args: Vec<wrap_t!(Ast)>,
    },
    Lambda {
        formal_args: Vec<String>,
        rhs: wrap_t!(Ast),
    },
    DefAst(Def),
}

#[derive(Debug)]
pub enum Def {
    Val { name: String, rhs: wrap_t!(Ast) },
    Ast(wrap_t!(Ast)),
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
            Ast::Apply { l, r } => {
                f.write_str(&format!("( {} ) apply ( {} )", l.borrow(), r.borrow()))
            }
            Ast::Call { f: func, args } => {
                let mut arg_str = String::from(" ");
                for arg in args {
                    arg_str.push_str(&format!("{} ", arg.borrow()));
                }
                f.write_str(&format!("call ( {} ) ({})", func.borrow(), arg_str))
            }
            Ast::DefAst(def) => f.write_str(&format!("def {}", def)),
            Ast::Lambda { .. } => f.write_str(&format!("#<lambda>")),
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
    pub fn from_sexp(sexp: wrap_t!(Obj)) -> Result<wrap_t!(Ast)> {
        match &*sexp.borrow() {
            Obj::Fixnum(_) => Ok(wrap!(Ast::Literal(sexp.clone()))),
            Obj::Bool(_) => Ok(wrap!(Ast::Literal(sexp.clone()))),
            Obj::Local(name) => Ok(wrap!(Ast::Var(name.to_string()))),
            Obj::Nil => Ok(wrap!(Ast::Literal(sexp.clone()))),
            Obj::Quote(_) => Ok(wrap!(Ast::Literal(sexp.clone()))),
            Obj::Primitive(f, _) => Err(format!("Unexpected Primitive sexp '{}'", f)),
            Obj::Closure { .. } => Err("Unexpected closure".to_string()),
            Obj::Pair(..) => {
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
                                    Ok(wrap!(Ast::If {
                                        pred: Ast::from_sexp(items[1].clone())?,
                                        cons: Ast::from_sexp(items[2].clone())?,
                                        alt: Ast::from_sexp(items[3].clone())?,
                                    }))
                                }
                            }
                            "and" => {
                                if items.len() != 3 {
                                    Err("expected form (and (l) (r))".to_string())
                                } else {
                                    Ok(wrap!(Ast::And {
                                        l: Ast::from_sexp(items[1].clone())?,
                                        r: Ast::from_sexp(items[2].clone())?,
                                    }))
                                }
                            }
                            "or" => {
                                if items.len() != 3 {
                                    Err("expected form (or (l) (r))".to_string())
                                } else {
                                    Ok(wrap!(Ast::Or {
                                        l: Ast::from_sexp(items[1].clone())?,
                                        r: Ast::from_sexp(items[2].clone())?,
                                    }))
                                }
                            }
                            "val" => {
                                if items.len() != 3 {
                                    Err("expected form (val (name) (expr))".to_string())
                                } else {
                                    if let Obj::Local(name) = &*items[1].borrow() {
                                        Ok(wrap!(Ast::DefAst(Def::Val {
                                            name: name.to_string(),
                                            rhs: Ast::from_sexp(items[2].clone())?,
                                        })))
                                    } else {
                                        Err("expected `name` to be a string in form (val (name) (expr))".to_string())
                                    }
                                }
                            }
                            "apply" => {
                                if items.len() != 3 {
                                    Err("expected form (apply (fnexpr) (args list))".to_string())
                                } else {
                                    Ok(wrap!(Ast::Apply {
                                        l: Ast::from_sexp(items[1].clone())?.clone(),
                                        r: Ast::from_sexp(items[2].clone())?.clone(),
                                    }))
                                }
                            }
                            "lambda" => {
                                if items.len() != 3 || !items[1].borrow().is_list() {
                                    Err("expected form (lambda (formal args) body)".to_string())
                                } else {
                                    let formal_args: Vec<String> = items[1]
                                        .borrow()
                                        .to_vec()
                                        .iter()
                                        .map(|x| {
                                            if let Obj::Local(name) = &*x.borrow() {
                                                Ok(name.clone())
                                            } else {
                                                Err(format!(
                                                    "Got '{}' as formal arg to lambda",
                                                    x.borrow()
                                                ))
                                            }
                                        })
                                        .collect::<Result<Vec<_>>>()?;
                                    Ok(wrap!(Ast::Lambda {
                                        formal_args,
                                        rhs: Ast::from_sexp(items[2].clone())?.clone(),
                                    }))
                                }
                            }
                            _ => {
                                let mut args = Vec::new();
                                args.reserve(items.len());
                                for arg in items[1..].into_iter() {
                                    args.push(Ast::from_sexp(arg.clone())?);
                                }
                                Ok(wrap!(Ast::Call {
                                    f: Ast::from_sexp(items[0].clone())?,
                                    args,
                                }))
                            }
                        }
                    } else {
                        let mut args = Vec::new();
                        args.reserve(items.len() - 1);
                        for arg in items[1..].into_iter() {
                            args.push(Ast::from_sexp(arg.clone())?);
                        }
                        Ok(wrap!(Ast::Call {
                            f: Ast::from_sexp(items[0].clone())?,
                            args,
                        }))
                    };
                    x
                } else {
                    // TODO: How does this work?
                    Ok(wrap!(Ast::Literal(sexp.clone())))
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
            Ast::Lambda {
                formal_args: lformals,
                rhs: lrhs,
            } => {
                if let Ast::Lambda {
                    formal_args: rformals,
                    rhs: rrhs,
                } = other
                {
                    lformals == rformals && lrhs == rrhs
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

    macro_rules! test_case {
        ($name:ident, failure, $input:expr) => {
            #[test]
            fn $name() {
                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);

                let parse_res = stream.read_sexp().unwrap();
                let res = Ast::from_sexp(parse_res);
                assert!(res.is_err());
            }
        };
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

    test_case!(fixnum, "0", lit_wrap!(Obj::Fixnum(0)));
    test_case!(boolean, "#t", lit_wrap!(Obj::Bool(true)));
    test_case!(nil, "()", lit_wrap!(Obj::Nil));

    test_case!(local, "hello\n", wrap!(Ast::Var("hello".to_string())));

    test_case!(
        val,
        "(val x 5)",
        wrap!(Ast::DefAst(Def::Val {
            name: "x".to_string(),
            rhs: lit_wrap!(Obj::Fixnum(5)),
        }))
    );
    test_case!(
        conditional,
        "(if #t 5 6)",
        wrap!(Ast::If {
            pred: lit_wrap!(Obj::Bool(true)),
            cons: lit_wrap!(Obj::Fixnum(5)),
            alt: lit_wrap!(Obj::Fixnum(6)),
        })
    );
    test_case!(
        and,
        "(and #t #f)",
        wrap!(Ast::And {
            l: lit_wrap!(Obj::Bool(true)),
            r: lit_wrap!(Obj::Bool(false)),
        })
    );
    test_case!(
        or,
        "(or #t #f)",
        wrap!(Ast::Or {
            l: lit_wrap!(Obj::Bool(true)),
            r: lit_wrap!(Obj::Bool(false)),
        })
    );
    test_case!(
        apply,
        "(apply f ())",
        wrap!(Ast::Apply {
            l: wrap!(Ast::Var("f".to_string())),
            r: lit_wrap!(Obj::Nil),
        })
    );
    test_case!(
        call_with_fixnum_first,
        "(1 2 3)",
        wrap!(Ast::Call {
            f: lit_wrap!(Obj::Fixnum(1)),
            args: vec![lit_wrap!(Obj::Fixnum(2)), lit_wrap!(Obj::Fixnum(3))],
        })
    );
    test_case!(
        call,
        "(f 1 2)",
        wrap!(Ast::Call {
            f: wrap!(Ast::Var("f".to_string())),
            args: vec![lit_wrap!(Obj::Fixnum(1)), lit_wrap!(Obj::Fixnum(2))],
        })
    );

    test_case!(
        lambda,
        "(lambda (x) 5)",
        wrap!(Ast::Lambda {
            formal_args: vec!["x".to_string()],
            rhs: lit_wrap!(Obj::Fixnum(5)),
        })
    );
    test_case!(
        lambda_with_fixnum_formal,
        failure,
        "(lambda (5) 5)"
    );
}
