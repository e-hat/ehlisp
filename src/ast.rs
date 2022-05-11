use std::cell::RefCell;
use std::cmp::PartialEq;
use std::fmt;
use std::rc::Rc;

use crate::gc::{Gc, GcGraphNode, GcHandle, GcNodeType, GcStrong};
use crate::parse::Obj;

// A representation of expressions/programs that lends itself better to traversal and evaluation.
// This is instead of evaluating the S-expressions directly, which means a lot of headaches with
// verifying valid forms and whatnot.
pub enum Ast {
    Literal(GcHandle<Obj>),
    Var(String),
    If {
        pred: GcHandle<Ast>,
        cons: GcHandle<Ast>,
        alt: GcHandle<Ast>,
    },
    PairAccessor {
        pattern: String,
        arg: GcHandle<Ast>,
    },
    And {
        l: GcHandle<Ast>,
        r: GcHandle<Ast>,
    },
    Or {
        l: GcHandle<Ast>,
        r: GcHandle<Ast>,
    },
    Apply {
        l: GcHandle<Ast>,
        r: GcHandle<Ast>,
    },
    Call {
        f: GcHandle<Ast>,
        args: Vec<GcHandle<Ast>>,
    },
    Lambda {
        formal_args: Vec<String>,
        rhs: GcHandle<Ast>,
    },
    DefAst(Def),
}

impl GcGraphNode for Ast {
    fn neighbors(&self) -> Vec<GcNodeType> {
        match self {
            Ast::Literal(obj) => vec![GcNodeType::Obj(obj.clone())],
            Ast::Var(_) => Vec::new(),
            Ast::If { pred, cons, alt } => vec![pred.clone(), cons.clone(), alt.clone()]
                .iter()
                .map(|x| GcNodeType::Ast(x.clone()))
                .collect::<Vec<_>>(),
            Ast::PairAccessor { pattern: _, arg } => vec![GcNodeType::Ast(arg.clone())],
            Ast::And { l, r } => vec![l.clone(), r.clone()]
                .iter()
                .map(|x| GcNodeType::Ast(x.clone()))
                .collect::<Vec<_>>(),
            Ast::Or { l, r } => vec![l.clone(), r.clone()]
                .iter()
                .map(|x| GcNodeType::Ast(x.clone()))
                .collect::<Vec<_>>(),
            Ast::Apply { l, r } => vec![l.clone(), r.clone()]
                .iter()
                .map(|x| GcNodeType::Ast(x.clone()))
                .collect::<Vec<_>>(),
            Ast::Call { f, args } => {
                let mut res = vec![GcNodeType::Ast(f.clone())];
                res.extend(args.clone().iter().map(|x| GcNodeType::Ast(x.clone())));
                res
            }
            Ast::Lambda {
                formal_args: _,
                rhs,
            } => vec![GcNodeType::Ast(rhs.clone())],
            Ast::DefAst(Def::Val { name: _, rhs }) => vec![GcNodeType::Ast(rhs.clone())],
            Ast::DefAst(Def::Def {
                name: _,
                formal_args: _,
                rhs,
            }) => vec![GcNodeType::Ast(rhs.clone())],
        }
    }
}

// This is for ASTs that change the evaluation's environment. I don't think we need this Def::Ast
// alternative.
pub enum Def {
    Val {
        name: String,
        rhs: GcHandle<Ast>,
    },
    Def {
        name: String,
        formal_args: Vec<String>,
        rhs: GcHandle<Ast>,
    },
    // Ast(GcHandle(Ast)),
}

type Error = String;
pub type Result<T> = std::result::Result<T, Error>;

impl Ast {
    // Translating S-expressions to the AST type. The input is expected to come from the parsing stage of
    // the REPL, so we will fail if we encounter Obj::Primitive's or Obj::Closure's, which only appear
    // during evaluation. This is also where special forms are built. I don't think `and` or `or`
    // should be handled here, as they are not special forms and make more sense as primitives. I'm
    // on the fence about `lambda` and `apply`, but they seem kinda special.
    pub fn from_sexp(sexp: &GcHandle<Obj>, gc: Rc<RefCell<Gc>>) -> Result<GcHandle<Ast>> {
        match &*sexp.get().borrow() {
            Obj::Fixnum(_) => Ok(gc.borrow_mut().new_ast(Ast::Literal(sexp.clone()))),
            Obj::Bool(_) => Ok(gc.borrow_mut().new_ast(Ast::Literal(sexp.clone()))),
            Obj::Local(name) => Ok(gc.borrow_mut().new_ast(Ast::Var(name.to_string()))),
            Obj::Nil => Ok(gc.borrow_mut().new_ast(Ast::Literal(sexp.clone()))),
            Obj::Quote(_) => Ok(gc.borrow_mut().new_ast(Ast::Literal(sexp.clone()))),
            Obj::Primitive(f, _) => Err(format!("Unexpected Primitive sexp '{}'", f)),
            Obj::Closure { .. } => Err("Unexpected closure".to_string()),
            Obj::Pair(..) => {
                // Handle special forms here
                if sexp.get().borrow().is_list() {
                    let items = sexp.get().borrow().to_vec();
                    // A previous pattern match proved that this sexp is NOT Obj::Nil
                    // Therefore items.len() >= 1
                    let x = if let Obj::Local(first_word) = &*items[0].get().borrow() {
                        match first_word.as_str() {
                            "if" => {
                                if items.len() != 4 {
                                    Err("expected form (if (pred) (cons) (alt))".to_string())
                                } else {
                                    let pred = Ast::from_sexp(&items[1], gc.clone())?;
                                    let cons = Ast::from_sexp(&items[2], gc.clone())?;
                                    let alt = Ast::from_sexp(&items[3], gc.clone())?;
                                    Ok(gc.borrow_mut().new_ast(Ast::If { pred, cons, alt }))
                                }
                            }
                            "and" => {
                                if items.len() != 3 {
                                    Err("expected form (and (l) (r))".to_string())
                                } else {
                                    let l = Ast::from_sexp(&items[1], gc.clone())?;
                                    let r = Ast::from_sexp(&items[2], gc.clone())?;
                                    Ok(gc.borrow_mut().new_ast(Ast::And { l, r }))
                                }
                            }
                            "or" => {
                                if items.len() != 3 {
                                    Err("expected form (or (l) (r))".to_string())
                                } else {
                                    let l = Ast::from_sexp(&items[1], gc.clone())?;
                                    let r = Ast::from_sexp(&items[2], gc.clone())?;
                                    Ok(gc.borrow_mut().new_ast(Ast::Or { l, r }))
                                }
                            }
                            "val" => {
                                if items.len() != 3 {
                                    Err("expected form (val (name) (expr))".to_string())
                                } else {
                                    if let Obj::Local(name) = &*items[1].get().borrow() {
                                        let rhs = Ast::from_sexp(&items[2], gc.clone())?;
                                        Ok(gc.borrow_mut().new_ast(Ast::DefAst(Def::Val {
                                            name: name.to_string(),
                                            rhs,
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
                                    let l = Ast::from_sexp(&items[1], gc.clone())?;
                                    let r = Ast::from_sexp(&items[2], gc.clone())?;
                                    Ok(gc.borrow_mut().new_ast(Ast::Apply { l, r }))
                                }
                            }
                            "lambda" => {
                                if items.len() != 3 || !items[1].get().borrow().is_list() {
                                    Err("expected form (lambda (formal args) body)".to_string())
                                } else {
                                    let formal_args = parse_formal_args(&*items[1].get().borrow())?;
                                    let rhs = Ast::from_sexp(&items[2], gc.clone())?;
                                    Ok(gc.borrow_mut().new_ast(Ast::Lambda { formal_args, rhs }))
                                }
                            }
                            "define" => {
                                if items.len() != 4 || !items[2].get().borrow().is_list() {
                                    Err("expected form (define name (formal args) body)"
                                        .to_string())
                                } else {
                                    if let Obj::Local(name) = &*items[1].get().borrow() {
                                        let formal_args =
                                            parse_formal_args(&*items[2].get().borrow())?;
                                        let rhs = Ast::from_sexp(&items[3], gc.clone())?;
                                        Ok(gc.borrow_mut().new_ast(Ast::DefAst(Def::Def {
                                            name: name.clone(),
                                            formal_args,
                                            rhs,
                                        })))
                                    } else {
                                        Err(format!(
                                            "expected function name to be Local, got '{}'",
                                            items[1].get().borrow()
                                        ))
                                    }
                                }
                            }
                            _ => {
                                let as_bytes = &first_word[..].as_bytes();
                                if as_bytes.len() >= 3
                                    && as_bytes[0] == b'c'
                                    && as_bytes[as_bytes.len() - 1] == b'r'
                                    && contains_only_ad(&as_bytes[1..as_bytes.len() - 1])
                                {
                                    if items.len() != 2 {
                                        Err("expected form (cxxr pair)".to_string())
                                    } else {
                                        let arg = Ast::from_sexp(&items[1], gc.clone())?;
                                        Ok(gc.borrow_mut().new_ast(Ast::PairAccessor {
                                            pattern: String::from_utf8(Vec::from(
                                                &as_bytes[1..as_bytes.len() - 1],
                                            ))
                                            .expect("Given non-utf8 encoded string :["),
                                            arg,
                                        }))
                                    }
                                } else {
                                    let mut args = Vec::new();
                                    args.reserve(items.len());
                                    for arg in items[1..].into_iter() {
                                        args.push(Ast::from_sexp(arg, gc.clone())?);
                                    }
                                    let call = Ast::Call {
                                        f: Ast::from_sexp(&items[0], gc.clone())?,
                                        args,
                                    };
                                    Ok(gc.borrow_mut().new_ast(call))
                                }
                            }
                        }
                    } else {
                        // This is the case where the function itself is not a simple variable
                        // name.
                        let mut args = Vec::new();
                        args.reserve(items.len() - 1);
                        for arg in items[1..].into_iter() {
                            args.push(Ast::from_sexp(arg, gc.clone())?);
                        }
                        let f = Ast::from_sexp(&items[0], gc.clone())?;
                        Ok(gc.borrow_mut().new_ast(Ast::Call { f, args }))
                    };
                    x
                } else {
                    // We won't ever end up here, as there's no way for the user to input pairs
                    // without calling the `pair` function. Maybe I should use `unreachable!()`
                    Ok(gc.borrow_mut().new_ast(Ast::Literal(sexp.clone())))
                }
            }
        }
    }
}

fn contains_only_ad(chars: &[u8]) -> bool {
    for c in chars {
        if *c != b'a' && *c != b'd' {
            return false;
        }
    }

    true
}

fn parse_formal_args(sexp: &Obj) -> Result<Vec<String>> {
    sexp.to_vec()
        .iter()
        .map(|x| {
            if let Obj::Local(name) = &*x.get().borrow() {
                Ok(name.clone())
            } else {
                Err(format!("Got '{}' as formal arg", x.get().borrow()))
            }
        })
        .collect::<Result<Vec<_>>>()
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ast::Literal(obj) => f.write_str(&format!("{}", obj.get().borrow())),
            Ast::Var(name) => f.write_str(&format!("var: {}", name)),
            Ast::If { pred, cons, alt } => f.write_str(&format!(
                "if {}\nthen\n{}\nelse\n{}",
                pred.get().borrow(),
                cons.get().borrow(),
                alt.get().borrow()
            )),
            Ast::PairAccessor { pattern, arg } => {
                f.write_str(&format!("(c{}r {})", pattern, arg.get().borrow()))
            }
            Ast::And { l, r } => f.write_str(&format!(
                "( {} ) and ( {} )",
                l.get().borrow(),
                r.get().borrow()
            )),
            Ast::Or { l, r } => f.write_str(&format!(
                "( {} ) or ( {} )",
                l.get().borrow(),
                r.get().borrow()
            )),
            Ast::Apply { l, r } => f.write_str(&format!(
                "( {} ) apply ( {} )",
                l.get().borrow(),
                r.get().borrow()
            )),
            Ast::Call { f: func, args } => {
                let mut arg_str = String::from(" ");
                for arg in args {
                    arg_str.push_str(&format!("{} ", arg.get().borrow()));
                }
                f.write_str(&format!("call ( {} ) ({})", func.get().borrow(), arg_str))
            }
            Ast::DefAst(def) => f.write_str(&format!("def {}", def)),
            Ast::Lambda { .. } => f.write_str(&format!("#<lambda>")),
        }
    }
}

impl fmt::Display for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Def::Val { name, rhs } => {
                f.write_str(&format!("let {} = {}", name, rhs.get().borrow()))
            }
            Def::Def { .. } => f.write_str("#<definition>"),
            // Def::Ast(ast) => f.write_str(&format!("{}", ast.get().get().borrow())),
        }
    }
}

impl fmt::Debug for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&format!("{}", self))
    }
}

impl PartialEq for Ast {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Ast::Literal(l) => {
                if let Ast::Literal(r) = other {
                    l.get() == r.get()
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
                    lpred.get() == rpred.get()
                        && lcons.get() == rcons.get()
                        && lalt.get() == ralt.get()
                } else {
                    false
                }
            }
            Ast::PairAccessor {
                pattern: lpattern,
                arg: larg,
            } => {
                if let Ast::PairAccessor {
                    pattern: rpattern,
                    arg: rarg,
                } = other
                {
                    lpattern == rpattern && larg.get() == rarg.get()
                } else {
                    false
                }
            }
            Ast::And { l: ll, r: lr } => {
                if let Ast::And { l: rl, r: rr } = other {
                    ll.get() == rl.get() && lr.get() == rr.get()
                } else {
                    false
                }
            }
            Ast::Or { l: ll, r: lr } => {
                if let Ast::Or { l: rl, r: rr } = other {
                    ll.get() == rl.get() && lr.get() == rr.get()
                } else {
                    false
                }
            }
            Ast::Apply { l: ll, r: lr } => {
                if let Ast::Apply { l: rl, r: rr } = other {
                    ll.get() == rl.get() && lr.get() == rr.get()
                } else {
                    false
                }
            }
            Ast::Call { f: lf, args: largs } => {
                if let Ast::Call { f: rf, args: rargs } = other {
                    lf.get() == rf.get()
                        && largs
                            .iter()
                            .map(|x| x.get())
                            .collect::<Vec<GcStrong<Ast>>>()
                            == rargs
                                .iter()
                                .map(|x| x.get())
                                .collect::<Vec<GcStrong<Ast>>>()
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
                    lformals == rformals && lrhs.get() == rrhs.get()
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
                    lname == rname && lrhs.get() == rrhs.get()
                } else {
                    false
                }
            }
            Def::Def {
                name: lname,
                formal_args: lformals,
                rhs: lrhs,
            } => {
                if let Def::Def {
                    name: rname,
                    formal_args: rformals,
                    rhs: rrhs,
                } = other
                {
                    lname == rname && lformals == rformals && lrhs.get() == rrhs.get()
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
    use std::cell::RefCell;
    use std::rc::Rc;

    use crate::gc::Gc;
    use crate::handle;
    use crate::parse::*;

    macro_rules! test_case {
        ($name:ident, failure, $input:expr) => {
            #[test]
            fn $name() {
                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);

                let gc = Rc::new(RefCell::new(Gc::new()));

                let parse_res = stream.read_sexp(&mut *gc.borrow_mut()).unwrap();
                let res = Ast::from_sexp(&parse_res, gc);
                assert!(res.is_err());
            }
        };
        ($name:ident, $input:expr, $expected:expr) => {
            #[test]
            fn $name() {
                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);

                let gc = Rc::new(RefCell::new(Gc::new()));

                let parse_res = stream.read_sexp(&mut *gc.borrow_mut()).unwrap();
                let res = Ast::from_sexp(&parse_res, gc.clone());
                assert!(!res.is_err());
                assert_eq!(&*res.unwrap().get().borrow(), &$expected);
            }
        };
    }

    macro_rules! lit_wrap {
        ($x:expr) => {
            Ast::Literal(handle!($x))
        };
    }

    test_case!(fixnum, "0", lit_wrap!(Obj::Fixnum(0)));
    test_case!(boolean, "#t", lit_wrap!(Obj::Bool(true)));
    test_case!(nil, "()", lit_wrap!(Obj::Nil));

    test_case!(local, "hello\n", Ast::Var("hello".to_string()));

    test_case!(
        val,
        "(val x 5)",
        Ast::DefAst(Def::Val {
            name: "x".to_string(),
            rhs: handle!(lit_wrap!(Obj::Fixnum(5))),
        })
    );
    test_case!(
        conditional,
        "(if #t 5 6)",
        Ast::If {
            pred: handle!(lit_wrap!(Obj::Bool(true))),
            cons: handle!(lit_wrap!(Obj::Fixnum(5))),
            alt: handle!(lit_wrap!(Obj::Fixnum(6))),
        }
    );
    test_case!(
        and,
        "(and #t #f)",
        Ast::And {
            l: handle!(lit_wrap!(Obj::Bool(true))),
            r: handle!(lit_wrap!(Obj::Bool(false))),
        }
    );
    test_case!(
        or,
        "(or #t #f)",
        Ast::Or {
            l: handle!(lit_wrap!(Obj::Bool(true))),
            r: handle!(lit_wrap!(Obj::Bool(false))),
        }
    );
    test_case!(
        apply,
        "(apply f ())",
        Ast::Apply {
            l: handle!(Ast::Var("f".to_string())),
            r: handle!(lit_wrap!(Obj::Nil)),
        }
    );
    test_case!(
        call_with_fixnum_first,
        "(1 2 3)",
        Ast::Call {
            f: handle!(lit_wrap!(Obj::Fixnum(1))),
            args: vec![
                handle!(lit_wrap!(Obj::Fixnum(2))),
                handle!(lit_wrap!(Obj::Fixnum(3)))
            ],
        }
    );
    test_case!(
        call,
        "(f 1 2)",
        Ast::Call {
            f: handle!(Ast::Var("f".to_string())),
            args: vec![
                handle!(lit_wrap!(Obj::Fixnum(1))),
                handle!(lit_wrap!(Obj::Fixnum(2)))
            ],
        }
    );

    test_case!(
        lambda,
        "(lambda (x) 5)",
        Ast::Lambda {
            formal_args: vec!["x".to_string()],
            rhs: handle!(lit_wrap!(Obj::Fixnum(5))),
        }
    );
    test_case!(lambda_with_fixnum_formal, failure, "(lambda (5) 5)");

    test_case!(
        define,
        "(define x () 5)",
        Ast::DefAst(Def::Def {
            name: "x".to_string(),
            formal_args: vec![],
            rhs: handle!(lit_wrap!(Obj::Fixnum(5))),
        })
    );

    macro_rules! pair_accessor_pattern_case {
        ($name:ident, $pattern:expr) => {
            test_case!(
                $name,
                format!("(c{}r nil)", $pattern),
                Ast::Call {
                    f: handle!(Ast::Var(format!("c{}r", $pattern))),
                    args: vec![handle!(Ast::Var(String::from("nil"))),]
                }
            );
        };
    }

    pair_accessor_pattern_case!(pair_accessor_happy_path, "aaadddr");
    pair_accessor_pattern_case!(pair_accessor_empty_pattern, "");
    pair_accessor_pattern_case!(pair_accessor_invalid_char, "p");
}
