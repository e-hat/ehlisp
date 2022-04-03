use std::cell::RefCell;
use std::rc::Rc;

use crate::parse::Obj;

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

pub enum Def {
    Val { name: String, rhs: Rc<RefCell<Ast>> },
    Ast(Rc<RefCell<Ast>>),
}

type Error = String;
pub type Result<T> = std::result::Result<T, Error>;

impl Ast {
    pub fn from_sexp(sexp: Rc<RefCell<Obj>>) -> Result<Rc<RefCell<Ast>>> {
        match &*sexp.borrow() {
            Obj::Fixnum(_) => Ok(Rc::new(RefCell::new(Ast::Literal(sexp.clone())))),
            Obj::Bool(_) => Ok(Rc::new(RefCell::new(Ast::Literal(sexp.clone())))),
            Obj::Local(name) => Ok(Rc::new(RefCell::new(Ast::Var(name.to_string())))),
            Obj::Nil => Ok(Rc::new(RefCell::new(Ast::Literal(sexp.clone())))),
            _ => {
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
                                    Ok(Rc::new(RefCell::new(Ast::If{
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
                                    Ok(Rc::new(RefCell::new(Ast::And{
                                        l: Ast::from_sexp(items[1].clone())?,
                                        r: Ast::from_sexp(items[2].clone())?,
                                    })))
                                }
                            }
                            "or" => {
                                if items.len() != 3 {
                                    Err("expected form (or (l) (r))".to_string())
                                } else {
                                    Ok(Rc::new(RefCell::new(Ast::Or{
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
                                        Ok(Rc::new(RefCell::new(Ast::DefAst(Def::Val{
                                            name: name.to_string(),
                                            rhs: Ast::from_sexp(items[2].clone())?,
                                        }))))
                                    } else {
                                        Err("expected `name` to be a string in form (val (name) (expr))".to_string())
                                    }
                                }
                            }
                        }
                    } else {
                        let mut args = Vec::new();
                        args.reserve(items.len() - 1);
                        for arg in items[1..].into_iter() {
                            args.push(Ast::from_sexp(arg.clone())?);
                        }
                        Ok(Rc::new(RefCell::new(Ast::Call{
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
