use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::parse::Obj;

pub struct Context {
    env: HashMap<String, Rc<RefCell<Obj>>>,
}

type EvalError = String;
pub type Result<T> = std::result::Result<T, EvalError>;

fn is_keyword(word: &str) -> bool {
    return word == "val";
}

fn invalid_control_flow(keyword: &str) -> EvalError {
    format!("Invalid control flow in `{}` statement", keyword)
}

impl Context {
    pub fn new() -> Self {
        Context {
            env: HashMap::new(),
        }
    }

    pub fn eval(&mut self, stmt: Rc<RefCell<Obj>>) -> Result<Rc<RefCell<Obj>>> {
        match *stmt.borrow() {
            Obj::Fixnum(_) => Ok(stmt.clone()),
            Obj::Nil => Ok(stmt.clone()),
            Obj::Bool(_) => Ok(stmt.clone()),
            Obj::Local(ref l) => match self.env.get(l) {
                Some(res) => Ok(res.clone()),
                None => Err(format!("Non-existent local `{}` referenced", l)),
            },
            _ => self.eval_pair(stmt.clone()),
        }
    }

    fn eval_pair(&mut self, lst: Rc<RefCell<Obj>>) -> Result<Rc<RefCell<Obj>>> {
        match &*lst.borrow() {
            Obj::Pair(l, r) => {
                if let Obj::Local(ref word) = *l.borrow() {
                    if is_keyword(word) {
                        self.eval_keyword(word, r.clone())
                    } else {
                        self.eval_pair_normal(lst.clone())
                    }
                } else {
                    self.eval_pair_normal(lst.clone())
                }
            }
            _ => unreachable!(),
        }
    }

    fn eval_keyword(&mut self, keyword: &str, lst: Rc<RefCell<Obj>>) -> Result<Rc<RefCell<Obj>>> {
        match keyword {
            "val" => {
                if let Obj::Pair(ref lhs, ref rhs) = *lst.borrow() {
                    self.eval_assignment(lhs.clone(), rhs.clone())
                } else {
                    Err(invalid_control_flow("val"))
                }
            }
            _ => unreachable!(),
        }
    }

    fn eval_assignment(
        &mut self,
        lhs: Rc<RefCell<Obj>>,
        rhs: Rc<RefCell<Obj>>,
    ) -> Result<Rc<RefCell<Obj>>> {
        if let Obj::Local(ref name) = *lhs.borrow() {
            if self.env.contains_key(name) {
                Err(format!("Object with name `{}` already exists", name))
            } else {
                if let Obj::Pair(rhs_stmt, nil) = &*rhs.borrow() {
                    if let Obj::Nil = &*nil.borrow() {
                        let result = self.eval(rhs_stmt.clone())?;
                        self.env.insert(name.to_string(), result.clone());
                        Ok(result.clone())
                    } else {
                        Err(invalid_control_flow("val"))
                    }
                } else {
                    Err(invalid_control_flow("val"))
                }
            }
        } else {
            Err(String::from(
                "Expected an identifier as first element in `val` statement",
            ))
        }
    }

    fn eval_pair_normal(&mut self, lst: Rc<RefCell<Obj>>) -> Result<Rc<RefCell<Obj>>> {
        if let Obj::Pair(l, r) = &*lst.borrow() {
            Ok(Rc::new(RefCell::new(Obj::Pair(
                self.eval(l.clone())?,
                self.eval(r.clone())?,
            ))))
        } else {
            unreachable!();
        }
    }
}
