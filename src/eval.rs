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
    return word == "val" || word == "if";
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
        if let Obj::Pair(l, r) = &*lst.borrow() {
            if let Obj::Local(ref word) = *l.borrow() {
                if is_keyword(word) {
                    if lst.borrow().is_list() {
                        self.eval_keyword(word, r.clone())
                    } else {
                        unreachable!()
                    }
                } else {
                    self.eval_pair_normal(lst.clone())
                }
            } else {
                self.eval_pair_normal(lst.clone())
            }
        } else {
            unreachable!()
        }
    }

    fn eval_keyword(&mut self, keyword: &str, lst: Rc<RefCell<Obj>>) -> Result<Rc<RefCell<Obj>>> {
        let items = lst.borrow().to_vec();
        match keyword {
            "val" => self.eval_assignment(items),
            "if" => self.eval_conditional(items),
            _ => unreachable!(),
        }
    }

    fn eval_conditional(&mut self, items: Vec<Rc<RefCell<Obj>>>) -> Result<Rc<RefCell<Obj>>> {
        if items.len() != 3 {
            Err(invalid_control_flow("val"))
        } else {
            let pred = &items[0];
            let cons = &items[1];
            let alt = &items[2];
            if let Obj::Bool(pred_val) = *self.eval(pred.clone())?.borrow() {
                if pred_val {
                    self.eval(cons.clone())
                } else {
                    self.eval(alt.clone())
                }
            } else {
                Err(String::from("if-conditional expects a `bool` result for predicate expression"))
            }
        }
    }

    fn eval_assignment(&mut self, items: Vec<Rc<RefCell<Obj>>>) -> Result<Rc<RefCell<Obj>>> {
        if items.len() < 2 {
            Err(invalid_control_flow("val"))
        } else {
            let lhs = &items[0];
            let rhs = &items[1];
            if let Obj::Local(ref name) = *lhs.borrow() {
                if self.env.contains_key(name) {
                    Err(format!("Object with name `{}` already exists", name))
                } else {
                    let result = self.eval(rhs.clone())?;
                    self.env.insert(name.to_string(), result.clone());
                    if items.len() == 3 {
                        self.eval(items[2].clone())
                    } else {
                        Ok(result.clone())
                    }
                }
            } else {
                Err(String::from(
                    "Expected an identifier as first element in `val` statement",
                ))
            }
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
