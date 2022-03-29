use std::rc::Rc;
use std::cell::RefCell;

use crate::parse::Obj;

fn is_trivial(stmt: &Obj) -> bool {
    match stmt {
        Obj::Fixnum(_) => true,
        Obj::Nil => true,
        Obj::Bool(_) => true,
        Obj::Pair(l, r) => is_trivial(&l.borrow()) && is_trivial(&r.borrow()),
        Obj::Local(_) => false
    }
}

pub fn eval(stmt: Rc<RefCell<Obj>>) -> Rc<RefCell<Obj>> {
    if is_trivial(&stmt.borrow()) {
        stmt
    } else {
        unimplemented!()
    }
}
