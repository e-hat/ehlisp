use std::rc::Rc;
use std::cell::RefCell;
use std::rc::Weak;
use std::cmp::PartialEq;
use std::clone::Clone;

use crate::{parse::Obj, ast::Ast};

pub struct Gc {
    pub obj_pool: Vec<GcStrong<Obj>>,
    ast_pool: Vec<GcStrong<Ast>>,
}

#[derive(Debug)]
pub struct GcHandle<T> { inner: Weak<RefCell<T>> }

type GcStrong<T> = Rc<RefCell<T>>;

impl<T> GcHandle<T> {
    pub fn new(inner: Weak<RefCell<T>>) -> Self {
        GcHandle { inner }
    }

    pub fn get(&self) -> GcStrong<T> {
        self.inner.upgrade().unwrap()
    }

    pub fn clone(&self) -> Self {
        GcHandle::new(self.inner.clone())
    }
}

impl<T: PartialEq> PartialEq for GcHandle<T> {
    fn eq(&self, other: &GcHandle<T>) -> bool {
        self.get() == other.get()
    }
}

impl<T> Clone for GcHandle<T> {
    fn clone(&self) -> Self {
        GcHandle::new(self.inner.clone())
    }
}

impl Gc {
    pub fn new() -> Gc {
        Gc {
            obj_pool: vec![],
            ast_pool: vec![],
        }
    }

    pub fn new_obj(&mut self, obj: Obj) -> GcHandle<Obj> {
        Gc::new_t(&mut self.obj_pool, obj)
    }

    pub fn new_ast(&mut self, ast: Ast) -> GcHandle<Ast> {
        Gc::new_t(&mut self.ast_pool, ast)
    }

    fn new_t<T>(ts: &mut Vec<GcStrong<T>>, t: T) -> GcHandle<T> {
        let rc = Rc::new(RefCell::new(t));
        ts.push(rc.clone());
        GcHandle::new(Rc::downgrade(&rc))
    }
}
