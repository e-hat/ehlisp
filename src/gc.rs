use std::cell::RefCell;
use std::clone::Clone;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::rc::Rc;
use std::rc::Weak;

use crate::{ast::Ast, parse::Obj};

pub struct Gc {
    obj_pool: HashMap<u64, GcStrong<Obj>>,
    ast_pool: HashMap<u64, GcStrong<Ast>>,
    item_count: u64,
}

#[derive(Debug)]
pub struct GcHandle<T> {
    inner: Weak<RefCell<T>>,
}

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
            obj_pool: HashMap::new(),
            ast_pool: HashMap::new(),
            item_count: 0,
        }
    }

    pub fn new_obj(&mut self, obj: Obj) -> GcHandle<Obj> {
        self.item_count += 1;
        Gc::new_t(&mut self.obj_pool, self.item_count, obj)
    }

    pub fn new_ast(&mut self, ast: Ast) -> GcHandle<Ast> {
        self.item_count += 1;
        Gc::new_t(&mut self.ast_pool, self.item_count, ast)
    }

    fn new_t<T>(ts: &mut HashMap<u64, GcStrong<T>>, id: u64, t: T) -> GcHandle<T> {
        let rc = Rc::new(RefCell::new(t));
        ts.insert(id, rc.clone());
        GcHandle::new(Rc::downgrade(&rc))
    }

    pub fn sweep(&mut self) {
        let mut dead_objs = Vec::new();
        for (id, obj) in &self.obj_pool {
            if Rc::strong_count(&obj) == 1 && Rc::weak_count(&obj) == 0 {
                dead_objs.push(*id);
                println!("Pruning '{}'", obj.borrow());
            }
        }
        for id in dead_objs.iter() {
            self.obj_pool.remove(id);
        }

        let mut dead_asts = Vec::new();
        for (id, ast) in &self.ast_pool {
            if Rc::strong_count(&ast) == 1 && Rc::weak_count(&ast) == 0 {
                dead_asts.push(*id);
                println!("Pruning '{}'", ast.borrow());
            }
        }
        for id in dead_asts.iter() {
            self.ast_pool.remove(id);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    
    use crate::gc::*;

    macro_rules! handle {
        ($x:expr) => {
            GcHandle::new(Rc::downgrade(&Rc::new(RefCell::new($x))))
        };
    }
    #[test]
    fn pointer_cycle() {
        let gc = Rc::new(RefCell::new(Gc::new()));
        let obj = gc.borrow_mut().new_obj(Obj::Closure {
            formal_args: Vec::new(),
            rhs: handle!(Ast::Literal(handle!(Obj::Nil))),
            env: HashMap::new(),
        });
        if let Obj::Closure {
            formal_args: _,
            rhs: _,
            env,
        } = &mut *obj.get().borrow_mut()
        {
            env.insert(String::from("hello"), Some(obj.clone()));
        } else {
            unreachable!()
        }
    }
}
