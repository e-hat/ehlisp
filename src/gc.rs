use std::cell::{RefCell, Ref, RefMut};
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

pub struct GcStrong<T>(Rc<RefCell<GcData<T>>>);

impl<T: GcGraphNode> GcStrong<T> {
    pub fn new(data: Rc<RefCell<GcData<T>>>) -> Self {
        GcStrong(data)
    }

    pub fn replace(&self, data: T) {
        let marked: bool = self.0.borrow().marked;
        self.0.replace(GcData { data, marked });
    }

    pub fn get_handle(&self) -> GcHandle<T> {
        GcHandle::new(Rc::downgrade(&self.0))
    }

    pub fn strong_count(&self) -> usize {
        Rc::strong_count(&self.0)
    }

    pub fn weak_count(&self) -> usize {
        Rc::weak_count(&self.0)
    }

    pub fn borrow(&self) -> Ref<T> {
        Ref::map(self.0.borrow(), |x| &x.data)
    }

    pub fn borrow_mut(&mut self) -> RefMut<T> {
        RefMut::map(self.0.borrow_mut(), |x: &mut GcData<T>| &mut x.data)
    }
}

impl<T: std::fmt::Display> std::fmt::Display for GcStrong<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("{}", self.0.borrow()))
    }
}

impl<T: PartialEq> PartialEq for GcStrong<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Clone for GcStrong<T> {
    fn clone(&self) -> Self {
        GcStrong(self.0.clone())
    }
}

pub trait GcGraphNode {
    fn neighbors(&self) -> Vec<Box<dyn GcGraphNode>>;
}

// GcData definition/trait impls
#[derive(Debug)]
pub struct GcData<T> {
    data: T,
    marked: bool,
}

impl<T: PartialEq> PartialEq for GcData<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T> GcData<T> {
    pub fn new(data: T) -> Self {
        GcData {
            data,
            marked: false,
        }
    }
}

impl<T: std::fmt::Display> std::fmt::Display for GcData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("{}", self.data))
    }
}

impl<T: GcGraphNode> GcGraphNode for GcData<T> {
    fn neighbors(&self) -> Vec<Box<dyn GcGraphNode>> {
        self.data.neighbors()
    }
}

impl<T> std::ops::Deref for GcData<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

// GcHandle definition/trait impls
#[derive(Debug)]
pub struct GcHandle<T: GcGraphNode> {
    inner: Weak<RefCell<GcData<T>>>,
}

impl<T: GcGraphNode> GcHandle<T> {
    pub fn new(inner: Weak<RefCell<GcData<T>>>) -> Self {
        GcHandle { inner }
    }

    pub fn get(&self) -> GcStrong<T> {
        GcStrong::new(self.inner.upgrade().unwrap())
    }
}

impl<T: PartialEq + GcGraphNode> PartialEq for GcHandle<T> {
    fn eq(&self, other: &GcHandle<T>) -> bool {
        self.get() == other.get()
    }
}

impl<T: GcGraphNode> Clone for GcHandle<T> {
    fn clone(&self) -> Self {
        GcHandle::new(self.inner.clone())
    }
}

impl<T: GcGraphNode> GcGraphNode for GcHandle<T> {
    fn neighbors(&self) -> Vec<Box<dyn GcGraphNode>> {
        // don't recurse
        self.get().borrow().neighbors()
    }
}

// Gc impls
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

    fn new_t<T: GcGraphNode>(ts: &mut HashMap<u64, GcStrong<T>>, id: u64, t: T) -> GcHandle<T> {
        let rc = GcStrong::new(Rc::new(RefCell::new(GcData::new(t))));
        ts.insert(id, rc.clone());
        rc.get_handle()
    }

    pub fn sweep(&mut self) {
        let mut dead_objs = Vec::new();
        for (id, obj) in &self.obj_pool {
            if obj.strong_count() == 1 && obj.weak_count() == 0 {
                dead_objs.push(*id);
                println!("Pruning '{}'", obj.borrow());
            }
        }
        for id in dead_objs.iter() {
            self.obj_pool.remove(id);
        }

        let mut dead_asts = Vec::new();
        for (id, ast) in &self.ast_pool {
            if ast.strong_count() == 1 && ast.weak_count() == 0 {
                dead_asts.push(*id);
                println!("Pruning '{}'", ast.borrow());
            }
        }
        for id in dead_asts.iter() {
            self.ast_pool.remove(id);
        }
    }

    pub fn mark(handles: &[GcHandle<Obj>]) {}
}

#[macro_export]
macro_rules! handle {
    ($x:expr) => {
        GcHandle::new(Rc::downgrade(&Rc::new(RefCell::new(GcData::new($x)))))
    };
}

#[cfg(test)]
mod tests {
    use std::assert;
    use std::mem::size_of;
    use std::rc::Rc;

    extern crate test;
    use test::Bencher;

    use crate::gc::*;
    use crate::handle;

    #[bench]
    fn pointer_cycle(b: &mut Bencher) {
        b.iter(|| {
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
            } = *obj.get().borrow_mut()
            {
                env.insert(String::from("hello"), Some(obj.clone()));
            } else {
                unreachable!()
            }
            println!("sizeof Obj: {}", size_of::<Obj>());

            assert!(obj.get().weak_count() == 2);
        })
    }
}
