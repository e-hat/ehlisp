use std::cell::{Ref, RefCell, RefMut, Cell};
use std::clone::Clone;
use std::cmp::PartialEq;
use std::rc::Rc;
use std::rc::Weak;

use crate::{ast::Ast, parse::Obj};

static MEM_CAP: usize = 1000;

// The global Gc struct. This could possibly be handled by a crate::eval::Context.
pub struct Gc {
    obj_pool: Vec<GcStrong<Obj>>,
    ast_pool: Vec<GcStrong<Ast>>,
    current_color: bool,
}

// A "strong" pointer to T, an object on the heap. Identical interface to Rc<RefCell<T>>.
// Please do not make reference cycles with this type :]
// Use this when you actual need to use the value behind a handle, for both reading/writing with
// borrow()/borrow_mut() respectively.
pub struct GcStrong<T>(Rc<RefCell<GcData<T>>>);

impl<T: GcGraphNode> GcStrong<T> {
    pub fn new(data: Rc<RefCell<GcData<T>>>) -> Self {
        GcStrong(data)
    }

    pub fn replace(&self, data: T) {
        let mut inner = self.0.borrow_mut();
        inner.data = data;
    }

    pub fn get_handle(&self) -> GcHandle<T> {
        GcHandle::new(Rc::downgrade(&self.0))
    }

    fn strong_count(&self) -> usize {
        Rc::strong_count(&self.0)
    }

    fn weak_count(&self) -> usize {
        Rc::weak_count(&self.0)
    }

    pub fn borrow(&self) -> Ref<T> {
        Ref::map(self.0.borrow(), |x| &x.data)
    }

    pub fn borrow_mut(&mut self) -> RefMut<T> {
        RefMut::map(self.0.borrow_mut(), |x| &mut x.data)
    }

    pub fn color(&self) -> bool {
        self.0.borrow().color.get()
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

pub enum GcNodeType {
    Obj(GcHandle<Obj>),
    Ast(GcHandle<Ast>),
}

impl GcNodeType {
    fn color(&self) -> bool {
        match self {
            GcNodeType::Obj(handle) => handle.get().0.borrow().color.get(),
            GcNodeType::Ast(handle) => handle.get().0.borrow().color.get(),
        }
    }

    fn set_color(&self, color: bool) {
        match self {
            GcNodeType::Obj(handle) => {
                handle.get().0.borrow().color.set(color);
            }
            GcNodeType::Ast(handle) => {
                handle.get().0.borrow().color.set(color);
            }
        }
    }
}

impl GcGraphNode for GcNodeType {
    fn neighbors(&self) -> Vec<GcNodeType> {
        match self {
            GcNodeType::Obj(handle) => handle.neighbors(),
            GcNodeType::Ast(handle) => handle.neighbors(),
        }
    }
}

// For traversing/marking the object graph.
pub trait GcGraphNode {
    fn neighbors(&self) -> Vec<GcNodeType>;
}

// GcData definition/trait impls
// A metadata wrapper for a T allocated on the Gc's heap.
#[derive(Debug)]
pub struct GcData<T> {
    data: T,
    color: Cell<bool>,
}

impl<T: PartialEq> PartialEq for GcData<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T> GcData<T> {
    pub fn new(data: T, color: bool) -> Self {
        GcData { data, color: Cell::new(color) }
    }
}

impl<T: std::fmt::Display> std::fmt::Display for GcData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("{}", self.data))
    }
}

impl<T: GcGraphNode> GcGraphNode for GcData<T> {
    fn neighbors(&self) -> Vec<GcNodeType> {
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
// GcHandle<T> is what the client of the Gc should be storing to reference the T's allocated on the Gc's
// heap. To read/mutate the value behind a GcHandle, call `get()` to get a GcStrong<T> to it.
// Go ahead! Make reference cycles with this type! I dare you!
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
    fn neighbors(&self) -> Vec<GcNodeType> {
        // don't recurse
        self.get().borrow().neighbors()
    }
}

// Gc interface/impl
impl Gc {
    pub fn new() -> Gc {
        Gc {
            obj_pool: Vec::new(),
            ast_pool: Vec::new(),
            current_color: false,
        }
    }

    pub fn new_obj(&mut self, obj: Obj) -> GcHandle<Obj> {
        Gc::new_t(&mut self.obj_pool, obj, self.current_color)
    }

    pub fn new_ast(&mut self, ast: Ast) -> GcHandle<Ast> {
        Gc::new_t(&mut self.ast_pool, ast, self.current_color)
    }

    fn new_t<T: GcGraphNode>(ts: &mut Vec<GcStrong<T>>, t: T, color: bool) -> GcHandle<T> {
        let rc = GcStrong::new(Rc::new(RefCell::new(GcData::new(t, color))));
        let res = rc.get_handle();
        ts.push(rc);
        res
    }

    // We call em "No-Handles". These are pointers in our pool that don't have any handles out
    // there at all, not even unreachable ones. We should most definitely clean these up.
    fn collect_no_handles(&mut self) {
        Self::collect_no_handles_t(&mut self.obj_pool);
        Self::collect_no_handles_t(&mut self.ast_pool);

        self.print_status();
    }

    fn collect_no_handles_t<T: GcGraphNode>(vec: &mut Vec<GcStrong<T>>) {
        vec.retain(|x| x.weak_count() > 0 || x.strong_count() > 1);
    }

    fn print_status(&self) {
        println!(
            "Obj pool size: {}b\nAst pool size: {}b",
            self.obj_pool.len() * std::mem::size_of::<Obj>(),
            self.ast_pool.len() * std::mem::size_of::<Ast>(),
        );
    }

    pub fn needs_to_collect(&self) -> bool {
        self.print_status();
        self.obj_pool.len() * std::mem::size_of::<Obj>()
            + self.obj_pool.len() * std::mem::size_of::<Ast>() > MEM_CAP
    }

    pub fn collect(&mut self, reachable_handles: Vec<GcNodeType>) {
        println!("Before anything");
        self.print_status();
        println!();

        Self::collect_no_handles_t(&mut self.obj_pool);
        Self::collect_no_handles_t(&mut self.ast_pool);
        println!("After collecting unreachables");
        self.print_status();
        println!();

        // Mark (starting with [handles])
        self.mark(reachable_handles);

        // Sweep over self.obj_pool and self.ast_pool
        self.obj_pool
            .retain(|x: &GcStrong<Obj>| x.color() != self.current_color);
        self.ast_pool
            .retain(|x: &GcStrong<Ast>| x.color() != self.current_color);
        println!("After sweeping");
        self.print_status();
        println!();

        self.current_color = !self.current_color;
    }

    fn mark(&self, handles: Vec<GcNodeType>) {
        use std::collections::VecDeque;
        let mut worklist = VecDeque::from(handles);

        while !worklist.is_empty() {
            let next = worklist.pop_front().unwrap();
            if next.color() == self.current_color {
                next.set_color(!self.current_color);
                worklist.append(&mut VecDeque::from(next.neighbors()));
            }
        }
    }
}

impl std::ops::Drop for Gc {
    fn drop(&mut self) {
        self.collect_no_handles();
    }
}

#[macro_export]
macro_rules! handle {
    ($x:expr) => {
        crate::gc::GcHandle::new(Rc::downgrade(&Rc::new(RefCell::new(
            crate::gc::GcData::new($x, false),
        ))))
    };
}

#[cfg(test)]
mod tests {
    use std::assert;
    use std::collections::HashMap;
    use std::rc::Rc;

    use crate::gc::*;
    use crate::handle;

    #[test]
    fn clean_up_handle_cycle() {
        let gc = Rc::new(RefCell::new(Gc::new()));
        {
            // Intentionally create a cycle of GcHandle's!
            let rc: GcStrong<Obj> = {
                let obj = gc.borrow_mut().new_obj(Obj::Closure {
                    formal_args: Vec::new(),
                    rhs: handle!(Ast::Literal(handle!(Obj::Nil))),
                    env: HashMap::new(),
                });
                if let Obj::Closure {
                    formal_args: _,
                    rhs: _,
                    ref mut env,
                } = *obj.get().borrow_mut()
                {
                    env.insert(String::from("hello"), Some(obj.clone()));
                } else {
                    unreachable!()
                }

                obj.get()
            };
            // We don't have any reachable GcHandle's, but the # of them is 1!
            // Eg, we have an unreachable pointer that still is out there somewhere!
            assert_eq!(rc.weak_count(), 1);
            assert_eq!(rc.strong_count(), 2);
        }
        // Ok, we have one object, and we have a single strong pointer (owned by the Gc) and a
        // single weak pointer, out there in memory somewhere I guess.
        assert_eq!(gc.borrow().obj_pool.len(), 1);
        assert_eq!(gc.borrow().obj_pool[0].strong_count(), 1);
        assert_eq!(gc.borrow().obj_pool[0].weak_count(), 1);

        // Since this weak pointer isn't reachable, then it's memory should get collected and we
        // should have 0 objects!
        gc.borrow_mut().collect(Vec::new());

        assert!(gc.borrow().obj_pool.is_empty());
    }

    #[test]
    fn clean_up_no_handles() {
        let gc = Rc::new(RefCell::new(Gc::new()));
        // Ok, add an object to the GC, but immediately drop the handle for it.
        gc.borrow_mut().new_obj(Obj::Nil);

        // Assert valid state of GC
        assert_eq!(gc.borrow().obj_pool.len(), 1);
        assert_eq!(gc.borrow().obj_pool[0].strong_count(), 1);
        assert_eq!(gc.borrow().obj_pool[0].weak_count(), 0);

        gc.borrow_mut().collect_no_handles();
        assert!(gc.borrow().obj_pool.is_empty());

        {
            let handle = gc.borrow_mut().new_obj(Obj::Nil);
            assert_eq!(gc.borrow().obj_pool.len(), 1);
            assert_eq!(gc.borrow().obj_pool[0].strong_count(), 1);
            assert_eq!(gc.borrow().obj_pool[0].weak_count(), 1);

            gc.borrow_mut().collect_no_handles();
            assert!(!gc.borrow().obj_pool.is_empty());
            assert!(handle.inner.upgrade().is_some());
        }

        gc.borrow_mut().collect_no_handles();
        assert!(gc.borrow().obj_pool.is_empty());

        {
            let rc = gc.borrow_mut().new_obj(Obj::Nil).get();
            assert_eq!(gc.borrow().obj_pool.len(), 1);
            assert_eq!(gc.borrow().obj_pool[0].strong_count(), 2);
            assert_eq!(gc.borrow().obj_pool[0].weak_count(), 0);

            gc.borrow_mut().collect_no_handles();
            assert!(!gc.borrow().obj_pool.is_empty());
            assert_eq!(rc.strong_count(), 2);
        }

        gc.borrow_mut().collect_no_handles();
        assert!(gc.borrow().obj_pool.is_empty());
    }
}
