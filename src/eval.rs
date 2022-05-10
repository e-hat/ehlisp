use crate::ast::{Ast, Def};
use crate::gc::{Gc, GcHandle};
use crate::parse::Obj;

use std::cell::RefCell;
use std::clone::Clone;
use std::collections::HashMap;
use std::rc::Rc;

pub type Env = HashMap<String, Option<GcHandle<Obj>>>;

pub struct Context {
    env: Env,
    gc: Rc<RefCell<Gc>>,
}

type Error = String;
pub type Result<T> = std::result::Result<T, Error>;

// PRIMITIVE FUNCTIONS -- similar to closures, but they do not depend on any other existing
// environment objects.

// Expects args to be completely evaluated -- aka it will fail if not passed only Fixnum's
fn prim_plus(args: Vec<GcHandle<Obj>>, gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() <= 1 {
        Err(String::from("Expected at least two arguments for '+'"))
    } else {
        let mut sum: i32 = 0;
        for arg in args.iter() {
            if let Obj::Fixnum(n) = *arg.get().borrow() {
                sum += n;
            } else {
                return Err(format!(
                    "Expected fixnum as parameter to '+', got: {}",
                    arg.get().borrow()
                ));
            }
        }

        Ok(gc.new_obj(Obj::Fixnum(sum)))
    }
}

fn prim_pair(args: Vec<GcHandle<Obj>>, gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() != 2 {
        Err(String::from("Expected two arguments for 'pair'"))
    } else {
        Ok(gc.new_obj(Obj::Pair(args[0].clone(), args[1].clone())))
    }
}

fn prim_list(args: Vec<GcHandle<Obj>>, gc: &mut Gc) -> Result<GcHandle<Obj>> {
    Ok(Obj::from_vec(&args, gc))
}

fn prim_mul(args: Vec<GcHandle<Obj>>, gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() <= 1 {
        Err(String::from("Expected at least two arguments for '*'"))
    } else {
        let mut prod: i32 = 1;
        for arg in args.iter() {
            if let Obj::Fixnum(n) = *arg.get().borrow() {
                prod *= n;
            } else {
                return Err(format!(
                    "Expected fixnum as parameter to '*', got: {}",
                    arg.get().borrow()
                ));
            }
        }

        Ok(gc.new_obj(Obj::Fixnum(prod)))
    }
}

fn prim_sub(args: Vec<GcHandle<Obj>>, gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() != 2 {
        Err(String::from("Expected two arguments for '-'"))
    } else {
        match (&*args[0].get().borrow(), &*args[1].get().borrow()) {
            (Obj::Fixnum(l), Obj::Fixnum(r)) => Ok(gc.new_obj(Obj::Fixnum(l - r))),
            _ => Err(String::from(
                "Type Error: expected two ints as args for '-'",
            )),
        }
    }
}

fn prim_eq(args: Vec<GcHandle<Obj>>, gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() != 2 {
        Err(String::from("Expected two arguments for '='"))
    } else {
        Ok(gc.new_obj(Obj::Bool(args[0].get() == args[1].get())))
    }
}

fn prim_isatom(args: Vec<GcHandle<Obj>>, gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() != 1 {
        Err(String::from("Expected a single argument to 'atom?'"))
    } else {
        if let Obj::Pair(..) = &*args[0].get().borrow() {
            Ok(gc.new_obj(Obj::Bool(false)))
        } else {
            Ok(gc.new_obj(Obj::Bool(true)))
        }
    }
}

fn prim_car(args: Vec<GcHandle<Obj>>, _gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() != 1 {
        Err(String::from("Expected a single argument to 'car'"))
    } else {
        if let Obj::Pair(car, _) = &*args[0].get().borrow() {
            Ok(car.clone())
        } else {
            Err(format!(
                "Type Error: expected argument to 'car' to be a pair, got '{}'",
                args[0].get().borrow()
            ))
        }
    }
}

fn prim_cdr(args: Vec<GcHandle<Obj>>, _gc: &mut Gc) -> Result<GcHandle<Obj>> {
    if args.len() != 1 {
        Err(String::from("Expected a single argument to 'cdr'"))
    } else {
        if let Obj::Pair(_, cdr) = &*args[0].get().borrow() {
            Ok(cdr.clone())
        } else {
            Err(format!(
                "Type Error: expected argument to 'cdr' to be a pair, got '{}'",
                args[0].get().borrow()
            ))
        }
    }
}

// Defines the environment that evaluation begins with.
fn basis_env(gc: &mut Gc) -> Env {
    let mut res: Env = HashMap::new();
    res.insert(
        String::from("+"),
        Some(gc.new_obj(Obj::Primitive(String::from("+"), prim_plus))),
    );

    res.insert(
        String::from("pair"),
        Some(gc.new_obj(Obj::Primitive(String::from("pair"), prim_pair))),
    );

    res.insert(
        String::from("list"),
        Some(gc.new_obj(Obj::Primitive(String::from("list"), prim_list))),
    );

    res.insert(
        String::from("="),
        Some(gc.new_obj(Obj::Primitive(String::from("="), prim_eq))),
    );

    res.insert(
        String::from("-"),
        Some(gc.new_obj(Obj::Primitive(String::from("-"), prim_sub))),
    );

    res.insert(
        String::from("*"),
        Some(gc.new_obj(Obj::Primitive(String::from("*"), prim_mul))),
    );

    res.insert(
        String::from("atom?"),
        Some(gc.new_obj(Obj::Primitive(String::from("atom?"), prim_isatom))),
    );

    res.insert(
        String::from("car"),
        Some(gc.new_obj(Obj::Primitive(String::from("car"), prim_car))),
    );

    res.insert(
        String::from("cdr"),
        Some(gc.new_obj(Obj::Primitive(String::from("cdr"), prim_cdr))),
    );

    res
}

impl Context {
    pub fn new(gc: Rc<RefCell<Gc>>) -> Self {
        Context {
            env: basis_env(&mut *gc.borrow_mut()),
            gc: gc.clone(),
        }
    }

    pub fn eval(&mut self, ast: &GcHandle<Ast>) -> Result<GcHandle<Obj>> {
        if let Ast::DefAst(ref d) = *ast.get().borrow() {
            self.eval_def(d)
        } else {
            self.eval_ast(ast)
        }
    }

    fn eval_ast(&mut self, ast: &GcHandle<Ast>) -> Result<GcHandle<Obj>> {
        match &*ast.get().borrow() {
            Ast::Literal(l) => {
                if let Obj::Quote(inner) = &*l.get().borrow() {
                    Ok(inner.clone())
                } else {
                    Ok(l.clone())
                }
            }
            Ast::Var(name) => match self.env.get(name) {
                Some(Some(rhs)) => Ok(rhs.clone()),
                _ => Err(format!(
                    "Variable '{}' does not exist in the current environment",
                    name
                )),
            },
            Ast::If { pred, cons, alt } => match &*self.eval(pred)?.get().borrow() {
                Obj::Bool(true) => self.eval(cons),
                Obj::Bool(false) => self.eval(alt),
                res => Err(format!(
                    "Invalid predicate result for if statement: '{}', evaluated from '{}'",
                    res,
                    pred.get().borrow()
                )),
            },
            Ast::PairAccessor { pattern, arg } => {
                let first_pair = self.eval(arg)?;
                let x = if let Obj::Pair(..) = &*first_pair.get().borrow() {
                    let mut current = first_pair.clone();
                    for c in pattern.chars() {
                        let next = match (&*current.get().borrow(), c as u8) {
                            (Obj::Pair(car, _), b'a') => Ok(Some(car.clone())),
                            (Obj::Pair(_, cdr), b'd') => Ok(Some(cdr.clone())),
                            (Obj::Pair(..), _) => Err(format!(
                                "Got unexpected char '{}' in pair accessor '{}'",
                                c, pattern
                            )),
                            _ => Err(format!(
                                "Got non-pair argument to pair accessor. Got '{}'",
                                current.get().borrow()
                            )),
                        };
                        current = next?.unwrap();
                    }
                    Ok(current)
                } else {
                    unimplemented!()
                };
                x
            }
            Ast::And { l, r } => match (
                &*self.eval(l)?.get().borrow(),
                &*self.eval(r)?.get().borrow(),
            ) {
                (Obj::Bool(l_res), Obj::Bool(r_res)) => {
                    Ok(self.gc.borrow_mut().new_obj(Obj::Bool(*l_res && *r_res)))
                }
                _ => Err("Type error: (and bool bool)".to_string()),
            },
            Ast::Or { l, r } => match (
                &*self.eval(l)?.get().borrow(),
                &*self.eval(r)?.get().borrow(),
            ) {
                (Obj::Bool(l_res), Obj::Bool(r_res)) => {
                    Ok(self.gc.borrow_mut().new_obj(Obj::Bool(*l_res && *r_res)))
                }
                _ => Err("Type error: (or bool bool)".to_string()),
            },
            Ast::Apply { l, r } => match &mut *self.eval(l)?.get().borrow_mut() {
                Obj::Primitive(_, func) => {
                    let args = self.eval(r)?;
                    if args.get().borrow().is_list() {
                        func(args.get().borrow().to_vec(), &mut *self.gc.borrow_mut())
                    } else {
                        Err("Type Error: expected list as argument to function call".to_string())
                    }
                }
                Obj::Closure {
                    formal_args,
                    rhs,
                    env,
                } => {
                    let actuals_obj = self.eval(r)?;
                    if actuals_obj.get().borrow().is_list() {
                        // TODO: Investigate making a temp of the environment, altering the
                        // existing environment, evaluating and saving the result, setting the
                        // environment equal to the original saved in temp, then returning the
                        // result -- is this better/faster than what is happening here?
                        let actuals = actuals_obj.get().borrow().to_vec();
                        if actuals.len() != formal_args.len() {
                            Err("Incorrect number of args passed to closure".to_string())
                        } else {
                            let mut env_copy = env.clone();
                            for (formal, actual) in formal_args.iter().zip(actuals.iter()) {
                                env_copy.insert(formal.clone(), Some(actual.clone()));
                            }

                            let mut new_ctx = Context::new(self.gc.clone());
                            new_ctx.env = env_copy;
                            new_ctx.eval(rhs)
                        }
                    } else {
                        Err("Type Error: expected list as argument to function call".to_string())
                    }
                }
                _ => Err("Type Error: (apply prim '(args))".to_string()),
            },
            Ast::Call { f, args } => match &*self.eval(f)?.get().borrow() {
                Obj::Primitive(_, func) => {
                    let obj_args = args
                        .iter()
                        .map(|x| self.eval(x))
                        .collect::<Result<Vec<_>>>()?;
                    func(obj_args, &mut *self.gc.borrow_mut())
                }
                Obj::Closure {
                    formal_args,
                    rhs,
                    env,
                } => {
                    if formal_args.len() != args.len() {
                        Err("Incorrect number of args passed to closure".to_string())
                    } else {
                        let mut env_copy = env.clone();
                        for (formal, actual) in formal_args.iter().zip(args.iter()) {
                            env_copy.insert(formal.clone(), Some(self.eval(actual)?));
                        }

                        let mut new_ctx = Context::new(self.gc.clone());
                        new_ctx.env = env_copy;
                        new_ctx.eval(rhs)
                    }
                }
                _ => Err("Type Error: (f args)".to_string()),
            },
            Ast::Lambda { formal_args, rhs } => Ok(self.gc.borrow_mut().new_obj(Obj::Closure {
                formal_args: formal_args.clone(),
                rhs: rhs.clone(),
                env: self.env.clone(),
            })),
            Ast::DefAst(_) => unreachable!(),
        }
    }

    fn eval_def(&mut self, def: &Def) -> Result<GcHandle<Obj>> {
        match def {
            Def::Val { name, rhs } => {
                let res = self.eval(rhs)?;
                self.env.insert(name.clone(), Some(res.clone()));
                Ok(res)
            }
            Def::Def {
                name,
                formal_args,
                rhs,
            } => {
                let lambda = self.gc.borrow_mut().new_ast(Ast::Lambda {
                    formal_args: formal_args.clone(),
                    rhs: rhs.clone(),
                });
                let res = self.eval(&lambda)?;
                if let Obj::Closure {
                    formal_args: _,
                    rhs: _,
                    env: cl_env,
                } = &mut *res.get().borrow_mut()
                {
                    cl_env.insert(name.clone(), Some(res.clone()));
                    self.env.insert(name.clone(), Some(res.clone()));
                } else {
                    unreachable!()
                }
                Ok(res)
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

    use crate::gc::{Gc, GcHandle, GcData};
    use crate::parse::*;
    use crate::handle;

    macro_rules! test_case {
        ($name:ident, failure, $input:expr) => {
            #[test]
            fn $name() {
                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);
                let gc = Rc::new(RefCell::new(Gc::new()));
                let parse_res = stream.read_sexp(&mut *gc.borrow_mut()).unwrap();

                let ast_res = Ast::from_sexp(&parse_res, gc.clone()).unwrap();

                let mut ctx = Context::new(gc.clone());
                let res = ctx.eval(&ast_res);
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

                let ast_res = Ast::from_sexp(&parse_res, gc.clone()).unwrap();

                let mut ctx = Context::new(gc.clone());

                let res = ctx.eval(&ast_res);
                assert!(!res.is_err());
                assert_eq!(&*res.unwrap().get().borrow(), &$expected);
            }
        };
        ($name:ident, $prep_steps:expr, $input:expr, $expected:expr) => {
            #[test]
            fn $name() {
                let gc = Rc::new(RefCell::new(Gc::new()));
                let mut ctx = Context::new(gc.clone());
                for step in $prep_steps {
                    let input_str = String::from(step);
                    let mut input = input_str.as_bytes();
                    let mut stream = Stream::new(&mut input);
                    let parse_res = stream.read_sexp(&mut *gc.borrow_mut()).unwrap();

                    let ast_res = Ast::from_sexp(&parse_res, gc.clone()).unwrap();
                    assert!(!ctx.eval(&ast_res).is_err());
                }

                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);
                let parse_res = stream.read_sexp(&mut *gc.borrow_mut()).unwrap();

                let ast_res = Ast::from_sexp(&parse_res, gc.clone()).unwrap();
                let res = ctx.eval(&ast_res);
                assert!(!res.is_err());
                assert_eq!(&*res.unwrap().get().borrow(), &$expected);
            }
        };
    }

    test_case!(trivial_fixnum, "0", Obj::Fixnum(0));
    test_case!(trivial_bool, "#t", Obj::Bool(true));
    test_case!(trivial_nil, "()", Obj::Nil);
    test_case!(trivial_quote, "'a\n", Obj::Local("a".to_string()));

    test_case!(nonexistent_local, failure, "x\n");
    test_case!(local, ["(val x 5)"], "x\n", Obj::Fixnum(5));

    test_case!(plus, "(+ 1 2)", Obj::Fixnum(3));
    test_case!(wrong_types_plus, failure, "(+ #t #f)");
    test_case!(wrong_num_args_plus, failure, "(+ 0)");

    test_case!(
        pair,
        "(pair 1 2)",
        Obj::Pair(handle!(Obj::Fixnum(1)), handle!(Obj::Fixnum(2)))
    );
    test_case!(wrong_num_args_pair, failure, "(pair 1)");

    test_case!(
        list,
        "(list 1 2)",
        Obj::Pair(
            handle!(Obj::Fixnum(1)),
            handle!(Obj::Pair(handle!(Obj::Fixnum(2)), handle!(Obj::Nil)))
        )
    );
    test_case!(empty_list, "(list)", Obj::Nil);

    test_case!(call_wrong_type, failure, "(1 2 3)");

    test_case!(
        apply_with_list,
        "(apply + (list 1 2))",
        Obj::Fixnum(3)
    );
    test_case!(
        apply_with_quote,
        "(apply + '(1 2))",
        Obj::Fixnum(3)
    );
    test_case!(apply_plus_with_empty_args, failure, "(apply + '())");

    test_case!(
        closure_assign_to_var,
        ["(val add-one (lambda (x) (+ x 1)))"],
        "(add-one 0)",
        Obj::Fixnum(1)
    );
    test_case!(
        closure_called_in_closure,
        ["(val add-one (lambda (x) (+ x 1)))"],
        "(add-one (add-one 0))",
        Obj::Fixnum(2)
    );

    test_case!(
        define,
        ["(define f () 5)"],
        "(f)",
        Obj::Fixnum(5)
    );
    test_case!(
        factorial,
        ["(define factorial (n) (if (= n 1) 1 (* n (factorial (- n 1)))))"],
        "(factorial 5)",
        Obj::Fixnum(120)
    );

    test_case!(is_atom_true, "(atom? 1)", Obj::Bool(true));
    test_case!(
        is_atom_false,
        "(atom? (pair 0 1))",
        Obj::Bool(false)
    );

    test_case!(car, "(car (pair 1 2))", Obj::Fixnum(1));
    test_case!(cdr, "(cdr (pair 1 2))", Obj::Fixnum(2));

    test_case!(
        caadr,
        "(caadr (pair (pair (pair 1 2) 3) 4))",
        Obj::Fixnum(2)
    );
}
