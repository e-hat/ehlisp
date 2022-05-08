use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{Ast, Def};
use crate::parse::Obj;
use crate::{wrap, wrap_t};

pub type Env = HashMap<String, Option<wrap_t!(Obj)>>;

pub struct Context {
    env: Env,
}

type Error = String;
pub type Result<T> = std::result::Result<T, Error>;

// PRIMITIVE FUNCTIONS -- similar to closures, but they do not depend on any other existing
// environment objects.

// Expects args to be completely evaluated -- aka it will fail if not passed only Fixnum's
fn prim_plus(args: Vec<Rc<RefCell<Obj>>>) -> Result<Rc<RefCell<Obj>>> {
    if args.len() <= 1 {
        Err(String::from("Expected at least two arguments for '+'"))
    } else {
        let mut sum: i32 = 0;
        for arg in args.iter() {
            if let Obj::Fixnum(n) = *arg.borrow() {
                sum += n;
            } else {
                return Err(format!(
                    "Expected fixnum as parameter to '+', got: {}",
                    arg.borrow()
                ));
            }
        }

        Ok(wrap!(Obj::Fixnum(sum)))
    }
}

fn prim_pair(args: Vec<Rc<RefCell<Obj>>>) -> Result<Rc<RefCell<Obj>>> {
    if args.len() != 2 {
        Err(String::from("Expected two arguments for 'pair'"))
    } else {
        Ok(wrap!(Obj::Pair(args[0].clone(), args[1].clone(),)))
    }
}

fn prim_list(args: Vec<Rc<RefCell<Obj>>>) -> Result<Rc<RefCell<Obj>>> {
    Ok(Obj::from_vec(&args))
}

fn prim_mul(args: Vec<Rc<RefCell<Obj>>>) -> Result<Rc<RefCell<Obj>>> {
    if args.len() <= 1 {
        Err(String::from("Expected at least two arguments for '*'"))
    } else {
        let mut prod: i32 = 1;
        for arg in args.iter() {
            if let Obj::Fixnum(n) = *arg.borrow() {
                prod *= n;
            } else {
                return Err(format!(
                    "Expected fixnum as parameter to '*', got: {}",
                    arg.borrow()
                ));
            }
        }

        Ok(wrap!(Obj::Fixnum(prod)))
    }
}

fn prim_sub(args: Vec<wrap_t!(Obj)>) -> Result<wrap_t!(Obj)> {
    if args.len() != 2 {
        Err(String::from("Expected two arguments for '-'"))
    } else {
        match (&*args[0].borrow(), &*args[1].borrow()) {
            (Obj::Fixnum(l), Obj::Fixnum(r)) => Ok(wrap!(Obj::Fixnum(l - r))),
            _ => Err(String::from(
                "Type Error: expected two ints as args for '-'",
            )),
        }
    }
}

fn prim_eq(args: Vec<wrap_t!(Obj)>) -> Result<wrap_t!(Obj)> {
    if args.len() != 2 {
        Err(String::from("Expected two arguments for '='"))
    } else {
        Ok(wrap!(Obj::Bool(args[0] == args[1])))
    }
}

fn prim_isatom(args: Vec<wrap_t!(Obj)>) -> Result<wrap_t!(Obj)> {
    if args.len() != 1 {
        Err(String::from("Expected a single argument to 'atom?'"))
    } else {
        if let Obj::Pair(..) = &*args[0].borrow() {
            Ok(wrap!(Obj::Bool(false)))
        } else {
            Ok(wrap!(Obj::Bool(true)))
        }
    }
}

fn prim_car(args: Vec<wrap_t!(Obj)>) -> Result<wrap_t!(Obj)> {
    if args.len() != 1 {
        Err(String::from("Expected a single argument to 'car'"))
    } else {
        if let Obj::Pair(car, _) = &*args[0].borrow() {
            Ok(car.clone())
        } else {
            Err(format!("Type Error: expected argument to 'car' to be a pair, got '{}'", args[0].borrow()))
        }
    }
}

fn prim_cdr(args: Vec<wrap_t!(Obj)>) -> Result<wrap_t!(Obj)> {
    if args.len() != 1 {
        Err(String::from("Expected a single argument to 'cdr'"))
    } else {
        if let Obj::Pair(_, cdr) = &*args[0].borrow() {
            Ok(cdr.clone())
        } else {
            Err(format!("Type Error: expected argument to 'cdr' to be a pair, got '{}'", args[0].borrow()))
        }
    }
}

// Defines the environment that evaluation begins with.
fn basis_env() -> Env {
    let mut res: Env = HashMap::new();
    res.insert(
        String::from("+"),
        Some(wrap!(Obj::Primitive(String::from("+"), prim_plus))),
    );

    res.insert(
        String::from("pair"),
        Some(wrap!(Obj::Primitive(String::from("pair"), prim_pair))),
    );

    res.insert(
        String::from("list"),
        Some(wrap!(Obj::Primitive(String::from("list"), prim_list))),
    );

    res.insert(
        String::from("="),
        Some(wrap!(Obj::Primitive(String::from("="), prim_eq))),
    );

    res.insert(
        String::from("-"),
        Some(wrap!(Obj::Primitive(String::from("-"), prim_sub))),
    );

    res.insert(
        String::from("*"),
        Some(wrap!(Obj::Primitive(String::from("*"), prim_mul))),
    );

    res.insert(
        String::from("atom?"),
        Some(wrap!(Obj::Primitive(String::from("atom?"), prim_isatom))),
    );

    res.insert(
        String::from("car"),
        Some(wrap!(Obj::Primitive(String::from("car"), prim_car))),
        );

    res.insert(
        String::from("cdr"),
        Some(wrap!(Obj::Primitive(String::from("cdr"), prim_cdr))),
    );

    res
}

impl Context {
    pub fn new() -> Self {
        Context { env: basis_env() }
    }

    pub fn from(env: Env) -> Self {
        Context { env }
    }

    pub fn eval(&mut self, ast: &Rc<RefCell<Ast>>) -> Result<Rc<RefCell<Obj>>> {
        if let Ast::DefAst(ref d) = *ast.borrow() {
            self.eval_def(d)
        } else {
            self.eval_ast(ast)
        }
    }

    fn eval_ast(&mut self, ast: &Rc<RefCell<Ast>>) -> Result<Rc<RefCell<Obj>>> {
        match &*ast.borrow() {
            Ast::Literal(l) => {
                if let Obj::Quote(inner) = &*l.borrow() {
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
            Ast::If { pred, cons, alt } => match &*self.eval(pred)?.borrow() {
                Obj::Bool(true) => self.eval(cons),
                Obj::Bool(false) => self.eval(alt),
                res => Err(format!(
                    "Invalid predicate result for if statement: '{}', evaluated from '{}'",
                    res,
                    pred.borrow()
                )),
            },
            Ast::PairAccessor { pattern, arg } => {
                let first_pair = self.eval(arg)?;
                let x = if let Obj::Pair( .. ) = &*first_pair.borrow() {
                    let mut current = first_pair.clone();
                    for c in pattern.chars() {
                        let mut next: Option<wrap_t!(Obj)> = None;
                        match (&*current.borrow(), c as u8) {
                            (Obj::Pair(car, _), b'a') => {
                                next = Some(car.clone())
                            },
                            (Obj::Pair(_, cdr), b'd') => {
                                next = Some(cdr.clone());
                            },
                            (Obj::Pair( .. ), _) => {
                                return Err(format!("Got unexpected char '{}' in pair accessor '{}'", c, pattern))
                            },
                            _ => {
                                return Err(format!("Got non-pair argument to pair accessor. Got '{}'", current.borrow()))
                            },
                        };
                        current = next.unwrap();
                    }
                    Ok(current)
                } else {
                    unimplemented!()
                }; x
            },
            Ast::And { l, r } => match (&*self.eval(l)?.borrow(), &*self.eval(r)?.borrow()) {
                (Obj::Bool(l_res), Obj::Bool(r_res)) => Ok(wrap!(Obj::Bool(*l_res && *r_res))),
                _ => Err("Type error: (and bool bool)".to_string()),
            },
            Ast::Or { l, r } => match (&*self.eval(l)?.borrow(), &*self.eval(r)?.borrow()) {
                (Obj::Bool(l_res), Obj::Bool(r_res)) => Ok(wrap!(Obj::Bool(*l_res && *r_res))),
                _ => Err("Type error: (or bool bool)".to_string()),
            },
            Ast::Apply { l, r } => match &mut *self.eval(l)?.borrow_mut() {
                Obj::Primitive(_, func) => {
                    let args = self.eval(r)?;
                    if args.borrow().is_list() {
                        func(args.borrow().to_vec())
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
                    if actuals_obj.borrow().is_list() {
                        // TODO: Investigate making a temp of the environment, altering the
                        // existing environment, evaluating and saving the result, setting the
                        // environment equal to the original saved in temp, then returning the
                        // result -- is this better/faster than what is happening here?
                        let actuals = actuals_obj.borrow().to_vec();
                        if actuals.len() != formal_args.len() {
                            Err("Incorrect number of args passed to closure".to_string())
                        } else {
                            let mut env_copy = env.clone();
                            for (formal, actual) in formal_args.iter().zip(actuals.iter()) {
                                env_copy.insert(formal.clone(), Some(actual.clone()));
                            }

                            Context::from(env_copy).eval(rhs)
                        }
                    } else {
                        Err("Type Error: expected list as argument to function call".to_string())
                    }
                }
                _ => Err("Type Error: (apply prim '(args))".to_string()),
            },
            Ast::Call { f, args } => match &*self.eval(f)?.borrow() {
                Obj::Primitive(_, func) => {
                    let obj_args = args
                        .iter()
                        .map(|x| self.eval(x))
                        .collect::<Result<Vec<_>>>()?;
                    func(obj_args)
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

                        Context::from(env_copy).eval(rhs)
                    }
                }
                _ => Err("Type Error: (f args)".to_string()),
            },
            Ast::Lambda { formal_args, rhs } => Ok(wrap!(Obj::Closure {
                formal_args: formal_args.clone(),
                rhs: rhs.clone(),
                env: self.env.clone()
            })),
            Ast::DefAst(_) => unreachable!(),
        }
    }

    fn eval_def(&mut self, def: &Def) -> Result<Rc<RefCell<Obj>>> {
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
                let res = self.eval(&wrap!(Ast::Lambda {
                    formal_args: formal_args.clone(),
                    rhs: rhs.clone()
                }))?;
                if let Obj::Closure {
                    formal_args: _,
                    rhs: _,
                    env: cl_env,
                } = &mut *res.borrow_mut()
                {
                    // Memory leak happens here. If this line is commented mem does not leak.
                    // cl_env contains res, which contains cl_env. Simple?
                    cl_env.insert(name.clone(), Some(res.clone()));
                    // This is also possibly a mem leak.
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

    use crate::parse::*;
    use crate::wrap;

    macro_rules! test_case {
        ($name:ident, failure, $input:expr) => {
            #[test]
            fn $name() {
                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);
                let parse_res = stream.read_sexp().unwrap();

                let ast_res = Ast::from_sexp(&parse_res).unwrap();

                let mut ctx = Context::new();
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
                let parse_res = stream.read_sexp().unwrap();

                let ast_res = Ast::from_sexp(&parse_res).unwrap();

                let mut ctx = Context::new();
                let res = ctx.eval(&ast_res);
                assert!(!res.is_err());
                assert_eq!(res.unwrap(), $expected);
            }
        };
        ($name:ident, $prep_steps:expr, $input:expr, $expected:expr) => {
            #[test]
            fn $name() {
                let mut ctx = Context::new();
                for step in $prep_steps {
                    let input_str = String::from(step);
                    let mut input = input_str.as_bytes();
                    let mut stream = Stream::new(&mut input);
                    let parse_res = stream.read_sexp().unwrap();

                    let ast_res = Ast::from_sexp(&parse_res).unwrap();
                    assert!(!ctx.eval(&ast_res).is_err());
                }

                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);
                let parse_res = stream.read_sexp().unwrap();

                let ast_res = Ast::from_sexp(&parse_res).unwrap();
                let res = ctx.eval(&ast_res);
                assert!(!res.is_err());
                assert_eq!(res.unwrap(), $expected);
            }
        };
    }

    test_case!(trivial_fixnum, "0", wrap!(Obj::Fixnum(0)));
    test_case!(trivial_bool, "#t", wrap!(Obj::Bool(true)));
    test_case!(trivial_nil, "()", wrap!(Obj::Nil));
    test_case!(trivial_quote, "'a\n", wrap!(Obj::Local("a".to_string())));

    test_case!(nonexistent_local, failure, "x\n");
    test_case!(local, ["(val x 5)"], "x\n", wrap!(Obj::Fixnum(5)));

    test_case!(plus, "(+ 1 2)", wrap!(Obj::Fixnum(3)));
    test_case!(wrong_types_plus, failure, "(+ #t #f)");
    test_case!(wrong_num_args_plus, failure, "(+ 0)");

    test_case!(
        pair,
        "(pair 1 2)",
        wrap!(Obj::Pair(wrap!(Obj::Fixnum(1)), wrap!(Obj::Fixnum(2))))
    );
    test_case!(wrong_num_args_pair, failure, "(pair 1)");

    test_case!(
        list,
        "(list 1 2 3)",
        Obj::from_vec(&vec![
            wrap!(Obj::Fixnum(1)),
            wrap!(Obj::Fixnum(2)),
            wrap!(Obj::Fixnum(3))
        ])
    );
    test_case!(empty_list, "(list)", wrap!(Obj::Nil));

    test_case!(call_wrong_type, failure, "(1 2 3)");

    test_case!(
        apply_with_list,
        "(apply + (list 1 2))",
        wrap!(Obj::Fixnum(3))
    );
    test_case!(apply_with_quote, "(apply + '(1 2))", wrap!(Obj::Fixnum(3)));
    test_case!(apply_plus_with_empty_args, failure, "(apply + '())");

    test_case!(
        closure_assign_to_var,
        ["(val add-one (lambda (x) (+ x 1)))"],
        "(add-one 0)",
        wrap!(Obj::Fixnum(1))
    );
    test_case!(
        closure_called_in_closure,
        ["(val add-one (lambda (x) (+ x 1)))"],
        "(add-one (add-one 0))",
        wrap!(Obj::Fixnum(2))
    );

    test_case!(define, ["(define f () 5)"], "(f)", wrap!(Obj::Fixnum(5)));
    test_case!(
        factorial,
        ["(define factorial (n) (if (= n 1) 1 (* n (factorial (- n 1)))))"],
        "(factorial 5)",
        wrap!(Obj::Fixnum(120))
    );

    test_case!(
        is_atom_true,
        "(atom? 1)",
        wrap!(Obj::Bool(true))
    );
    test_case!(
        is_atom_false,
        "(atom? (pair 0 1))",
        wrap!(Obj::Bool(false))
    );

    test_case!(
        car,
        "(car (pair 1 2))",
        wrap!(Obj::Fixnum(1))
    );
    test_case!(
        cdr,
        "(cdr (pair 1 2))",
        wrap!(Obj::Fixnum(2))
    );
    
    test_case!(
        caadr,
        "(caadr (pair (pair (pair 1 2) 3) 4))",
        wrap!(Obj::Fixnum(2))
    );
}
