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

    res
}

impl Context {
    pub fn new() -> Self {
        Context { env: basis_env() }
    }

    pub fn from(env: Env) -> Self {
        Context { env }
    }

    pub fn eval(&mut self, ast: Rc<RefCell<Ast>>) -> Result<Rc<RefCell<Obj>>> {
        if let Ast::DefAst(ref d) = *ast.borrow() {
            self.eval_def(d)
        } else {
            self.eval_ast(ast.clone())
        }
    }

    fn eval_ast(&mut self, ast: Rc<RefCell<Ast>>) -> Result<Rc<RefCell<Obj>>> {
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
            Ast::If { pred, cons, alt } => match &*self.eval(pred.clone())?.borrow() {
                Obj::Bool(true) => self.eval(cons.clone()),
                Obj::Bool(false) => self.eval(alt.clone()),
                res => Err(format!(
                    "Invalid predicate result for if statement: '{}', evaluated from '{}'",
                    res,
                    pred.borrow()
                )),
            },
            Ast::And { l, r } => match (
                &*self.eval(l.clone())?.borrow(),
                &*self.eval(r.clone())?.borrow(),
            ) {
                (Obj::Bool(l_res), Obj::Bool(r_res)) => Ok(wrap!(Obj::Bool(*l_res && *r_res))),
                _ => Err("Type error: (and bool bool)".to_string()),
            },
            Ast::Or { l, r } => match (
                &*self.eval(l.clone())?.borrow(),
                &*self.eval(r.clone())?.borrow(),
            ) {
                (Obj::Bool(l_res), Obj::Bool(r_res)) => Ok(wrap!(Obj::Bool(*l_res && *r_res))),
                _ => Err("Type error: (or bool bool)".to_string()),
            },
            Ast::Apply { l, r } => match &mut *self.eval(l.clone())?.borrow_mut() {
                Obj::Primitive(_, func) => {
                    let args = self.eval(r.clone())?;
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
                    let actuals_obj = self.eval(r.clone())?;
                    if actuals_obj.borrow().is_list() {
                        // TODO: Investigate making a temp of the environment, altering the
                        // existing environment, evaluating and saving the result, setting the
                        // environment equal to the original saved in temp, then returning the
                        // result -- is this better/faster than what is happening here?
                        let actuals = actuals_obj.borrow().to_vec();
                        let mut env_copy = env.clone();
                        for (formal, actual) in formal_args.iter().zip(actuals.iter()) {
                            env_copy.insert(formal.clone(), Some(actual.clone()));
                        }

                        Context::from(env_copy).eval(rhs.clone())
                    } else {
                        Err("Type Error: expected list as argument to function call".to_string())
                    }
                }
                _ => Err("Type Error: (apply prim '(args))".to_string()),
            },
            Ast::Call { f, args } => match &*self.eval(f.clone())?.borrow() {
                Obj::Primitive(_, func) => {
                    let obj_args = args
                        .iter()
                        .map(|x| self.eval(x.clone()))
                        .collect::<Result<Vec<_>>>()?;
                    func(obj_args)
                }
                Obj::Closure {
                    formal_args,
                    rhs,
                    env,
                } => {
                    let mut env_copy = env.clone();
                    for (formal, actual) in formal_args.iter().zip(args.iter()) {
                        env_copy.insert(formal.clone(), Some(self.eval(actual.clone())?));
                    }

                    Context::from(env_copy).eval(rhs.clone())
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
                let res = self.eval(rhs.clone())?;
                self.env.insert(name.clone(), Some(res.clone()));
                Ok(res)
            }
            Def::Def { .. } => {
                unimplemented!()
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

                let ast_res = Ast::from_sexp(parse_res).unwrap();

                let mut ctx = Context::new();
                let res = ctx.eval(ast_res.clone());
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

                let ast_res = Ast::from_sexp(parse_res).unwrap();

                let mut ctx = Context::new();
                let res = ctx.eval(ast_res.clone());
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

                    let ast_res = Ast::from_sexp(parse_res).unwrap();
                    assert!(!ctx.eval(ast_res.clone()).is_err());
                }

                let input_str = String::from($input);
                let mut input = input_str.as_bytes();
                let mut stream = Stream::new(&mut input);
                let parse_res = stream.read_sexp().unwrap();

                let ast_res = Ast::from_sexp(parse_res).unwrap();
                let res = ctx.eval(ast_res.clone());
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
}
