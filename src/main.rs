#![feature(test)]

mod ast;
mod eval;
mod gc;
mod parse;

use std::cell::RefCell;
use std::io;
use std::io::Write;
use std::io::{Error, ErrorKind};
use std::rc::Rc;

use gc::GcGraphNode;

fn repl(stream: &mut parse::Stream, gc: &Rc<RefCell<gc::Gc>>) -> io::Result<()> {
    let mut ctx = eval::Context::new(gc.clone());
    loop {
        print!("> ");
        io::stdout().flush()?;
        let input = stream.read_sexp(&mut *gc.borrow_mut())?;
        match ast::Ast::from_sexp(&input, gc.clone()) {
            Ok(ref sexp) => match ctx.eval(sexp) {
                Ok(res) => println!("{}", res.get().borrow()),
                Err(msg) => return Err(Error::new(ErrorKind::Other, msg)),
            },
            Err(msg) => return Err(Error::new(ErrorKind::Other, msg)),
        }
        gc.borrow_mut().collect(ctx.neighbors());
    }
}

fn main() {
    let mut stdin = io::stdin();
    let mut stream = parse::Stream::new(&mut stdin);
    let gc = Rc::new(RefCell::new(gc::Gc::new()));
    match repl(&mut stream, &gc) {
        Ok(()) => println!("Goodbye! :]"),
        Err(msg) => println!("Error encountered:\n{}", msg),
    }
}
