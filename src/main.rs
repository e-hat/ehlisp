mod ast;
mod eval;
mod parse;
mod gc;

use std::io;
use std::io::Write;
use std::io::{Error, ErrorKind};
use std::rc::Rc;
use std::cell::RefCell;

fn repl(stream: &mut parse::Stream) -> io::Result<()> {
    let gc = Rc::new(RefCell::new(gc::Gc::new()));
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
    }
}

fn main() {
    let mut stdin = io::stdin();
    let mut stream = parse::Stream::new(&mut stdin);
    match repl(&mut stream) {
        Ok(()) => println!("Goodbye! :]"),
        Err(msg) => println!("Error encountered:\n{}", msg),
    }
}
