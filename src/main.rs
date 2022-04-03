mod eval;
mod parse;
mod ast;

use std::io;
use std::io::Write;
use std::io::{Error, ErrorKind};

fn repl(stream: &mut parse::Stream) -> io::Result<()> {
    let mut ctx = eval::Context::new();
    loop {
        print!("> ");
        io::stdout().flush()?;
        let sexp = stream.read_sexp()?;
        match ctx.eval(sexp) {
            Ok(res) => println!("{}", res.borrow()),
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
