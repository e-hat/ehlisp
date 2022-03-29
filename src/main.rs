mod parse;
mod eval;

use std::io;
use std::io::Write;

fn repl(stream: &mut parse::Stream) -> std::io::Result<()> {
    loop {
        print!("> ");
        io::stdout().flush()?;
        let sexp = stream.read_sexp()?;
        let res = eval::eval(sexp);
        println!("{}", res.borrow());
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
