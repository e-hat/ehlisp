mod parse;

use std::io;
use std::io::Write;

fn repl(stream: &mut parse::Stream) -> std::io::Result<()> {
    loop {
        print!("> ");
        io::stdout().flush()?;
        let s = stream.read_sexp()?;
        println!("{}", s);
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
