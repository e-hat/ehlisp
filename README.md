# ehlisp
## About/Roadmap
- [x] ~~I am currently translating [this tutorial](https://bernsteinbear.com/blog/lisp/00_fundamentals/) 
into rust.~~ I'm all done! I've got a working lisp interpreter! 
- [ ] I'm doing garbage collection now! I am piggy-backing off of the existing reference counting provided by rust's `Rc` and `Weak` pointers. I absolutely REFUSE to use `unsafe`! This is also already working, I just need to implement sweeping. Then I wanna do sweeping and actual execution on different threads. We'll see how that goes.
- [ ] I'm scared to say it but, JIT compilation would be super cool? It sounds quite difficult. Maybe I'll be able to 
look at some existing LISP compilers and try to do similar stuff. I just gotta start simple and build from there. I'll definitely 
be using LLVM/cranelift/however that works in rust for this.

This is also my first ever time using rust! I am currently loving it. I can't believe I survive in C++ without pattern
matching, which has been amazing for traversing the ASTs and S-expressions. Also, programming in rust has made me 
think a lot more about the memory lifetimes in my program, which is fun and has already made me better at C++.

## Pronunciation
"eh-lisp", like "Eh", followed by "lisp"
