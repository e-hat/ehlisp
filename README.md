# ehlisp
## About/Roadmap
- [x] ~~I am currently translating [this tutorial](https://bernsteinbear.com/blog/lisp/00_fundamentals/) 
into rust.~~ I'm all done! I've got a working lisp interpr`eter! 
- [ ] I'm doing garbage collection now! 
* I am using `Weak` pointers as my handles throughout my program. I will keep a list of `Rc` inside the GC
that will be checked periodically, before a collection, whether it contains any active pointers other than the one owned by the Gc. 
* If not, then I will clean up that pointer. Then, I have to do a mark/sweep of the pointers in the current `env` to clean up any `Weak` cycles, 
which I have found do not leak memory, but do not get cleaned up until the Gc goes out of scope, which still isn't good.
* I also think the that special `Rc`/`Weak` collection trick for easily finding garbage pointers could be done in parallel with the marking stage of GC. The two will never touch the same pointers, which is perfect.
- [ ] I'm scared to say it but, JIT compilation would be super cool? It sounds quite difficult. Maybe I'll be able to 
look at some existing LISP compilers and try to do similar stuff. I just gotta start simple and build from there. I'll definitely 
be using LLVM/cranelift/however that works in rust for this.

This is also my first ever time using rust! I am currently loving it. I can't believe I survive in C++ without pattern
matching, which has been amazing for traversing the ASTs and S-expressions. Also, programming in rust has made me 
think a lot more about the memory lifetimes in my program, which is fun and has already made me better at C++.

## Pronunciation
"eh-lisp", like "Eh", followed by "lisp"
