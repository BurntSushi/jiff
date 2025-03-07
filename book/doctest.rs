// I had never used mdbook before I embarked on the journey of writing a book
// for Jiff. I recalled lots of people suggesting it. *Unbelievably*, the
// single most important requirement for me was that it could run the examples
// as tests. And it can't do it![1] So instead, we just smush all of the
// chapters into a single ad hoc Rust project, and then let `cargo test --doc`
// do the work.
//
// I don't understand how people persist with this nonsense. The official Rust
// book works around this by putting every single code listing in its own Cargo
// project. That is absolute madness! (OK OK, in the Rust book case, you do get
// the advantage of having multiple snippets reference one cohesive project.)
// If I wasn't able to find this work-around, I likely would have found another
// book generator or just written my own.
//
// I think the main downside here is that when a test fails, it can
// be tricky to know which code block it comes from. This is why we use a
// module for each chapter, instead of smushing them all together into one
// module (which we could do). It's not perfect, but it does help identify
// the origin of the failure somewhat. If this becomes A Big Deal, then I
// would probably solve it by writing a program to copy each code snippet
// from the book Markdown into Rust code, and make each code snippet its own
// function or module or whatever. With the line number of where the original
// code snippet started along with the basename of the Markdown file. That
// would give you a pretty good idea which test failed. It would also still
// retain "rustdoc doctest" semantics. All we'd have to do is pluck out the
// code fence blocks and copy them into rustdoc comments.
//
// TODO: Once this project is further along, post my technique here on the
// mdbook issue tracker[1]. I'm surprised that I don't see it there, because
// this by far seems like the least bad choice available today. No need to use
// preprocessors or different tools like rust-skeptic that don't work like
// `rustdoc`. No need to futz with `extern crate` even in Rust 2018+. It Just
// Works (mostly).
//
// [1]: https://github.com/rust-lang/mdBook/issues/394

#[doc = include_str!("src/chapter_1.md")]
pub mod chapter1 {}
#[doc = include_str!("src/appendix/specs.md")]
pub mod appendix_specs {}
