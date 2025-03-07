The Jiff Book
=============
This directory contains the source code for the Jiff book found at
https://jiff.rs

The Jiff Book is versioned and tied to releases of `jiff` itself. By default,
going to https://jiff.rs will redirect you to https://jiff.rs/latest. But you
can also go to, for example, https://jiff.rs/0.2.3 to see the book as it
existed when `jiff 0.2.3` was released.

### Inside Baseball

This marks my first time using [mdBook], and it's missing two features that I
think are critical to enabling frictionless writing:

* It can't easily test code snippets that rely on crates other than the
standard library. A book about Jiff is going to have lots of code snippets
using Jiff, and it wouldn't be practical to write if they weren't checked.
* I can't easily link to _versioned_ items in Jiff's API on docs.rs. Not only
would I need to write out the full links to each item, but managing the
versions would be tricky. I already lived through years of doing that with
`rustdoc` before it introduced intra crate links, and the result was major
annoyance, fewer hyperlinks and dead links.

I've "fixed" these two issues for this book specifically.

For the first issue, [`./doctest.rs`](./doctest.rs) is used to embed every
Markdown file as a `rustdoc` comment. `rustdoc` then does the work of picking
up and testing code snippets. At time of writing (2025-03-07), I manually add
each Markdown file. But I might add a `jiff-cli generate` command to do this
for me based on the contents of `./src`.

For the second issue, I wrote a [mdBook preprocessor] in the form of a
[heinous Python script]. It first builds up a map of API items by crawling
the `./target/doc/` directory, where the keys are API item paths (e.g.,
`jiff::tz::TimeZone`) and the values are URL suffixes that can be appended
to versioned `docs.rs` URLs (e.g., `/jiff/tz/struct.TimeZone.html`). It then
extracts the versions of all crates in use from [`./Cargo.lock`](./Cargo.lock).
Then it uses regexes to replace Markdown links, like the intra doc links that
`rustdoc` supports, with full versioned permalinks.

The end result is that we get a book that not only emits versioned links, but
can _itself_ be versioned. So if you're using a specific version of Jiff, then
you can also read the corresponding version of The Jiff Book.

[mdBook]: https://rust-lang.github.io/mdBook/index.html
[mdBook preprocessor]: https://rust-lang.github.io/mdBook/for_developers/preprocessors.html
[heinous Python script]: ../scripts/mdbook-docsrs
