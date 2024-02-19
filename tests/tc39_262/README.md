These tests come from [TC39's Test262] for the [Temporal proposal]. The tests
here try to mimic what's in Test262 as much as possible, but there are many
tests that are omitted because they are caught by Rust's type system. On
occasion, we diverge in behavior from Temporal. These differences are, to the
best of my ability, marked with `DIFFERENCE`.

These tests were ported by hand. There is, at time of writing, no mechanism for
ensuring they remain in sync with Test262.

[TC39's Test262]: https://github.com/tc39/test262/tree/9e03c403e73341658d8d485a673798ae61f6f94a/test/built-ins/Temporal
[Temporal proposal]: https://github.com/tc39/proposal-temporal

# TODO

These are some test files that I came across while porting things that I
couldn't quite write yet. For example, tests that require parsing ISO 8601
duration strings, since the parsing code doesn't exist yet (at time of writing,
2024-03-06).

I tried to list what I could as `TODO` comments in the test files.
