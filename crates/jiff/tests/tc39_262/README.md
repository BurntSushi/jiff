These tests come from [TC39's Test262] for the [Temporal proposal]. The tests
here try to mimic what's in Test262 as much as possible, but there are many
tests that are omitted because they are caught by Rust's type system. On
occasion, we diverge in behavior from Temporal. These differences are, to the
best of my ability, marked with `DIFFERENCE`.

These tests were ported by hand. There is, at time of writing, no mechanism
for ensuring they remain in sync with Test262. There's also no real way to
determine which tests were ported and which were not.

I've also omitted tests where I feel like they don't add much value.
For example, APIs like `Date::checked_sub` are just a negation of
`Date::checked_add`, so there's no real reason to duplicate all of Temporal's
`PlainDate.add` tests for both `Date::checked_add` and `Date::checked_sub`. A
similar argument applies for `Date::until` and `Date::since` and other datetime
types. (Not to say we should have zero tests, but such things usually have
unit tests and/or documentation tests.)

There are also a lot of tests that cover some of the more stringly-typed
aspects of Temporal's API. Namely, routines like `PlainDateTime.compare` accept
one of a `PlainDateTime`, or a property bag or a string that can be parsed to
a `PlainDateTime`. But in Jiff, if you want to compare a `civil::DateTime`,
you just need a `civil::DateTime`.

Overall, Temporal's tests are strict spec compliance tests for a dynamically
typed language. So we just try to take what is "useful" instead of attempting
a fool's errand of porting literally everything.

Of course, Temporal's test suite is vast. So it is not just plausible but
likely I have missed porting some tests because they are actually useful. So
if you think more should be added, please file an issue or just open a PR if
it's a smaller addition.

NOTE: I started porting tests with the `PlainTime` tests, and I ported more
than I should have. That is, I developed the above philosophy after porting too
many redundant tests.

[TC39's Test262]: https://github.com/tc39/test262/tree/9e03c403e73341658d8d485a673798ae61f6f94a/test/built-ins/Temporal
[Temporal proposal]: https://github.com/tc39/proposal-temporal
