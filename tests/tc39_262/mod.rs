/// A type alias we use for tests.
///
/// I normally don't like using Results in unit tests, but... I had to write
/// *so* many tests when porting from TC39's 262 test suite that the `?` mark
/// was just easier to use.
type Result = std::result::Result<(), jiff::Error>;

/// A macro helper, only used in tests, for comparing spans for equality.
macro_rules! span_eq {
    ($span1:expr, $span2:expr $(,)?) => {{
        assert_eq!($span1.fieldwise(), $span2.fieldwise());
    }};
    ($span1:expr, $span2:expr, $($tt:tt)*) => {{
        assert_eq!($span1.fieldwise(), $span2.fieldwise(), $($tt)*);
    }};
}

mod civil;
mod span;
