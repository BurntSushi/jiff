mod civil;
mod span;

/// A type alias we use for tests.
///
/// I normally don't like using Results in unit tests, but... I had to write
/// *so* many tests when porting from TC39's 262 test suite that the `?` mark
/// was just easier to use.
type Result = std::result::Result<(), jiff::Error>;
