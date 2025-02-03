/// Creates a new ad hoc error via `format_args!`.
macro_rules! err {
    ($($tt:tt)*) => {{
        crate::error::Error::adhoc_from_args(format_args!($($tt)*))
    }}
}

pub(crate) use err;

/// An error that can occur when converting between types in this crate.
#[derive(Clone, Debug)]
pub struct Error {
    kind: ErrorKind,
}

impl Error {
    /// Creates an error from an arbitrary `core::fmt::Arguments`.
    ///
    /// When `alloc` isn't enabled, then `Arguments::as_str()` is used to
    /// find an error message. Otherwise, a generic error message is emitted.
    pub(crate) fn adhoc_from_args<'a>(
        message: core::fmt::Arguments<'a>,
    ) -> Error {
        let kind = ErrorKind::Adhoc(AdhocError::from_args(message));
        Error { kind }
    }
}

#[derive(Clone, Debug)]
enum ErrorKind {
    Adhoc(AdhocError),
    Jiff(jiff::Error),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self.kind {
            ErrorKind::Adhoc(ref err) => {
                core::fmt::Display::fmt(&err.message, f)
            }
            ErrorKind::Jiff(ref err) => err.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self.kind {
            ErrorKind::Adhoc(_) => None,
            ErrorKind::Jiff(ref err) => Some(err),
        }
    }
}

impl From<jiff::Error> for Error {
    fn from(e: jiff::Error) -> Error {
        Error { kind: ErrorKind::Jiff(e) }
    }
}

/// A generic error message.
#[derive(Clone, Debug)]
struct AdhocError {
    #[cfg(feature = "alloc")]
    message: alloc::boxed::Box<str>,
    #[cfg(not(feature = "alloc"))]
    message: &'static str,
}

impl AdhocError {
    fn from_args<'a>(message: core::fmt::Arguments<'a>) -> AdhocError {
        #[cfg(feature = "alloc")]
        {
            AdhocError::from_display(message)
        }
        #[cfg(not(feature = "alloc"))]
        {
            let message = message.as_str().unwrap_or(
                "unknown `jiff-icu` error (better error messages require \
                 enabling the `alloc` feature for the `jiff-icu` crate)",
            );
            AdhocError::from_static_str(message)
        }
    }

    #[cfg(feature = "alloc")]
    fn from_display<'a>(message: impl core::fmt::Display + 'a) -> AdhocError {
        use alloc::string::ToString;

        let message = message.to_string().into_boxed_str();
        AdhocError { message }
    }

    #[cfg(not(feature = "alloc"))]
    fn from_static_str(message: &'static str) -> AdhocError {
        AdhocError { message }
    }
}
