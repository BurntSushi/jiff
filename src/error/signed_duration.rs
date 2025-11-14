use crate::{error, Unit};

#[derive(Clone, Debug)]
pub(crate) enum Error {
    ConvertNonFinite,
    ConvertSystemTime,
    RoundCalendarUnit { unit: Unit },
    RoundOverflowed { unit: Unit },
}

impl From<Error> for error::Error {
    #[cold]
    #[inline(never)]
    fn from(err: Error) -> error::Error {
        error::ErrorKind::SignedDuration(err).into()
    }
}

impl error::IntoError for Error {
    fn into_error(self) -> error::Error {
        self.into()
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use self::Error::*;

        match *self {
            ConvertNonFinite => f.write_str(
                "could not convert non-finite \
                 floating point seconds to signed duration \
                 (floating point seconds must be finite)",
            ),
            ConvertSystemTime => f.write_str(
                "failed to get duration between \
                 `std::time::SystemTime` values",
            ),
            RoundCalendarUnit { unit } => write!(
                f,
                "rounding `jiff::SignedDuration` failed because \
                 a calendar unit of '{plural}' was provided \
                 (to round by calendar units, you must use a `jiff::Span`)",
                plural = unit.plural(),
            ),
            RoundOverflowed { unit } => write!(
                f,
                "rounding signed duration to nearest {singular} \
                 resulted in a value outside the supported range \
                 of a `jiff::SignedDuration`",
                singular = unit.singular(),
            ),
        }
    }
}
