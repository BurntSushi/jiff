use crate::{error, Unit};

#[derive(Clone, Debug)]
pub(crate) enum Error {
    FailedAddDays,
    FailedAddDurationOverflowing,
    FailedAddSpanDate,
    FailedAddSpanOverflowing,
    FailedAddSpanTime,
    IllegalTimeWithMicrosecond,
    IllegalTimeWithMillisecond,
    IllegalTimeWithNanosecond,
    InvalidISOWeekNumber,
    OverflowDaysDuration,
    OverflowTimeNanoseconds,
    RoundMustUseDaysOrBigger { unit: Unit },
    RoundMustUseHoursOrSmaller { unit: Unit },
}

impl From<Error> for error::Error {
    #[cold]
    #[inline(never)]
    fn from(err: Error) -> error::Error {
        error::ErrorKind::Civil(err).into()
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
            FailedAddDays => f.write_str("failed to add days to date"),
            FailedAddDurationOverflowing => {
                f.write_str("failed to add overflowing duration")
            }
            FailedAddSpanDate => f.write_str("failed to add span to date"),
            FailedAddSpanOverflowing => {
                f.write_str("failed to add overflowing span")
            }
            FailedAddSpanTime => f.write_str("failed to add span to time"),
            IllegalTimeWithMicrosecond => f.write_str(
                "cannot set both `TimeWith::microsecond` \
                 and `TimeWith::subsec_nanosecond`",
            ),
            IllegalTimeWithMillisecond => f.write_str(
                "cannot set both `TimeWith::millisecond` \
                 and `TimeWith::subsec_nanosecond`",
            ),
            IllegalTimeWithNanosecond => f.write_str(
                "cannot set both `TimeWith::nanosecond` \
                 and `TimeWith::subsec_nanosecond`",
            ),
            InvalidISOWeekNumber => {
                f.write_str("ISO week number is invalid for given year")
            }
            OverflowDaysDuration => f.write_str(
                "number of days derived from duration exceed's \
                 Jiff's datetime limits",
            ),
            OverflowTimeNanoseconds => {
                f.write_str("adding duration to time overflowed")
            }
            RoundMustUseDaysOrBigger { unit } => write!(
                f,
                "rounding the span between two dates must use days \
                 or bigger for its units, but found {unit}",
                unit = unit.plural(),
            ),
            RoundMustUseHoursOrSmaller { unit } => write!(
                f,
                "rounding the span between two times must use hours \
                 or smaller for its units, but found {unit}",
                unit = unit.plural(),
            ),
        }
    }
}
