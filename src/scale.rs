use core::{
    fmt::Debug,
    ops::{Add, Div, Mul, Rem, Sub},
};

use crate::{
    error::Error,
    util::{
        rangeint::{ri64, RInto, RangedDebug, TryRFrom},
        t::{
            FractionalNanosecond, SpanSeconds, SubsecNanosecond, TaiSeconds,
            UnixSeconds,
        },
    },
};

pub trait TimeScale: TimeScaleInternal {}
impl<S: TimeScaleInternal> TimeScale for S {}

#[derive(Clone, Copy, Debug, Default)]
pub struct Unix;

#[derive(Clone, Copy, Debug, Default)]
pub struct Tai;

pub(crate) trait TimeScaleInternal: Clone + Copy {
    type Seconds: Seconds;

    fn name() -> &'static str;

    fn from_unix_timestamp(
        unix_second: UnixSeconds,
    ) -> Result<Self::Seconds, Error>;

    fn to_unix_timestamp(scale_second: Self::Seconds) -> UnixSeconds;
}

pub(crate) trait Seconds:
    Copy
    + Clone
    + Debug
    + Eq
    + PartialEq
    + PartialOrd
    + Ord
    + Add
    + Sub
    + Mul
    + Div
    + Rem
{
    fn new(val: i64) -> Option<Self>;

    fn from_span_seconds(val: SpanSeconds) -> Self;

    fn try_from_span_seconds(val: SpanSeconds) -> Result<Self, Error>;

    fn to_span_seconds(self) -> SpanSeconds;

    fn get(self) -> i64;
}

/*
impl TimeScaleInternal for super::Unix {
    type Seconds = UnixSeconds;

    fn name() -> &'static str {
        "UNIX"
    }

    fn from_unix_time(
        unix_time_seconds: UnixSeconds,
        unix_time_nanos: FractionalNanosecond,
    ) -> Result<(UnixSeconds, FractionalNanosecond), Error> {
        Ok((unix_time_seconds, unix_time_nanos))
    }

    fn to_unix_time(
        scale_time_seconds: UnixSeconds,
        scale_time_nanos: FractionalNanosecond,
    ) -> (UnixSeconds, FractionalNanosecond) {
        (scale_time_seconds, scale_time_nanos)
    }
}

impl Seconds for UnixSeconds {
    fn new(val: i64) -> Option<Self> {
        UnixSeconds::new(val)
    }

    fn from_span_seconds(val: SpanSeconds) -> Self {
        val.rinto()
    }

    fn try_from_span_seconds(val: SpanSeconds) -> Result<Self, Error> {
        Self::try_rfrom("instant-seconds", val)
    }

    fn to_span_seconds(self) -> SpanSeconds {
        self.rinto()
    }

    fn get(self) -> i64 {
        UnixSeconds::get(self)
    }
}
*/
