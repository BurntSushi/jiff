/*!
TODO
*/

use core::ops::Range;

pub type TzifStatic = Tzif<
    &'static str,
    &'static [TzifLocalTimeType],
    &'static [TzifTransition],
>;

#[cfg(feature = "alloc")]
pub type TzifOwned = Tzif<
    alloc::string::String,
    alloc::vec::Vec<TzifLocalTimeType>,
    alloc::vec::Vec<TzifTransition>,
>;

#[derive(Debug)]
pub struct Tzif<STRING, TYPES, TRANS> {
    pub fixed: TzifFixed<STRING>,
    pub types: TYPES,
    pub transitions: TRANS,
}

#[derive(Debug)]
pub struct TzifFixed<STRING> {
    pub name: Option<STRING>,
    pub version: u8,
    pub checksum: u32,
    pub designations: STRING,
    pub posix_tz: Option<PosixTimeZone<STRING>>,
}

// only-jiff-impl-start
impl TzifFixed<&'static str> {
    pub const fn to_jiff(
        &self,
        types: &'static [crate::tz::tzif::LocalTimeType],
        trans: &'static [crate::tz::tzif::Transition],
    ) -> crate::tz::tzif::TzifStatic {
        crate::tz::tzif::TzifStatic::from_shared_const(self, types, trans)
    }
}
// only-jiff-impl-end

#[derive(Debug)]
pub struct TzifLocalTimeType {
    pub offset: i32,
    pub is_dst: bool,
    pub designation: Range<u8>,
    pub indicator: TzifIndicator,
}

// only-jiff-impl-start
impl TzifLocalTimeType {
    pub const fn to_jiff(&self) -> crate::tz::tzif::LocalTimeType {
        crate::tz::tzif::LocalTimeType::from_shared(self)
    }
}
// only-jiff-impl-end

#[derive(Debug)]
pub enum TzifIndicator {
    LocalWall,
    LocalStandard,
    UTStandard,
}

#[derive(Debug)]
pub struct TzifTransition {
    pub timestamp: i64,
    pub type_index: u8,
}

// only-jiff-impl-start
impl TzifTransition {
    pub const fn to_jiff(
        &self,
        prev_offset: i32,
        this_offset: i32,
    ) -> crate::tz::tzif::Transition {
        crate::tz::tzif::Transition::from_shared(
            self,
            prev_offset,
            this_offset,
        )
    }
}
// only-jiff-impl-end

#[derive(Debug, Eq, PartialEq)]
pub struct PosixTimeZone<ABBREV> {
    pub std_abbrev: ABBREV,
    pub std_offset: i32,
    pub dst: Option<PosixDst<ABBREV>>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct PosixDst<ABBREV> {
    pub abbrev: ABBREV,
    pub offset: i32,
    pub rule: Option<PosixRule>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct PosixRule {
    pub start: PosixDayTime,
    pub end: PosixDayTime,
}

#[derive(Debug, Eq, PartialEq)]
pub struct PosixDayTime {
    pub date: PosixDay,
    pub time: i32,
}

#[derive(Debug, Eq, PartialEq)]
pub enum PosixDay {
    /// Julian day in a year, no counting for leap days.
    ///
    /// Valid range is `1..=365`.
    JulianOne(i16),
    /// Julian day in a year, counting for leap days.
    ///
    /// Valid range is `0..=365`.
    JulianZero(i16),
    /// The nth weekday of a month.
    WeekdayOfMonth {
        /// The month.
        ///
        /// Valid range is: `1..=12`.
        month: i8,
        /// The week.
        ///
        /// Valid range is `1..=5`.
        ///
        /// One interesting thing to note here (or my interpretation anyway),
        /// is that a week of `4` means the "4th weekday in a month" where as
        /// a week of `5` means the "last weekday in a month, even if it's the
        /// 4th weekday."
        week: i8,
        /// The weekday.
        ///
        /// Valid range is `0..=6`, with `0` corresponding to Sunday.
        weekday: i8,
    },
}

// only-jiff-impl-start
impl PosixTimeZone<&'static str> {
    pub const fn to_jiff(&self) -> crate::tz::posix::ReasonablePosixTimeZone {
        crate::tz::posix::ReasonablePosixTimeZone::from_shared_const(self)
    }
}
// only-jiff-impl-end

// Does not require `alloc`, but is only used when `alloc` is enabled.
#[cfg(feature = "alloc")]
pub(crate) mod crc32;
#[cfg(feature = "alloc")]
pub(crate) mod posix;
#[cfg(feature = "alloc")]
pub(crate) mod tzif;
pub(crate) mod util;
