pub use self::{
    date::{Date, DateSeries},
    datetime::{DateTime, DateTimeSeries},
    iso_week_date::ISOWeekDate,
    time::{Time, TimeSeries},
    weekday::{Weekday, WeekdaysForward, WeekdaysReverse},
};

mod date;
mod datetime;
mod iso_week_date;
mod time;
mod weekday;

/// The era corresponding to a particular year.
///
/// The BCE era corresponds to years less than or equal to `0`, while the CE
/// era corresponds to years greater than `0`.
///
/// In particular, this crate allows years to be negative and also to be `0`,
/// which is contrary to the common practice of excluding the year `0` when
/// writing dates for the Gregorian calendar. Moreover, common practice eschews
/// negative years in favor of labeling a year with an era notation. That is,
/// the year `1 BCE` is year `0` in this crate. The year `2 BCE` is the year
/// `-1` in this crate.
///
/// To get the year in its era format, use [`Date::era_year`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Era {
    /// The "before common era" era.
    ///
    /// This corresponds to all years less than or equal to `0`.
    ///
    /// This is precisely equivalent to the "BC" or "before Christ" era.
    BCE,
    /// The "common era" era.
    ///
    /// This corresponds to all years greater than `0`.
    ///
    /// This is precisely equivalent to the "AD" or "anno Domini" or "in the
    /// year of the Lord" era.
    CE,
}
