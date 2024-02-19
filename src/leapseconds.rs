use alloc::{vec, vec::Vec};

use crate::{
    civil::{Date, DateTime, Time},
    error::{err, Error, ErrorContext},
    instant::{Instant, Tai, Unix},
    tz::TimeZone,
    util::{
        parse,
        rangeint::{RFrom, RInto, TryRFrom},
        t::{self, C},
    },
};

/// The number of seconds that elapsed between the NTP epoch
/// (`1900-01-01T00:00:00Z`) and the Unix epoch (`1970-01-01T00:00:00Z`).
const NTP_UNIX_EPOCH_DIFFERENCE: i64 = 2208988800;

/// Leap seconds in NIST format, which is mostly a copy of the [IERS upstream
/// format].
///
/// Apparently the IERS data file isn't commonly used because of some bullshit
/// about copyright.
///
/// [IERA upstream format]: https://hpiers.obspm.fr/iers/bul/bulc/ntp/leap-seconds.list
static NIST: &'static [u8] = include_bytes!("data/leap-seconds.list");

/// Leap seconds in IANA format.
///
/// I'm not totally clear on why this format exists, but it expresses the same
/// thing as the NIST formatted data, but... in a different format. It is also
/// derived from the NIST data. Here are some differences I observed:
///
/// * The leap seconds specified in UTC. This is arguably more correct, because
/// this is to me how leap seconds are defined. But, it also makes the format
/// more annoying to parse and use. For example, it implies that you need a
/// way to go from civil datetimes to Unix timestamps. The NIST data instead
/// reports leap seconds in Unix time with a `1900-01-01T00:00:00Z` epoch.
/// * Each leap second is specified as a `+` or a `-`, where as in NIST,
/// each leap second reports the total accumulated offset. I find the NIST
/// representation easier to work with personally.
/// * The NIST data includes the 10 second offset at the start of UTC (Jan 1
/// 1972), where as the IANA data does not. The IANA data seems to omit it
/// because it doesn't technically denote a single leap second. But in my view,
/// it effectively denotes an accumulation of 10 leap seconds.
/// * The NIST data uses comments to denote the date immediately following the
/// leap second, where as the IANA UTC datetimes correspond to leap second
/// itself.
///
/// We just support both because it's not that hard to, and because it'd be
/// frustrating if you only had one format and not the other. For example, on
/// my Archlinux system, I have both `/usr/share/zoneinfo/leapseconds` (that's
/// IANA) and `/usr/share/zoneinfo/leap-seconds.list` (that's NIST), but on my
/// mac, all I have is `/usr/share/zoneinfo/leapseconds`. Fun times.
static IANA: &'static [u8] = include_bytes!("data/leapseconds");

#[derive(Debug, Eq, PartialEq)]
pub struct LeapSeconds {
    expires: Instant,
    by_unix: Vec<LeapSecondUnix>,
    by_tai: Vec<LeapSecondTai>,
}

impl LeapSeconds {
    pub fn builtin() -> LeapSeconds {
        LeapSeconds::from_nist_bytes(NIST)
            .expect("hard-coded leap seconds always parse correctly")
    }

    pub fn from_nist(data: &str) -> Result<LeapSeconds, Error> {
        parse_nist(data)
    }

    pub fn from_nist_bytes(data: &[u8]) -> Result<LeapSeconds, Error> {
        let data = core::str::from_utf8(data)
            .map_err(Error::adhoc)
            .context("invalid UTF-8")?;
        LeapSeconds::from_nist(data)
    }

    pub fn from_iana(data: &str) -> Result<LeapSeconds, Error> {
        parse_iana(data)
    }

    pub fn from_iana_bytes(data: &[u8]) -> Result<LeapSeconds, Error> {
        let data = core::str::from_utf8(data)
            .map_err(Error::adhoc)
            .context("invalid UTF-8")?;
        LeapSeconds::from_iana(data)
    }

    pub fn unix_to_tai(
        &self,
        instant: Instant<Unix>,
    ) -> Result<Instant<Tai>, Error> {
        let tai_timestamp =
            self.unix_to_tai_timestamp(instant.second_ranged())?;
        Ok(Instant::from_timestamp_ranged(
            tai_timestamp,
            instant.nanosecond_ranged(),
        ))
    }

    pub fn tai_to_unix(&self, instant: Instant<Tai>) -> Instant<Unix> {
        let (unix_timestamp, _) =
            self.tai_to_unix_timestamp(instant.second_ranged());
        Instant::from_timestamp_ranged(
            unix_timestamp,
            instant.nanosecond_ranged(),
        )
    }

    pub fn unix_to_tai_timestamp(
        &self,
        unix_timestamp: t::UnixSeconds,
    ) -> Result<t::TaiSeconds, Error> {
        let result = self
            .by_unix
            .binary_search_by(|ls| ls.timestamp.cmp(&unix_timestamp));
        let i = match result {
            Ok(i) => i,
            Err(i) if i == 0 => {
                return t::TaiSeconds::try_rfrom(
                    "unix-to-tai seconds",
                    unix_timestamp,
                );
            }
            Err(i) => i - 1,
        };
        let unix_timestamp = t::TaiSeconds::rfrom(unix_timestamp);
        Ok(unix_timestamp.try_checked_add(
            "unix-to-tai seconds",
            self.by_unix[i].leap_seconds,
        )?)
    }

    pub fn tai_to_unix_timestamp(
        &self,
        tai_timestamp: t::TaiSeconds,
    ) -> (t::UnixSeconds, bool) {
        let result = self
            .by_tai
            .binary_search_by(|ls| ls.timestamp.cmp(&tai_timestamp));
        let i = match result {
            Ok(i) => i,
            Err(i) if i == 0 => return (tai_timestamp.rinto(), false),
            Err(i) => i - 1,
        };
        // The leap second table is keyed by the first second *after* the leap
        // second. So we know we have a leap second when it is precisely one
        // less than the timestamp in the *next* entry.
        let is_leap = i
            .checked_add(1)
            .and_then(|i| self.by_tai.get(i))
            .and_then(|ls| ls.timestamp.checked_sub(C(1)))
            .map_or(false, |ts| ts == tai_timestamp);
        ((tai_timestamp + self.by_tai[i].leap_seconds).rinto(), is_leap)
    }
}

#[derive(Debug, Eq, PartialEq)]
struct LeapSecondTai {
    timestamp: t::TaiSeconds,
    leap_seconds: t::LeapSecondOffset,
}

#[derive(Debug, Eq, PartialEq)]
struct LeapSecondUnix {
    timestamp: t::UnixSeconds,
    leap_seconds: t::LeapSecondOffset,
}

impl LeapSecondUnix {
    /// Creates a new leap second for the given Unix timestamp and the leap
    /// second offset. This returns an error if the given values are not valid
    /// Unix timestamps in Jiff.
    fn new(
        timestamp: i64,
        leap_seconds: i64,
    ) -> Result<LeapSecondUnix, Error> {
        let timestamp =
            t::UnixSeconds::try_new("", timestamp).with_context(|| {
                err!("Unix timestamp {timestamp} is out of Jiff's range")
            })?;
        let leap_seconds = t::LeapSecondOffset::try_new("", leap_seconds)
            .with_context(|| {
                err!(
                    "leap second offset {leap_seconds} is out of Jiff's range"
                )
            })?;
        Ok(LeapSecondUnix { timestamp, leap_seconds })
    }

    /// Convert this leap second in terms of Unix time to TAI time.
    ///
    /// In effect, the corresponding TAI leap second is just the Unix time
    /// plus the number of leap seconds that have been added/subtracted since
    /// that point.
    fn to_tai(&self) -> Result<LeapSecondTai, Error> {
        let LeapSecondUnix { timestamp, leap_seconds } = *self;
        let timestamp = t::TaiSeconds::rfrom(timestamp)
            .try_checked_add("", leap_seconds)
            .with_context(|| {
                err!(
                    "overflow occurred when adding Unix timestamp \
                     {timestamp} to leap second offset {leap_seconds}",
                )
            })?;
        let leap_seconds = t::LeapSecondOffset::rfrom(-leap_seconds);
        Ok(LeapSecondTai { timestamp, leap_seconds })
    }
}

fn parse_nist(string: &str) -> Result<LeapSeconds, Error> {
    let mut expires: Option<Instant> = None;
    let mut by_unix = vec![];
    let mut by_tai = vec![];
    for line in string.lines() {
        if let Some(expires_str) = line.strip_prefix("#@") {
            if expires.is_some() {
                return Err(err!("found multiple expiration lines"));
            }
            let n = parse::i64(expires_str.trim().as_bytes()).with_context(
                || err!("failed to parse expiration timestamp from {line:?}"),
            )?;
            expires = Some(ntp_to_instant(n)?);
        } else if line.starts_with("#") || line.trim().is_empty() {
            continue;
        } else {
            let mut fields = line.trim().split_whitespace();
            let start_str = fields.next().ok_or_else(|| {
                err!(
                    "could not find first field in line {line:?} \
                     in NIST formatted leap second data",
                )
            })?;
            let offset_str = fields.next().ok_or_else(|| {
                err!(
                    "could not find second field in line {line:?} \
                     in NIST formatted leap second data",
                )
            })?;
            let ntp_timestamp = parse::i64(start_str.as_bytes())
                .with_context(|| {
                    err!("failed to parse NTP timestamp from {line:?}")
                })?;
            let timestamp = ntp_to_unix(ntp_timestamp).with_context(|| {
                err!("failed to convert NTP timestamp to Unix in {line:?}")
            })?;
            let leap_seconds = parse::i64(offset_str.as_bytes())
                .with_context(|| {
                    err!("failed to parse leap second offset in {line:?}")
                })?;
            let unix = LeapSecondUnix::new(timestamp, leap_seconds)
                .with_context(|| err!("out of Jiff's range in {line:?}"))?;
            let tai = unix.to_tai()?;
            by_unix.push(unix);
            by_tai.push(tai);
        }
    }
    let Some(expires) = expires else {
        return Err(err!(
            "could not find expiration in NIST formatted leap second data"
        ));
    };
    Ok(LeapSeconds { expires, by_unix, by_tai })
}

fn parse_iana(string: &str) -> Result<LeapSeconds, Error> {
    let mut expires: Option<Instant> = None;
    let mut by_unix = vec![];
    let mut by_tai = vec![];
    let mut leap_seconds: i64 = 9;
    // Add a dummy line corresponding to the initial 10 second offset.
    let init = "Leap	1971	Dec	31	23:59:60	+	S";
    for line in [init].into_iter().chain(string.lines()) {
        if let Some(expires_str) = line.strip_prefix("#Expires") {
            if expires.is_some() {
                return Err(err!("found multiple expiration lines"));
            }
            expires = Some(parse_iana_expires(expires_str)?);
        } else if let Some(expires_str) = line.strip_prefix("Expires") {
            if expires.is_some() {
                return Err(err!("found multiple expiration lines"));
            }
            expires = Some(parse_iana_expires(expires_str)?);
        } else if line.starts_with("#") || line.trim().is_empty() {
            continue;
        } else {
            let leap = line.strip_prefix("Leap").ok_or_else(|| {
                err!("expected 'Leap' prefix in line {line:?}")
            })?;
            let dt = if let Some((datetime_str, _)) = leap.split_once("+") {
                let dt = parse_iana_datetime(datetime_str)
                    .context("failed to parse leap second")?;
                leap_seconds = leap_seconds
                    .checked_add(1)
                    .ok_or_else(|| err!("leap second offset is too big"))?;
                dt
            } else if let Some((datetime_str, _)) = leap.split_once("-") {
                let dt = parse_iana_datetime(datetime_str)
                    .context("failed to parse leap second")?;
                leap_seconds = leap_seconds
                    .checked_sub(1)
                    .ok_or_else(|| err!("leap second offset is too small"))?;
                dt
            } else {
                return Err(err!(
                    "expected '+' or '-' in leap second line {line:?}"
                ));
            };
            let instant = TimeZone::UTC.to_instant(dt).with_context(|| {
                err!("leap second from line {line:?} is out of bounds")
            })?;
            let timestamp = instant.to_unix().0;
            let unix = LeapSecondUnix::new(timestamp, leap_seconds)
                .with_context(|| err!("out of Jiff's range in {line:?}"))?;
            let tai = unix.to_tai()?;
            by_unix.push(unix);
            by_tai.push(tai);
        }
    }
    let Some(expires) = expires else {
        return Err(err!(
            "could not find expiration in NIST formatted leap second data"
        ));
    };
    Ok(LeapSeconds { expires, by_unix, by_tai })
}

fn parse_iana_expires(expires_str: &str) -> Result<Instant, Error> {
    let dt = parse_iana_datetime(expires_str)
        .context("failed to parse expiration datetime")?;
    let instant = TimeZone::UTC
        .to_instant(dt)
        .context("expiration datetime out of bounds")?;
    Ok(instant)
}

fn parse_iana_datetime(datetime_str: &str) -> Result<DateTime, Error> {
    let mut fields = datetime_str.trim().split_whitespace();
    let year_str = fields.next().ok_or_else(|| {
        err!("could not find year field in {datetime_str:?}")
    })?;
    let month_str = fields.next().ok_or_else(|| {
        err!("could not find month field in {datetime_str:?}")
    })?;
    let day_str = fields
        .next()
        .ok_or_else(|| err!("could not find day field in {datetime_str:?}"))?;
    let time_str = fields.next().ok_or_else(|| {
        err!("could not find time field in {datetime_str:?}")
    })?;

    let mut time_fields = time_str.trim().split(':');
    let hour_str = time_fields
        .next()
        .ok_or_else(|| err!("could not find hour field in {time_str:?}"))?;
    let minute_str = time_fields
        .next()
        .ok_or_else(|| err!("could not find minute field in {time_str:?}"))?;
    let second_str = time_fields
        .next()
        .ok_or_else(|| err!("could not find second field in {time_str:?}"))?;

    let year64 = parse::i64(year_str.as_bytes())
        .with_context(|| err!("failed to parse year from {year_str:?}"))?;
    let year = t::Year::try_new("year", year64)?;

    let month = parse_iana_month(month_str)?;

    let day64 = parse::i64(day_str.as_bytes())
        .with_context(|| err!("failed to parse day from {day_str:?}"))?;
    let day = t::Day::try_new("day", day64)?;

    let hour64 = parse::i64(hour_str.as_bytes())
        .with_context(|| err!("failed to parse hour from {hour_str:?}"))?;
    let hour = t::Hour::try_new("hour", hour64)?;

    let minute64 = parse::i64(minute_str.as_bytes())
        .with_context(|| err!("failed to parse minute from {minute_str:?}"))?;
    let minute = t::Minute::try_new("minute", minute64)?;

    let mut second64 = parse::i64(second_str.as_bytes())
        .with_context(|| err!("failed to parse second from {second_str:?}"))?;
    let second = t::UtcSecond::try_new("second", second64)?;

    let date = Date::new_ranged(year, month, day)?;
    let time = Time::new_ranged(hour, minute, second);
    Ok(DateTime::from_parts(date, time))
}

fn parse_iana_month(month_str: &str) -> Result<t::Month, Error> {
    let n = match month_str {
        "Jan" => 1,
        "Feb" => 2,
        "Mar" => 3,
        "Apr" => 4,
        "May" => 5,
        "Jun" => 6,
        "Jul" => 7,
        "Aug" => 8,
        "Sep" => 9,
        "Oct" => 10,
        "Nov" => 11,
        "Dec" => 12,
        _ => return Err(err!("unrecognized month name {month_str:?}")),
    };
    Ok(t::Month::new_unchecked(n))
}

fn ntp_to_instant(ntp_timestamp: i64) -> Result<Instant, Error> {
    Instant::from_unix(ntp_to_unix(ntp_timestamp)?, 0).with_context(|| {
        err!(
            "Unix time (from NTP timestamp {ntp_timestamp}) overflows \
             allowed range in Jiff",
        )
    })
}

fn ntp_to_unix(ntp_timestamp: i64) -> Result<i64, Error> {
    ntp_timestamp.checked_sub(NTP_UNIX_EPOCH_DIFFERENCE).ok_or_else(|| {
        err!(
            "overflow when converting NTP timestamp \
            {ntp_timestamp} to Unix time"
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The leap seconds parsed from the NIST formatted file should be
    /// precisely equivalent to the leap seconds parsed from the IANA
    /// formatted file.
    #[test]
    fn equivalent() {
        let nist = LeapSeconds::from_nist_bytes(NIST).unwrap();
        let iana = LeapSeconds::from_iana_bytes(IANA).unwrap();
        assert_eq!(nist, iana);
    }

    #[test]
    fn nist() {
        insta::assert_debug_snapshot!(LeapSeconds::from_nist_bytes(NIST));
    }

    #[test]
    fn iana() {
        insta::assert_debug_snapshot!(LeapSeconds::from_iana_bytes(IANA));
    }
}
