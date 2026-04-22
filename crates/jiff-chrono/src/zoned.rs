use chrono::{
    DateTime as ChronoDateTime, FixedOffset as ChronoFixedOffset, Utc,
};
use jiff::{
    tz::{Offset as JiffOffset, TimeZone as JiffTimeZone},
    Timestamp as JiffTimestamp, Zoned as JiffZoned,
};

use crate::{
    error::Error,
    traits::{ConvertFrom, ConvertInto as _, ConvertTryFrom, ConvertTryInto as _},
};

#[cfg(feature = "chrono-tz")]
use crate::error::err;

/// Converts from a [`jiff::Zoned`] to a
/// [`chrono::DateTime<FixedOffset>`](chrono::DateTime).
///
/// The offset on the resulting value is the active offset of the zoned
/// instant (i.e. `zoned.offset()`), not the time zone's identity. The
/// IANA zone name, if any, is discarded. Round-tripping through
/// `DateTime<FixedOffset>` therefore loses DST-awareness.
///
/// **This is lossy.** If you need to preserve zone identity across a
/// round trip, enable the `chrono-tz` feature and convert to
/// [`chrono::DateTime<chrono_tz::Tz>`](chrono::DateTime) instead. See the
/// "Semantics caveats" section of the crate docs.
///
/// This conversion is fallible because Jiff's [`jiff::tz::Offset`] range
/// (`±25:59:59`) is wider than chrono's `FixedOffset` range (`±23:59:59`).
/// In practice, every IANA time zone's actual offset fits within chrono's
/// range.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let zdt: jiff::Zoned =
///     "2025-01-30T17:58:30-05[America/New_York]".parse()?;
/// let cdt = chrono::DateTime::<chrono::FixedOffset>::convert_try_from(&zdt)?;
/// assert_eq!(cdt.to_rfc3339(), "2025-01-30T17:58:30-05:00");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl<'a> ConvertTryFrom<&'a JiffZoned> for ChronoDateTime<ChronoFixedOffset> {
    type Error = Error;

    fn convert_try_from(
        v: &'a JiffZoned,
    ) -> Result<ChronoDateTime<ChronoFixedOffset>, Error> {
        let offset: ChronoFixedOffset = v.offset().convert_try_into()?;
        let utc: ChronoDateTime<Utc> = v.timestamp().convert_into();
        Ok(utc.with_timezone(&offset))
    }
}

/// Converts from a [`jiff::Zoned`] to a
/// [`chrono::DateTime<FixedOffset>`](chrono::DateTime) by value.
impl ConvertTryFrom<JiffZoned> for ChronoDateTime<ChronoFixedOffset> {
    type Error = Error;

    fn convert_try_from(
        v: JiffZoned,
    ) -> Result<ChronoDateTime<ChronoFixedOffset>, Error> {
        ChronoDateTime::<ChronoFixedOffset>::convert_try_from(&v)
    }
}

/// Converts from a [`chrono::DateTime<FixedOffset>`](chrono::DateTime) to a
/// [`jiff::Zoned`].
///
/// The resulting `Zoned` uses a fixed-offset time zone
/// ([`jiff::tz::TimeZone::fixed`]). It does not carry any IANA zone
/// identity, since chrono's `FixedOffset` carries none.
///
/// This conversion is fallible: it can fail if the chrono value falls
/// outside Jiff's supported timestamp range or represents a leap second.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let cdt = chrono::DateTime::parse_from_rfc3339(
///     "2025-01-30T17:58:30-05:00",
/// )?;
/// let zdt = jiff::Zoned::convert_try_from(cdt)?;
/// assert_eq!(zdt.to_string(), "2025-01-30T17:58:30-05:00[-05:00]");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<ChronoDateTime<ChronoFixedOffset>> for JiffZoned {
    type Error = Error;

    fn convert_try_from(
        v: ChronoDateTime<ChronoFixedOffset>,
    ) -> Result<JiffZoned, Error> {
        let offset = JiffOffset::convert_from(*v.offset());
        let ts = JiffTimestamp::convert_try_from(v)?;
        Ok(ts.to_zoned(JiffTimeZone::fixed(offset)))
    }
}

/// Converts from a [`chrono::DateTime<Utc>`](chrono::DateTime) to a
/// [`jiff::Zoned`] in UTC.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let cdt: chrono::DateTime<chrono::Utc> =
///     "2025-01-30T17:58:30Z".parse()?;
/// let zdt = jiff::Zoned::convert_try_from(cdt)?;
/// assert_eq!(zdt.to_string(), "2025-01-30T17:58:30+00:00[UTC]");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<ChronoDateTime<Utc>> for JiffZoned {
    type Error = Error;

    fn convert_try_from(
        v: ChronoDateTime<Utc>,
    ) -> Result<JiffZoned, Error> {
        let ts = JiffTimestamp::convert_try_from(v)?;
        Ok(ts.to_zoned(JiffTimeZone::UTC))
    }
}

/// Converts from a [`jiff::Zoned`] to a
/// [`chrono::DateTime<chrono_tz::Tz>`](chrono::DateTime).
///
/// This conversion uses the Jiff time zone's IANA identifier to look up the
/// corresponding [`chrono_tz::Tz`]. It fails if:
///
/// * The Jiff time zone is not IANA-named (e.g. a fixed-offset zone, an
///   unknown zone, or a POSIX-rule-only zone).
/// * chrono-tz's bundled database does not recognize the identifier.
///
/// Note that `jiff` and `chrono-tz` ship with independent copies of the
/// IANA time zone database. If the two databases disagree about offsets
/// for a given instant (e.g. because one is newer than the other), the
/// converted value's local clock reading may not match the original. This
/// crate does not try to detect such skew.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let zdt: jiff::Zoned =
///     "2025-01-30T17:58:30-05[America/New_York]".parse()?;
/// let cdt =
///     chrono::DateTime::<chrono_tz::Tz>::convert_try_from(&zdt)?;
/// assert_eq!(cdt.timezone(), chrono_tz::America::New_York);
/// assert_eq!(cdt.to_rfc3339(), "2025-01-30T17:58:30-05:00");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "chrono-tz")]
#[cfg_attr(docsrs_jiff, doc(cfg(feature = "chrono-tz")))]
impl<'a> ConvertTryFrom<&'a JiffZoned> for ChronoDateTime<chrono_tz::Tz> {
    type Error = Error;

    fn convert_try_from(
        v: &'a JiffZoned,
    ) -> Result<ChronoDateTime<chrono_tz::Tz>, Error> {
        use core::str::FromStr as _;

        let Some(name) = v.time_zone().iana_name() else {
            return Err(err!(
                "cannot convert Jiff `Zoned` to `chrono::DateTime<Tz>`: \
                 time zone has no IANA name",
            ));
        };
        let tz = chrono_tz::Tz::from_str(name).map_err(|_| {
            err!(
                "cannot convert Jiff `Zoned` to `chrono::DateTime<Tz>`: \
                 `chrono-tz` does not recognize IANA name {name:?}",
            )
        })?;
        let utc: ChronoDateTime<Utc> = v.timestamp().convert_into();
        Ok(utc.with_timezone(&tz))
    }
}

/// Converts from a [`jiff::Zoned`] to a
/// [`chrono::DateTime<chrono_tz::Tz>`](chrono::DateTime) by value.
#[cfg(feature = "chrono-tz")]
#[cfg_attr(docsrs_jiff, doc(cfg(feature = "chrono-tz")))]
impl ConvertTryFrom<JiffZoned> for ChronoDateTime<chrono_tz::Tz> {
    type Error = Error;

    fn convert_try_from(
        v: JiffZoned,
    ) -> Result<ChronoDateTime<chrono_tz::Tz>, Error> {
        ChronoDateTime::<chrono_tz::Tz>::convert_try_from(&v)
    }
}

/// Converts from a [`chrono::DateTime<chrono_tz::Tz>`](chrono::DateTime) to a
/// [`jiff::Zoned`].
///
/// The resulting `Zoned` is anchored to the same instant as the input and
/// uses the same IANA time zone name, looked up via
/// [`jiff::tz::TimeZone::get`].
///
/// This conversion fails if Jiff cannot find the zone identifier in its
/// database, or if the instant falls outside Jiff's supported range.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let cdt = chrono::DateTime::parse_from_rfc3339(
///     "2025-01-30T17:58:30-05:00",
/// )?.with_timezone(&chrono_tz::America::New_York);
/// let zdt = jiff::Zoned::convert_try_from(cdt)?;
/// assert_eq!(
///     zdt.to_string(),
///     "2025-01-30T17:58:30-05:00[America/New_York]",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "chrono-tz")]
#[cfg_attr(docsrs_jiff, doc(cfg(feature = "chrono-tz")))]
impl ConvertTryFrom<ChronoDateTime<chrono_tz::Tz>> for JiffZoned {
    type Error = Error;

    fn convert_try_from(
        v: ChronoDateTime<chrono_tz::Tz>,
    ) -> Result<JiffZoned, Error> {
        let name = v.timezone().name();
        let tz = JiffTimeZone::get(name)?;
        let ts = JiffTimestamp::convert_try_from(v)?;
        Ok(ts.to_zoned(tz))
    }
}

/// Converts from a [`jiff::tz::TimeZone`] to a [`chrono_tz::Tz`].
///
/// Uses the Jiff zone's IANA identifier, looked up against chrono-tz's
/// bundled database. This conversion fails if:
///
/// * The Jiff time zone has no IANA name (e.g. a fixed-offset zone, the
///   unknown zone, or a POSIX-rule-only zone).
/// * chrono-tz's bundled database does not recognize the identifier.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let jiff_tz = jiff::tz::TimeZone::get("America/New_York")?;
/// let chrono_tz = chrono_tz::Tz::convert_try_from(&jiff_tz)?;
/// assert_eq!(chrono_tz, chrono_tz::America::New_York);
///
/// // Fixed-offset zones have no IANA name, so they are rejected.
/// let fixed = jiff::tz::TimeZone::fixed(jiff::tz::offset(-5));
/// assert!(chrono_tz::Tz::convert_try_from(&fixed).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "chrono-tz")]
#[cfg_attr(docsrs_jiff, doc(cfg(feature = "chrono-tz")))]
impl<'a> ConvertTryFrom<&'a JiffTimeZone> for chrono_tz::Tz {
    type Error = Error;

    fn convert_try_from(v: &'a JiffTimeZone) -> Result<chrono_tz::Tz, Error> {
        use core::str::FromStr as _;

        let Some(name) = v.iana_name() else {
            return Err(err!(
                "cannot convert Jiff `TimeZone` to `chrono_tz::Tz`: \
                 time zone has no IANA name",
            ));
        };
        chrono_tz::Tz::from_str(name).map_err(|_| {
            err!(
                "cannot convert Jiff `TimeZone` to `chrono_tz::Tz`: \
                 `chrono-tz` does not recognize IANA name {name:?}",
            )
        })
    }
}

/// Converts from a [`jiff::tz::TimeZone`] to a [`chrono_tz::Tz`] by value.
#[cfg(feature = "chrono-tz")]
#[cfg_attr(docsrs_jiff, doc(cfg(feature = "chrono-tz")))]
impl ConvertTryFrom<JiffTimeZone> for chrono_tz::Tz {
    type Error = Error;

    fn convert_try_from(v: JiffTimeZone) -> Result<chrono_tz::Tz, Error> {
        chrono_tz::Tz::convert_try_from(&v)
    }
}

/// Converts from a [`chrono_tz::Tz`] to a [`jiff::tz::TimeZone`].
///
/// Uses the chrono-tz identifier's IANA name to look up the zone in
/// Jiff's time zone database. In practice this fails only if the running
/// system's tzdb is missing an identifier that chrono-tz knows about,
/// which is rare but possible on minimal containers.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let chrono_tz = chrono_tz::Asia::Tokyo;
/// let jiff_tz = jiff::tz::TimeZone::convert_try_from(chrono_tz)?;
/// assert_eq!(jiff_tz.iana_name(), Some("Asia/Tokyo"));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "chrono-tz")]
#[cfg_attr(docsrs_jiff, doc(cfg(feature = "chrono-tz")))]
impl ConvertTryFrom<chrono_tz::Tz> for JiffTimeZone {
    type Error = Error;

    fn convert_try_from(v: chrono_tz::Tz) -> Result<JiffTimeZone, Error> {
        Ok(JiffTimeZone::get(v.name())?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_offset_roundtrip() {
        let zdt: JiffZoned =
            "2025-01-30T17:58:30-05[America/New_York]".parse().unwrap();
        let cdt: ChronoDateTime<ChronoFixedOffset> =
            ChronoDateTime::<ChronoFixedOffset>::convert_try_from(&zdt)
                .unwrap();
        let back = JiffZoned::convert_try_from(cdt).unwrap();
        // The IANA zone identity is discarded by this round trip.
        assert_eq!(back.timestamp(), zdt.timestamp());
        assert!(back.time_zone().iana_name().is_none());
    }

    #[test]
    fn utc_roundtrip() {
        let cdt: ChronoDateTime<Utc> =
            "2025-01-30T17:58:30Z".parse().unwrap();
        let zdt = JiffZoned::convert_try_from(cdt).unwrap();
        assert_eq!(zdt.time_zone().iana_name(), Some("UTC"));
    }

    #[cfg(feature = "chrono-tz")]
    #[test]
    fn chrono_tz_named_roundtrip() {
        let zdt: JiffZoned =
            "2025-01-30T17:58:30-05[America/New_York]".parse().unwrap();
        let cdt: ChronoDateTime<chrono_tz::Tz> =
            ChronoDateTime::<chrono_tz::Tz>::convert_try_from(&zdt).unwrap();
        assert_eq!(cdt.timezone(), chrono_tz::America::New_York);
        let back = JiffZoned::convert_try_from(cdt).unwrap();
        assert_eq!(back.timestamp(), zdt.timestamp());
        assert_eq!(
            back.time_zone().iana_name(),
            Some("America/New_York"),
        );
    }

    #[cfg(feature = "chrono-tz")]
    #[test]
    fn chrono_tz_fixed_offset_jiff_zone_is_rejected() {
        let zdt = jiff::Timestamp::from_second(0).unwrap().to_zoned(
            JiffTimeZone::fixed(JiffOffset::from_seconds(-5 * 3600).unwrap()),
        );
        assert!(
            ChronoDateTime::<chrono_tz::Tz>::convert_try_from(&zdt).is_err(),
        );
    }

    #[cfg(feature = "chrono-tz")]
    #[test]
    fn timezone_standalone_roundtrip() {
        use crate::traits::ConvertTryInto as _;

        let jiff_tz = JiffTimeZone::get("Asia/Tokyo").unwrap();
        let chrono_tz: chrono_tz::Tz = (&jiff_tz).convert_try_into().unwrap();
        assert_eq!(chrono_tz, chrono_tz::Asia::Tokyo);
        let back: JiffTimeZone = chrono_tz.convert_try_into().unwrap();
        assert_eq!(back.iana_name(), Some("Asia/Tokyo"));
    }

    #[cfg(feature = "chrono-tz")]
    #[test]
    fn timezone_fixed_is_rejected_for_chrono_tz() {
        let fixed = JiffTimeZone::fixed(
            JiffOffset::from_seconds(-5 * 3600).unwrap(),
        );
        assert!(chrono_tz::Tz::convert_try_from(&fixed).is_err());
    }
}
