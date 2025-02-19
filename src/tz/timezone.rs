use crate::{
    civil::DateTime,
    error::{err, Error},
    tz::{
        ambiguous::{AmbiguousOffset, AmbiguousTimestamp, AmbiguousZoned},
        offset::{Dst, Offset},
    },
    util::{array_str::ArrayStr, sync::Arc},
    Timestamp, Zoned,
};

#[cfg(feature = "alloc")]
use crate::tz::posix::ReasonablePosixTimeZone;

/// A representation of a [time zone].
///
/// A time zone is a set of rules for determining the civil time, via an offset
/// from UTC, in a particular geographic region. In many cases, the offset
/// in a particular time zone can vary over the course of a year through
/// transitions into and out of [daylight saving time].
///
/// A `TimeZone` can be one of three possible representations:
///
/// * An identifier from the [IANA Time Zone Database] and the rules associated
/// with that identifier.
/// * A fixed offset where there are never any time zone transitions.
/// * A [POSIX TZ] string that specifies a standard offset and an optional
/// daylight saving time offset along with a rule for when DST is in effect.
/// The rule applies for every year. Since POSIX TZ strings cannot capture the
/// full complexity of time zone rules, they generally should not be used.
///
/// The most practical and useful representation is an IANA time zone. Namely,
/// it enjoys broad support and its database is regularly updated to reflect
/// real changes in time zone rules throughout the world. On Unix systems,
/// the time zone database is typically found at `/usr/share/zoneinfo`. For
/// more information on how Jiff interacts with The Time Zone Database, see
/// [`TimeZoneDatabase`](crate::tz::TimeZoneDatabase).
///
/// In typical usage, users of Jiff shouldn't need to reference a `TimeZone`
/// directly. Instead, there are convenience APIs on datetime types that accept
/// IANA time zone identifiers and do automatic database lookups for you. For
/// example, to convert a timestamp to a zone aware datetime:
///
/// ```
/// use jiff::Timestamp;
///
/// let ts = Timestamp::from_second(1_456_789_123)?;
/// let zdt = ts.in_tz("America/New_York")?;
/// assert_eq!(zdt.to_string(), "2016-02-29T18:38:43-05:00[America/New_York]");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Or to convert a civil datetime to a zoned datetime corresponding to a
/// precise instant in time:
///
/// ```
/// use jiff::civil::date;
///
/// let dt = date(2024, 7, 15).at(21, 27, 0, 0);
/// let zdt = dt.in_tz("America/New_York")?;
/// assert_eq!(zdt.to_string(), "2024-07-15T21:27:00-04:00[America/New_York]");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Or even converted a zoned datetime from one time zone to another:
///
/// ```
/// use jiff::civil::date;
///
/// let dt = date(2024, 7, 15).at(21, 27, 0, 0);
/// let zdt1 = dt.in_tz("America/New_York")?;
/// let zdt2 = zdt1.in_tz("Israel")?;
/// assert_eq!(zdt2.to_string(), "2024-07-16T04:27:00+03:00[Israel]");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # The system time zone
///
/// The system time zone can be retrieved via [`TimeZone::system`]. If it
/// couldn't be detected or if the `tz-system` crate feature is not enabled,
/// then [`TimeZone::UTC`] is returned. `TimeZone::system` is what's used
/// internally for retrieving the current zoned datetime via [`Zoned::now`].
///
/// While there is no platform independent way to detect your system's
/// "default" time zone, Jiff employs best-effort heuristics to determine it.
/// (For example, by examining `/etc/localtime` on Unix systems.) When the
/// heuristics fail, Jiff will emit a `WARN` level log. It can be viewed by
/// installing a `log` compatible logger, such as [`env_logger`].
///
/// # Custom time zones
///
/// At present, Jiff doesn't provide any APIs for manually constructing a
/// custom time zone. However, [`TimeZone::tzif`] is provided for reading
/// any valid TZif formatted data, as specified by [RFC 8536]. This provides
/// an interoperable way of utilizing custom time zone rules.
///
/// # A `TimeZone` is immutable
///
/// Once a `TimeZone` is created, it is immutable. That is, its underlying
/// time zone transition rules will never change. This is true for system time
/// zones or even if the IANA Time Zone Database it was loaded from changes on
/// disk. The only way such changes can be observed is by re-requesting the
/// `TimeZone` from a `TimeZoneDatabase`. (Or, in the case of the system time
/// zone, by calling `TimeZone::system`.)
///
/// # A `TimeZone` is cheap to clone
///
/// A `TimeZone` can be cheaply cloned. It uses automic reference counting
/// internally. When `alloc` is disabled, cloning a `TimeZone` is still cheap
/// because POSIX time zones and TZif time zones are unsupported. Therefore,
/// cloning a time zone does a deep copy (since automic reference counting is
/// not available), but the data being copied is small.
///
/// # Time zone equality
///
/// `TimeZone` provides an imperfect notion of equality. That is, when two time
/// zones are equal, then it is guaranteed for them to have the same rules.
/// However, two time zones may compare unequal and yet still have the same
/// rules.
///
/// The equality semantics are as follows:
///
/// * Two fixed offset time zones are equal when their offsets are equal.
/// * Two POSIX time zones are equal when their original rule strings are
/// byte-for-byte identical.
/// * Two IANA time zones are equal when their identifiers are equal _and_
/// checksums of their rules are equal.
/// * In all other cases, time zones are unequal.
///
/// Time zone equality is, for example, used in APIs like [`Zoned::since`]
/// when asking for spans with calendar units. Namely, since days can be of
/// different lengths in different time zones, `Zoned::since` will return an
/// error when the two zoned datetimes are in different time zones and when
/// the caller requests units greater than hours.
///
/// # Dealing with ambiguity
///
/// The principal job of a `TimeZone` is to provide two different
/// transformations:
///
/// * A conversion from a [`Timestamp`] to a civil time (also known as local,
/// naive or plain time). This conversion is always unambiguous. That is,
/// there is always precisely one representation of civil time for any
/// particular instant in time for a particular time zone.
/// * A conversion from a [`civil::DateTime`](crate::civil::DateTime) to an
/// instant in time. This conversion is sometimes ambiguous in that a civil
/// time might have either never appear on the clocks in a particular
/// time zone (a gap), or in that the civil time may have been repeated on the
/// clocks in a particular time zone (a fold). Typically, a transition to
/// daylight saving time is a gap, while a transition out of daylight saving
/// time is a fold.
///
/// The timestamp-to-civil time conversion is done via
/// [`TimeZone::to_datetime`], or its lower level counterpart,
/// [`TimeZone::to_offset`]. The civil time-to-timestamp conversion is done
/// via one of the following routines:
///
/// * [`TimeZone::to_zoned`] conveniently returns a [`Zoned`] and automatically
/// uses the
/// [`Disambiguation::Compatible`](crate::tz::Disambiguation::Compatible)
/// strategy if the given civil datetime is ambiguous in the time zone.
/// * [`TimeZone::to_ambiguous_zoned`] returns a potentially ambiguous
/// zoned datetime, [`AmbiguousZoned`], and provides fine-grained control over
/// how to resolve ambiguity, if it occurs.
/// * [`TimeZone::to_timestamp`] is like `TimeZone::to_zoned`, but returns
/// a [`Timestamp`] instead.
/// * [`TimeZone::to_ambiguous_timestamp`] is like
/// `TimeZone::to_ambiguous_zoned`, but returns an [`AmbiguousTimestamp`]
/// instead.
///
/// Here is an example where we explore the different disambiguation strategies
/// for a fold in time, where in this case, the 1 o'clock hour is repeated:
///
/// ```
/// use jiff::{civil::date, tz::TimeZone};
///
/// let tz = TimeZone::get("America/New_York")?;
/// let dt = date(2024, 11, 3).at(1, 30, 0, 0);
/// // It's ambiguous, so asking for an unambiguous instant presents an error!
/// assert!(tz.to_ambiguous_zoned(dt).unambiguous().is_err());
/// // Gives you the earlier time in a fold, i.e., before DST ends:
/// assert_eq!(
///     tz.to_ambiguous_zoned(dt).earlier()?.to_string(),
///     "2024-11-03T01:30:00-04:00[America/New_York]",
/// );
/// // Gives you the later time in a fold, i.e., after DST ends.
/// // Notice the offset change from the previous example!
/// assert_eq!(
///     tz.to_ambiguous_zoned(dt).later()?.to_string(),
///     "2024-11-03T01:30:00-05:00[America/New_York]",
/// );
/// // "Just give me something reasonable"
/// assert_eq!(
///     tz.to_ambiguous_zoned(dt).compatible()?.to_string(),
///     "2024-11-03T01:30:00-04:00[America/New_York]",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Serde integration
///
/// At present, a `TimeZone` does not implement Serde's `Serialize` or
/// `Deserialize` traits directly. Nor does it implement `std::fmt::Display`
/// or `std::str::FromStr`. The reason for this is that it's not totally
/// clear if there is one single obvious behavior. Moreover, some `TimeZone`
/// values do not have an obvious succinct serialized representation. (For
/// example, when `/etc/localtime` on a Unix system is your system's time zone,
/// and it isn't a symlink to a TZif file in `/usr/share/zoneinfo`. In which
/// case, an IANA time zone identifier cannot easily be deduced by Jiff.)
///
/// Instead, Jiff offers helpers for use with Serde's [`with` attribute] via
/// the [`fmt::serde`](crate::fmt::serde) module:
///
/// ```
/// use jiff::tz::TimeZone;
///
/// #[derive(Debug, serde::Deserialize, serde::Serialize)]
/// struct Record {
///     #[serde(with = "jiff::fmt::serde::tz::optional")]
///     tz: Option<TimeZone>,
/// }
///
/// let json = r#"{"tz":"America/Nuuk"}"#;
/// let got: Record = serde_json::from_str(&json)?;
/// assert_eq!(got.tz, Some(TimeZone::get("America/Nuuk")?));
/// assert_eq!(serde_json::to_string(&got)?, json);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Alternatively, you may use the
/// [`fmt::temporal::DateTimeParser::parse_time_zone`](crate::fmt::temporal::DateTimeParser::parse_time_zone)
/// or
/// [`fmt::temporal::DateTimePrinter::print_time_zone`](crate::fmt::temporal::DateTimePrinter::print_time_zone)
/// routines to parse or print `TimeZone` values without using Serde.
///
/// [time zone]: https://en.wikipedia.org/wiki/Time_zone
/// [daylight saving time]: https://en.wikipedia.org/wiki/Daylight_saving_time
/// [IANA Time Zone Database]: https://en.wikipedia.org/wiki/Tz_database
/// [POSIX TZ]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html
/// [`env_logger`]: https://docs.rs/env_logger
/// [RFC 8536]: https://datatracker.ietf.org/doc/html/rfc8536
/// [`with` attribute]: https://serde.rs/field-attrs.html#with
#[derive(Clone, Eq, PartialEq)]
pub struct TimeZone {
    kind: Option<Arc<TimeZoneKind>>,
}

impl TimeZone {
    /// The UTC time zone.
    ///
    /// The offset of this time is `0` and never has any transitions.
    pub const UTC: TimeZone = TimeZone { kind: None };

    /// Returns the system configured time zone, if available.
    ///
    /// Detection of a system's default time zone is generally heuristic
    /// based and platform specific.
    ///
    /// If callers need to know whether discovery of the system time zone
    /// failed, then use [`TimeZone::try_system`].
    ///
    /// # Fallback behavior
    ///
    /// If the system's default time zone could not be determined, or if
    /// the `tz-system` crate feature is not enabled, then this returns
    /// [`TimeZone::unknown`]. A `WARN` level log will also be emitted with
    /// a message explaining why time zone detection failed. The fallback to
    /// an unknown time zone is a practical trade-off, is what most other
    /// systems tend to do and is also recommended by [relevant standards such
    /// as freedesktop.org][freedesktop-org-localtime].
    ///
    /// An unknown time zone _behaves_ like [`TimeZone::UTC`], but will
    /// print as `Etc/Unknown` when converting a `Zoned` to a string.
    ///
    /// If you would instead like to fall back to UTC instead
    /// of the special "unknown" time zone, then you can do
    /// `TimeZone::try_system().unwrap_or(TimeZone::UTC)`.
    ///
    /// # Platform behavior
    ///
    /// This section is a "best effort" explanation of how the time zone is
    /// detected on supported platforms. The behavior is subject to change.
    ///
    /// On all platforms, the `TZ` environment variable overrides any other
    /// heuristic, and provides a way for end users to set the time zone for
    /// specific use cases. In general, Jiff respects the [POSIX TZ] rules.
    /// Here are some examples:
    ///
    /// * `TZ=America/New_York` for setting a time zone via an IANA Time Zone
    /// Database Identifier.
    /// * `TZ=/usr/share/zoneinfo/America/New_York` for setting a time zone
    /// by providing a file path to a TZif file directly.
    /// * `TZ=EST5EDT,M3.2.0,M11.1.0` for setting a time zone via a daylight
    /// saving time transition rule.
    ///
    /// Otherwise, when `TZ` isn't set, then:
    ///
    /// On Unix non-Android systems, this inspects `/etc/localtime`. If it's
    /// a symbolic link to an entry in `/usr/share/zoneinfo`, then the suffix
    /// is considered an IANA Time Zone Database identifier. Otherwise,
    /// `/etc/localtime` is read as a TZif file directly.
    ///
    /// On Android systems, this inspects the `persist.sys.timezone` property.
    ///
    /// On Windows, the system time zone is determined via
    /// [`GetDynamicTimeZoneInformation`]. The result is then mapped to an
    /// IANA Time Zone Database identifier via Unicode's
    /// [CLDR XML data].
    ///
    /// [freedesktop-org-localtime]: https://www.freedesktop.org/software/systemd/man/latest/localtime.html
    /// [POSIX TZ]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html
    /// [`GetDynamicTimeZoneInformation`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-getdynamictimezoneinformation
    /// [CLDR XML data]: https://github.com/unicode-org/cldr/raw/main/common/supplemental/windowsZones.xml
    #[inline]
    pub fn system() -> TimeZone {
        match TimeZone::try_system() {
            Ok(tz) => tz,
            Err(_err) => {
                warn!(
                    "failed to get system time zone, \
                     falling back to `Etc/Unknown` \
                     (which behaves like UTC): {_err}",
                );
                TimeZone::unknown()
            }
        }
    }

    /// Returns the system configured time zone, if available.
    ///
    /// If the system's default time zone could not be determined, or if the
    /// `tz-system` crate feature is not enabled, then this returns an error.
    ///
    /// Detection of a system's default time zone is generally heuristic
    /// based and platform specific.
    ///
    /// Note that callers should generally prefer using [`TimeZone::system`].
    /// If a system time zone could not be found, then it falls
    /// back to [`TimeZone::UTC`] automatically. This is often
    /// what is recommended by [relevant standards such as
    /// freedesktop.org][freedesktop-org-localtime]. Conversely, this routine
    /// is useful if detection of a system's default time zone is critical.
    ///
    /// # Platform behavior
    ///
    /// This section is a "best effort" explanation of how the time zone is
    /// detected on supported platforms. The behavior is subject to change.
    ///
    /// On all platforms, the `TZ` environment variable overrides any other
    /// heuristic, and provides a way for end users to set the time zone for
    /// specific use cases. In general, Jiff respects the [POSIX TZ] rules.
    /// Here are some examples:
    ///
    /// * `TZ=America/New_York` for setting a time zone via an IANA Time Zone
    /// Database Identifier.
    /// * `TZ=/usr/share/zoneinfo/America/New_York` for setting a time zone
    /// by providing a file path to a TZif file directly.
    /// * `TZ=EST5EDT,M3.2.0,M11.1.0` for setting a time zone via a daylight
    /// saving time transition rule.
    ///
    /// Otherwise, when `TZ` isn't set, then:
    ///
    /// On Unix systems, this inspects `/etc/localtime`. If it's a symbolic
    /// link to an entry in `/usr/share/zoneinfo`, then the suffix is
    /// considered an IANA Time Zone Database identifier. Otherwise,
    /// `/etc/localtime` is read as a TZif file directly.
    ///
    /// On Windows, the system time zone is determined via
    /// [`GetDynamicTimeZoneInformation`]. The result is then mapped to an
    /// IANA Time Zone Database identifier via Unicode's
    /// [CLDR XML data].
    ///
    /// [freedesktop-org-localtime]: https://www.freedesktop.org/software/systemd/man/latest/localtime.html
    /// [POSIX TZ]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html
    /// [`GetDynamicTimeZoneInformation`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-getdynamictimezoneinformation
    /// [CLDR XML data]: https://github.com/unicode-org/cldr/raw/main/common/supplemental/windowsZones.xml
    #[inline]
    pub fn try_system() -> Result<TimeZone, Error> {
        #[cfg(not(feature = "tz-system"))]
        {
            Err(err!(
                "failed to get system time zone since 'tz-system' \
                 crate feature is not enabled",
            ))
        }
        #[cfg(feature = "tz-system")]
        {
            crate::tz::system::get(crate::tz::db())
        }
    }

    /// A convenience function for performing a time zone database lookup for
    /// the given time zone identifier. It uses the default global time zone
    /// database via [`tz::db()`](crate::tz::db()).
    ///
    /// # Errors
    ///
    /// This returns an error if the given time zone identifier could not be
    /// found in the default [`TimeZoneDatabase`](crate::tz::TimeZoneDatabase).
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{tz::TimeZone, Timestamp};
    ///
    /// let tz = TimeZone::get("Japan")?;
    /// assert_eq!(
    ///     tz.to_datetime(Timestamp::UNIX_EPOCH).to_string(),
    ///     "1970-01-01T09:00:00",
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn get(time_zone_name: &str) -> Result<TimeZone, Error> {
        crate::tz::db().get(time_zone_name)
    }

    /// Returns a time zone with a fixed offset.
    ///
    /// A fixed offset will never have any transitions and won't follow any
    /// particular time zone rules. In general, one should avoid using fixed
    /// offset time zones unless you have a specific need for them. Otherwise,
    /// IANA time zones via [`TimeZone::get`] should be preferred, as they
    /// more accurately model the actual time zone transitions rules used in
    /// practice.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{tz::{self, TimeZone}, Timestamp};
    ///
    /// let tz = TimeZone::fixed(tz::offset(10));
    /// assert_eq!(
    ///     tz.to_datetime(Timestamp::UNIX_EPOCH).to_string(),
    ///     "1970-01-01T10:00:00",
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn fixed(offset: Offset) -> TimeZone {
        if offset == Offset::UTC {
            return TimeZone::UTC;
        }
        let fixed = TimeZoneFixed::new(offset);
        let kind = TimeZoneKind::Fixed(fixed);
        TimeZone { kind: Some(Arc::new(kind)) }
    }

    /// Creates a time zone from a [POSIX TZ] rule string.
    ///
    /// A POSIX time zone provides a way to tersely define a single daylight
    /// saving time transition rule (or none at all) that applies for all
    /// years.
    ///
    /// Users should avoid using this kind of time zone unless there is a
    /// specific need for it. Namely, POSIX time zones cannot capture the full
    /// complexity of time zone transition rules in the real world. (See the
    /// example below.)
    ///
    /// [POSIX TZ]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html
    ///
    /// # Errors
    ///
    /// This returns an error if the given POSIX time zone string is invalid.
    ///
    /// # Example
    ///
    /// This example demonstrates how a POSIX time zone may be historically
    /// inaccurate:
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone};
    ///
    /// // The tzdb entry for America/New_York.
    /// let iana = TimeZone::get("America/New_York")?;
    /// // The POSIX TZ string for New York DST that went into effect in 2007.
    /// let posix = TimeZone::posix("EST5EDT,M3.2.0,M11.1.0")?;
    ///
    /// // New York entered DST on April 2, 2006 at 2am:
    /// let dt = date(2006, 4, 2).at(2, 0, 0, 0);
    /// // The IANA tzdb entry correctly reports it as ambiguous:
    /// assert!(iana.to_ambiguous_timestamp(dt).is_ambiguous());
    /// // But the POSIX time zone does not:
    /// assert!(!posix.to_ambiguous_timestamp(dt).is_ambiguous());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[cfg(feature = "alloc")]
    pub fn posix(posix_tz_string: &str) -> Result<TimeZone, Error> {
        let posix_tz = ReasonablePosixTimeZone::parse(posix_tz_string)?;
        Ok(TimeZone::from_reasonable_posix_tz(posix_tz))
    }

    /// Creates a time zone from a POSIX tz. Expose so that other parts of Jiff
    /// can create a `TimeZone` from a POSIX tz. (Kinda sloppy to be honest.)
    #[cfg(feature = "alloc")]
    pub(crate) fn from_reasonable_posix_tz(
        posix: ReasonablePosixTimeZone,
    ) -> TimeZone {
        let posix = TimeZonePosix { posix };
        let kind = TimeZoneKind::Posix(posix);
        TimeZone { kind: Some(Arc::new(kind)) }
    }

    /// Creates a time zone from TZif binary data, whose format is specified
    /// in [RFC 8536]. All versions of TZif (up through version 4) are
    /// supported.
    ///
    /// This constructor is typically not used, and instead, one should rely
    /// on time zone lookups via time zone identifiers with routines like
    /// [`TimeZone::get`]. However, this constructor does provide one way
    /// of using custom time zones with Jiff.
    ///
    /// The name given should be a IANA time zone database identifier.
    ///
    /// [RFC 8536]: https://datatracker.ietf.org/doc/html/rfc8536
    ///
    /// # Errors
    ///
    /// This returns an error if the given data was not recognized as valid
    /// TZif.
    #[cfg(feature = "alloc")]
    pub fn tzif(name: &str, data: &[u8]) -> Result<TimeZone, Error> {
        use alloc::string::ToString;

        let tzif = TimeZoneTzif::new(Some(name.to_string()), data)?;
        let kind = TimeZoneKind::Tzif(tzif);
        Ok(TimeZone { kind: Some(Arc::new(kind)) })
    }

    /// Returns a `TimeZone` that is specifially marked as "unknown."
    ///
    /// This corresponds to the Unicode CLDR identifier `Etc/Unknown`, which
    /// is guaranteed to never be a valid IANA time zone identifier (as of
    /// the `2025a` release of tzdb).
    ///
    /// This type of `TimeZone` is used in circumstances where one wants to
    /// signal that discovering a time zone failed for some reason, but that
    /// execution can reasonably continue. For example, [`TimeZone::system`]
    /// returns this type of time zone when the system time zone could not be
    /// discovered.
    ///
    /// # Example
    ///
    /// Jiff permits an "unknown" time zone to losslessly be transmitted
    /// through serialization:
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone, Zoned};
    ///
    /// let tz = TimeZone::unknown();
    /// let zdt = date(2025, 2, 1).at(17, 0, 0, 0).to_zoned(tz)?;
    /// assert_eq!(zdt.to_string(), "2025-02-01T17:00:00Z[Etc/Unknown]");
    /// let got: Zoned = "2025-02-01T17:00:00Z[Etc/Unknown]".parse()?;
    /// assert_eq!(got, zdt);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Note that not all systems support this. Some systems will reject
    /// `Etc/Unknown` because it is not a valid IANA time zone identifier and
    /// does not have an entry in the IANA time zone database. However, Jiff
    /// takes this approach because it surfaces an error condition in detecting
    /// the end user's time zone. Callers not wanting an "unknown" time zone
    /// can use `TimeZone::try_system().unwrap_or(TimeZone::UTC)` instead of
    /// `TimeZone::system`. (Where the latter falls back to the "unknown" time
    /// zone when a system configured time zone could not be found.)
    pub fn unknown() -> TimeZone {
        let kind = TimeZoneKind::Unknown;
        TimeZone { kind: Some(Arc::new(kind)) }
    }

    /// This creates an unnamed TZif-backed `TimeZone`.
    ///
    /// At present, the only way for an unnamed TZif-backed `TimeZone` to be
    /// created is when the system time zone has no identifiable name. For
    /// example, when `/etc/localtime` is hard-linked to a TZif file instead
    /// of being symlinked. In this case, there is no cheap and unambiguous
    /// way to determine the time zone name. So we just let it be unnamed.
    /// Since this is the only such case, and hopefully will only ever be the
    /// only such case, we consider such unnamed TZif-back `TimeZone` values
    /// as being the "system" time zone.
    ///
    /// When this is used to construct a `TimeZone`, the `TimeZone::name`
    /// method will be "Local". This is... pretty unfortunate. I'm not sure
    /// what else to do other than to make `TimeZone::name` return an
    /// `Option<&str>`. But... we use it in a bunch of places and it just
    /// seems bad for a time zone to not have a name.
    ///
    /// OK, because of the above, I renamed `TimeZone::name` to
    /// `TimeZone::diagnostic_name`. This should make it clearer that you can't
    /// really use the name to do anything interesting. This also makes more
    /// sense for POSIX TZ strings too.
    ///
    /// In any case, this routine stays unexported because I don't want TZif
    /// backed `TimeZone` values to proliferate. If you have a legitimate use
    /// case otherwise, please file an issue. It will require API design.
    ///
    /// # Errors
    ///
    /// This returns an error if the given TZif data is invalid.
    #[cfg(feature = "tz-system")]
    pub(crate) fn tzif_system(data: &[u8]) -> Result<TimeZone, Error> {
        let tzif = TimeZoneTzif::new(None, data)?;
        let kind = TimeZoneKind::Tzif(tzif);
        Ok(TimeZone { kind: Some(Arc::new(kind)) })
    }

    #[inline]
    pub(crate) fn diagnostic_name(&self) -> DiagnosticName<'_> {
        DiagnosticName(self)
    }

    /// Returns true if and only if this `TimeZone` can be succinctly
    /// serialized.
    ///
    /// Basically, this is only `false` when this `TimeZone` was created from
    /// a `/etc/localtime` for which a valid IANA time zone identifier could
    /// not be extracted. It is also `false` when [`TimeZone::is_unknown`]
    /// is `true`.
    #[cfg(feature = "serde")]
    #[inline]
    pub(crate) fn has_succinct_serialization(&self) -> bool {
        let Some(ref kind) = self.kind else { return true };
        match **kind {
            TimeZoneKind::Unknown => true,
            TimeZoneKind::Fixed(_) => true,
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(_) => true,
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(ref tz) => tz.name().is_some(),
        }
    }

    /// When this time zone was loaded from an IANA time zone database entry,
    /// then this returns the canonicalized name for that time zone.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::TimeZone;
    ///
    /// let tz = TimeZone::get("america/NEW_YORK")?;
    /// assert_eq!(tz.iana_name(), Some("America/New_York"));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn iana_name(&self) -> Option<&str> {
        let Some(ref kind) = self.kind else { return Some("UTC") };
        match **kind {
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(ref tz) => tz.name(),
            // Note that while `Etc/Unknown` looks like an IANA time zone
            // identifier, it is specifically and explicitly NOT an IANA time
            // zone identifier. So we do not return it here if we have an
            // unknown time zone identifier.
            _ => None,
        }
    }

    /// Returns true if and only if this time zone is unknown.
    ///
    /// This has the special internal identifier of `Etc/Unknown`, and this
    /// is what will be used when converting a `Zoned` to a string.
    ///
    /// Note that while `Etc/Unknown` looks like an IANA time zone identifier,
    /// it is specifically and explicitly not one. It is reserved and is
    /// guaranteed to never be an IANA time zone identifier.
    ///
    /// An unknown time zone can be created via [`TimeZone::unknown`]. It is
    /// also returned by [`TimeZone::system`] when a system configured time
    /// zone could not be found.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::TimeZone;
    ///
    /// let tz = TimeZone::unknown();
    /// assert_eq!(tz.iana_name(), None);
    /// assert!(tz.is_unknown());
    /// ```
    #[inline]
    pub fn is_unknown(&self) -> bool {
        let Some(ref kind) = self.kind else { return false };
        matches!(**kind, TimeZoneKind::Unknown)
    }

    /// When this time zone is a POSIX time zone, return it.
    ///
    /// This doesn't attempt to convert other time zones that are representable
    /// as POSIX time zones to POSIX time zones (e.g., fixed offset time
    /// zones). Instead, this only returns something when the actual
    /// representation of the time zone is a POSIX time zone.
    #[cfg(feature = "alloc")]
    #[inline]
    pub(crate) fn posix_tz(&self) -> Option<&ReasonablePosixTimeZone> {
        let Some(ref kind) = self.kind else { return None };
        match **kind {
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(ref tz) => Some(&tz.posix),
            _ => None,
        }
    }

    /// Returns the civil datetime corresponding to the given timestamp in this
    /// time zone.
    ///
    /// This operation is always unambiguous. That is, for any instant in time
    /// supported by Jiff (that is, a `Timestamp`), there is always precisely
    /// one civil datetime corresponding to that instant.
    ///
    /// Note that this is considered a lower level routine. Consider working
    /// with zoned datetimes instead, and use [`Zoned::datetime`] to get its
    /// civil time if necessary.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{tz::TimeZone, Timestamp};
    ///
    /// let tz = TimeZone::get("Europe/Rome")?;
    /// assert_eq!(
    ///     tz.to_datetime(Timestamp::UNIX_EPOCH).to_string(),
    ///     "1970-01-01T01:00:00",
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// As mentioned above, consider using `Zoned` instead:
    ///
    /// ```
    /// use jiff::{tz::TimeZone, Timestamp};
    ///
    /// let zdt = Timestamp::UNIX_EPOCH.in_tz("Europe/Rome")?;
    /// assert_eq!(zdt.datetime().to_string(), "1970-01-01T01:00:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_datetime(&self, timestamp: Timestamp) -> DateTime {
        self.to_offset(timestamp).to_datetime(timestamp)
    }

    /// Returns the offset corresponding to the given timestamp in this time
    /// zone.
    ///
    /// This operation is always unambiguous. That is, for any instant in time
    /// supported by Jiff (that is, a `Timestamp`), there is always precisely
    /// one offset corresponding to that instant.
    ///
    /// Given an offset, one can use APIs like [`Offset::to_datetime`] to
    /// create a civil datetime from a timestamp.
    ///
    /// This also returns whether this timestamp is considered to be in
    /// "daylight saving time," as well as the abbreviation for the time zone
    /// at this time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{tz::{self, Dst, TimeZone}, Timestamp};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    ///
    /// // A timestamp in DST in New York.
    /// let ts = Timestamp::from_second(1_720_493_204)?;
    /// let offset = tz.to_offset(ts);
    /// assert_eq!(offset, tz::offset(-4));
    /// assert_eq!(offset.to_datetime(ts).to_string(), "2024-07-08T22:46:44");
    ///
    /// // A timestamp *not* in DST in New York.
    /// let ts = Timestamp::from_second(1_704_941_204)?;
    /// let offset = tz.to_offset(ts);
    /// assert_eq!(offset, tz::offset(-5));
    /// assert_eq!(offset.to_datetime(ts).to_string(), "2024-01-10T21:46:44");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_offset(&self, _timestamp: Timestamp) -> Offset {
        let Some(ref kind) = self.kind else {
            return Offset::UTC;
        };
        match **kind {
            TimeZoneKind::Unknown => Offset::UTC,
            TimeZoneKind::Fixed(ref tz) => tz.to_offset(),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(ref tz) => tz.to_offset(_timestamp),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(ref tz) => tz.to_offset(_timestamp),
        }
    }

    /// Returns the offset information corresponding to the given timestamp in
    /// this time zone. This includes the offset along with daylight saving
    /// time status and a time zone abbreviation.
    ///
    /// This is like [`TimeZone::to_offset`], but returns the aforementioned
    /// extra data in addition to the offset. This data may, in some cases, be
    /// more expensive to compute.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{tz::{self, Dst, TimeZone}, Timestamp};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    ///
    /// // A timestamp in DST in New York.
    /// let ts = Timestamp::from_second(1_720_493_204)?;
    /// let info = tz.to_offset_info(ts);
    /// assert_eq!(info.offset(), tz::offset(-4));
    /// assert_eq!(info.dst(), Dst::Yes);
    /// assert_eq!(info.abbreviation(), "EDT");
    /// assert_eq!(
    ///     info.offset().to_datetime(ts).to_string(),
    ///     "2024-07-08T22:46:44",
    /// );
    ///
    /// // A timestamp *not* in DST in New York.
    /// let ts = Timestamp::from_second(1_704_941_204)?;
    /// let info = tz.to_offset_info(ts);
    /// assert_eq!(info.offset(), tz::offset(-5));
    /// assert_eq!(info.dst(), Dst::No);
    /// assert_eq!(info.abbreviation(), "EST");
    /// assert_eq!(
    ///     info.offset().to_datetime(ts).to_string(),
    ///     "2024-01-10T21:46:44",
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_offset_info<'t>(
        &'t self,
        _timestamp: Timestamp,
    ) -> TimeZoneOffsetInfo<'t> {
        let Some(ref kind) = self.kind else {
            return TimeZoneOffsetInfo {
                offset: Offset::UTC,
                dst: Dst::No,
                abbreviation: TimeZoneAbbreviation::Borrowed("UTC"),
            };
        };
        match **kind {
            TimeZoneKind::Unknown => {
                TimeZoneOffsetInfo {
                    offset: Offset::UTC,
                    dst: Dst::No,
                    // It'd be kinda nice if this were just `ERR` to
                    // indicate an error, but I can't find any precedent
                    // for that. And CLDR says `Etc/Unknown` should behave
                    // like UTC, so... I guess we use UTC here.
                    abbreviation: TimeZoneAbbreviation::Borrowed("UTC"),
                }
            }
            TimeZoneKind::Fixed(ref tz) => tz.to_offset_info(),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(ref tz) => tz.to_offset_info(_timestamp),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(ref tz) => tz.to_offset_info(_timestamp),
        }
    }

    /// If this time zone is a fixed offset, then this returns the offset.
    /// If this time zone is not a fixed offset, then an error is returned.
    ///
    /// If you just need an offset for a given timestamp, then you can use
    /// [`TimeZone::to_offset`]. Or, if you need an offset for a civil
    /// datetime, then you can use [`TimeZone::to_ambiguous_timestamp`] or
    /// [`TimeZone::to_ambiguous_zoned`], although the result may be ambiguous.
    ///
    /// Generally, this routine is useful when you need to know whether the
    /// time zone is fixed, and you want to get the offset without having to
    /// specify a timestamp. This is sometimes required for interoperating with
    /// other datetime systems that need to distinguish between time zones that
    /// are fixed and time zones that are based on rules such as those found in
    /// the IANA time zone database.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::{Offset, TimeZone};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    /// // A named time zone is not a fixed offset
    /// // and so cannot be converted to an offset
    /// // without a timestamp or civil datetime.
    /// assert_eq!(
    ///     tz.to_fixed_offset().unwrap_err().to_string(),
    ///     "cannot convert non-fixed IANA time zone \
    ///      to offset without timestamp or civil datetime",
    /// );
    ///
    /// let tz = TimeZone::UTC;
    /// // UTC is a fixed offset and so can be converted
    /// // without a timestamp.
    /// assert_eq!(tz.to_fixed_offset()?, Offset::UTC);
    ///
    /// // And of course, creating a time zone from a
    /// // fixed offset results in a fixed offset time
    /// // zone too:
    /// let tz = TimeZone::fixed(jiff::tz::offset(-10));
    /// assert_eq!(tz.to_fixed_offset()?, jiff::tz::offset(-10));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_fixed_offset(&self) -> Result<Offset, Error> {
        let Some(ref kind) = self.kind else { return Ok(Offset::UTC) };
        #[allow(irrefutable_let_patterns)]
        match **kind {
            TimeZoneKind::Unknown => Ok(Offset::UTC),
            TimeZoneKind::Fixed(ref tz) => Ok(tz.to_offset()),
            #[cfg(feature = "alloc")]
            _ => Err(err!(
                "cannot convert non-fixed {kind} time zone to offset \
                 without timestamp or civil datetime",
                kind = self.kind_description(),
            )),
        }
    }

    /// Converts a civil datetime to a [`Zoned`] in this time zone.
    ///
    /// The given civil datetime may be ambiguous in this time zone. A civil
    /// datetime is ambiguous when either of the following occurs:
    ///
    /// * When the civil datetime falls into a "gap." That is, when there is a
    /// jump forward in time where a span of time does not appear on the clocks
    /// in this time zone. This _typically_ manifests as a 1 hour jump forward
    /// into daylight saving time.
    /// * When the civil datetime falls into a "fold." That is, when there is
    /// a jump backward in time where a span of time is _repeated_ on the
    /// clocks in this time zone. This _typically_ manifests as a 1 hour jump
    /// backward out of daylight saving time.
    ///
    /// This routine automatically resolves both of the above ambiguities via
    /// the
    /// [`Disambiguation::Compatible`](crate::tz::Disambiguation::Compatible)
    /// strategy. That in, the case of a gap, the time after the gap is used.
    /// In the case of a fold, the first repetition of the clock time is used.
    ///
    /// # Example
    ///
    /// This example shows how disambiguation works:
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    ///
    /// // This demonstrates disambiguation behavior for a gap.
    /// let zdt = tz.to_zoned(date(2024, 3, 10).at(2, 30, 0, 0))?;
    /// assert_eq!(zdt.to_string(), "2024-03-10T03:30:00-04:00[America/New_York]");
    /// // This demonstrates disambiguation behavior for a fold.
    /// // Notice the offset: the -04 corresponds to the time while
    /// // still in DST. The second repetition of the 1 o'clock hour
    /// // occurs outside of DST, in "standard" time, with the offset -5.
    /// let zdt = tz.to_zoned(date(2024, 11, 3).at(1, 30, 0, 0))?;
    /// assert_eq!(zdt.to_string(), "2024-11-03T01:30:00-04:00[America/New_York]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_zoned(&self, dt: DateTime) -> Result<Zoned, Error> {
        self.to_ambiguous_zoned(dt).compatible()
    }

    /// Converts a civil datetime to a possibly ambiguous zoned datetime in
    /// this time zone.
    ///
    /// The given civil datetime may be ambiguous in this time zone. A civil
    /// datetime is ambiguous when either of the following occurs:
    ///
    /// * When the civil datetime falls into a "gap." That is, when there is a
    /// jump forward in time where a span of time does not appear on the clocks
    /// in this time zone. This _typically_ manifests as a 1 hour jump forward
    /// into daylight saving time.
    /// * When the civil datetime falls into a "fold." That is, when there is
    /// a jump backward in time where a span of time is _repeated_ on the
    /// clocks in this time zone. This _typically_ manifests as a 1 hour jump
    /// backward out of daylight saving time.
    ///
    /// Unlike [`TimeZone::to_zoned`], this method does not do any automatic
    /// disambiguation. Instead, callers are expected to use the methods on
    /// [`AmbiguousZoned`] to resolve any ambiguity, if it occurs.
    ///
    /// # Example
    ///
    /// This example shows how to return an error when the civil datetime given
    /// is ambiguous:
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    ///
    /// // This is not ambiguous:
    /// let dt = date(2024, 3, 10).at(1, 0, 0, 0);
    /// assert_eq!(
    ///     tz.to_ambiguous_zoned(dt).unambiguous()?.to_string(),
    ///     "2024-03-10T01:00:00-05:00[America/New_York]",
    /// );
    /// // But this is a gap, and thus ambiguous! So an error is returned.
    /// let dt = date(2024, 3, 10).at(2, 0, 0, 0);
    /// assert!(tz.to_ambiguous_zoned(dt).unambiguous().is_err());
    /// // And so is this, because it's a fold.
    /// let dt = date(2024, 11, 3).at(1, 0, 0, 0);
    /// assert!(tz.to_ambiguous_zoned(dt).unambiguous().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_ambiguous_zoned(&self, dt: DateTime) -> AmbiguousZoned {
        self.clone().into_ambiguous_zoned(dt)
    }

    /// Converts a civil datetime to a possibly ambiguous zoned datetime in
    /// this time zone, and does so by assuming ownership of this `TimeZone`.
    ///
    /// This is identical to [`TimeZone::to_ambiguous_zoned`], but it avoids
    /// a `TimeZone::clone()` call. (Which are cheap, but not completely free.)
    ///
    /// # Example
    ///
    /// This example shows how to create a `Zoned` value from a `TimeZone`
    /// and a `DateTime` without cloning the `TimeZone`:
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    /// let dt = date(2024, 3, 10).at(1, 0, 0, 0);
    /// assert_eq!(
    ///     tz.into_ambiguous_zoned(dt).unambiguous()?.to_string(),
    ///     "2024-03-10T01:00:00-05:00[America/New_York]",
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn into_ambiguous_zoned(self, dt: DateTime) -> AmbiguousZoned {
        self.to_ambiguous_timestamp(dt).into_ambiguous_zoned(self)
    }

    /// Converts a civil datetime to a [`Timestamp`] in this time zone.
    ///
    /// The given civil datetime may be ambiguous in this time zone. A civil
    /// datetime is ambiguous when either of the following occurs:
    ///
    /// * When the civil datetime falls into a "gap." That is, when there is a
    /// jump forward in time where a span of time does not appear on the clocks
    /// in this time zone. This _typically_ manifests as a 1 hour jump forward
    /// into daylight saving time.
    /// * When the civil datetime falls into a "fold." That is, when there is
    /// a jump backward in time where a span of time is _repeated_ on the
    /// clocks in this time zone. This _typically_ manifests as a 1 hour jump
    /// backward out of daylight saving time.
    ///
    /// This routine automatically resolves both of the above ambiguities via
    /// the
    /// [`Disambiguation::Compatible`](crate::tz::Disambiguation::Compatible)
    /// strategy. That in, the case of a gap, the time after the gap is used.
    /// In the case of a fold, the first repetition of the clock time is used.
    ///
    /// This routine is identical to [`TimeZone::to_zoned`], except it returns
    /// a `Timestamp` instead of a zoned datetime. The benefit of this
    /// method is that it never requires cloning or consuming ownership of a
    /// `TimeZone`, and it doesn't require construction of `Zoned` which has
    /// a small but non-zero cost. (This is partially because a `Zoned` value
    /// contains a `TimeZone`, but of course, a `Timestamp` does not.)
    ///
    /// # Example
    ///
    /// This example shows how disambiguation works:
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    ///
    /// // This demonstrates disambiguation behavior for a gap.
    /// let ts = tz.to_timestamp(date(2024, 3, 10).at(2, 30, 0, 0))?;
    /// assert_eq!(ts.to_string(), "2024-03-10T07:30:00Z");
    /// // This demonstrates disambiguation behavior for a fold.
    /// // Notice the offset: the -04 corresponds to the time while
    /// // still in DST. The second repetition of the 1 o'clock hour
    /// // occurs outside of DST, in "standard" time, with the offset -5.
    /// let ts = tz.to_timestamp(date(2024, 11, 3).at(1, 30, 0, 0))?;
    /// assert_eq!(ts.to_string(), "2024-11-03T05:30:00Z");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_timestamp(&self, dt: DateTime) -> Result<Timestamp, Error> {
        self.to_ambiguous_timestamp(dt).compatible()
    }

    /// Converts a civil datetime to a possibly ambiguous timestamp in
    /// this time zone.
    ///
    /// The given civil datetime may be ambiguous in this time zone. A civil
    /// datetime is ambiguous when either of the following occurs:
    ///
    /// * When the civil datetime falls into a "gap." That is, when there is a
    /// jump forward in time where a span of time does not appear on the clocks
    /// in this time zone. This _typically_ manifests as a 1 hour jump forward
    /// into daylight saving time.
    /// * When the civil datetime falls into a "fold." That is, when there is
    /// a jump backward in time where a span of time is _repeated_ on the
    /// clocks in this time zone. This _typically_ manifests as a 1 hour jump
    /// backward out of daylight saving time.
    ///
    /// Unlike [`TimeZone::to_timestamp`], this method does not do any
    /// automatic disambiguation. Instead, callers are expected to use the
    /// methods on [`AmbiguousTimestamp`] to resolve any ambiguity, if it
    /// occurs.
    ///
    /// This routine is identical to [`TimeZone::to_ambiguous_zoned`], except
    /// it returns an `AmbiguousTimestamp` instead of a `AmbiguousZoned`. The
    /// benefit of this method is that it never requires cloning or consuming
    /// ownership of a `TimeZone`, and it doesn't require construction of
    /// `Zoned` which has a small but non-zero cost. (This is partially because
    /// a `Zoned` value contains a `TimeZone`, but of course, a `Timestamp`
    /// does not.)
    ///
    /// # Example
    ///
    /// This example shows how to return an error when the civil datetime given
    /// is ambiguous:
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("America/New_York")?;
    ///
    /// // This is not ambiguous:
    /// let dt = date(2024, 3, 10).at(1, 0, 0, 0);
    /// assert_eq!(
    ///     tz.to_ambiguous_timestamp(dt).unambiguous()?.to_string(),
    ///     "2024-03-10T06:00:00Z",
    /// );
    /// // But this is a gap, and thus ambiguous! So an error is returned.
    /// let dt = date(2024, 3, 10).at(2, 0, 0, 0);
    /// assert!(tz.to_ambiguous_timestamp(dt).unambiguous().is_err());
    /// // And so is this, because it's a fold.
    /// let dt = date(2024, 11, 3).at(1, 0, 0, 0);
    /// assert!(tz.to_ambiguous_timestamp(dt).unambiguous().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_ambiguous_timestamp(&self, dt: DateTime) -> AmbiguousTimestamp {
        let ambiguous_kind = match self.kind {
            None => AmbiguousOffset::Unambiguous { offset: Offset::UTC },
            Some(ref kind) => match **kind {
                TimeZoneKind::Unknown => {
                    AmbiguousOffset::Unambiguous { offset: Offset::UTC }
                }
                TimeZoneKind::Fixed(ref tz) => {
                    AmbiguousOffset::Unambiguous { offset: tz.to_offset() }
                }
                #[cfg(feature = "alloc")]
                TimeZoneKind::Posix(ref tz) => tz.to_ambiguous_kind(dt),
                #[cfg(feature = "alloc")]
                TimeZoneKind::Tzif(ref tz) => tz.to_ambiguous_kind(dt),
            },
        };
        AmbiguousTimestamp::new(dt, ambiguous_kind)
    }

    /// Returns an iterator of time zone transitions preceding the given
    /// timestamp. The iterator returned yields [`TimeZoneTransition`]
    /// elements.
    ///
    /// The order of the iterator returned moves backward through time. If
    /// there is a previous transition, then the timestamp of that transition
    /// is guaranteed to be strictly less than the timestamp given.
    ///
    /// This is a low level API that you generally shouldn't need. It's
    /// useful in cases where you need to know something about the specific
    /// instants at which time zone transitions occur. For example, an embedded
    /// device might need to be explicitly programmed with daylight saving
    /// time transitions. APIs like this enable callers to explore those
    /// transitions.
    ///
    /// A time zone transition refers to a specific point in time when the
    /// offset from UTC for a particular geographical region changes. This
    /// is usually a result of daylight saving time, but it can also occur
    /// when a geographic region changes its permanent offset from UTC.
    ///
    /// The iterator returned is not guaranteed to yield any elements. For
    /// example, this occurs with a fixed offset time zone. Logically, it
    /// would also be possible for the iterator to be infinite, except that
    /// eventually the timestamp would overflow Jiff's minimum timestamp
    /// value, at which point, iteration stops.
    ///
    /// # Example: time since the previous transition
    ///
    /// This example shows how much time has passed since the previous time
    /// zone transition:
    ///
    /// ```
    /// use jiff::{Unit, Zoned};
    ///
    /// let now: Zoned = "2024-12-31 18:25-05[US/Eastern]".parse()?;
    /// let trans = now.time_zone().preceding(now.timestamp()).next().unwrap();
    /// let prev_at = trans.timestamp().to_zoned(now.time_zone().clone());
    /// let span = now.since((Unit::Year, &prev_at))?;
    /// assert_eq!(format!("{span:#}"), "1mo 27d 17h 25m");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: show the 5 previous time zone transitions
    ///
    /// This shows how to find the 5 preceding time zone transitions (from a
    /// particular datetime) for a particular time zone:
    ///
    /// ```
    /// use jiff::{tz::offset, Zoned};
    ///
    /// let now: Zoned = "2024-12-31 18:25-05[US/Eastern]".parse()?;
    /// let transitions = now
    ///     .time_zone()
    ///     .preceding(now.timestamp())
    ///     .take(5)
    ///     .map(|t| (
    ///         t.timestamp().to_zoned(now.time_zone().clone()),
    ///         t.offset(),
    ///         t.abbreviation().to_string(),
    ///     ))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(transitions, vec![
    ///     ("2024-11-03 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
    ///     ("2024-03-10 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
    ///     ("2023-11-05 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
    ///     ("2023-03-12 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
    ///     ("2022-11-06 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
    /// ]);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn preceding<'t>(
        &'t self,
        timestamp: Timestamp,
    ) -> TimeZonePrecedingTransitions<'t> {
        TimeZonePrecedingTransitions { tz: self, cur: timestamp }
    }

    /// Returns an iterator of time zone transitions following the given
    /// timestamp. The iterator returned yields [`TimeZoneTransition`]
    /// elements.
    ///
    /// The order of the iterator returned moves forward through time. If
    /// there is a following transition, then the timestamp of that transition
    /// is guaranteed to be strictly greater than the timestamp given.
    ///
    /// This is a low level API that you generally shouldn't need. It's
    /// useful in cases where you need to know something about the specific
    /// instants at which time zone transitions occur. For example, an embedded
    /// device might need to be explicitly programmed with daylight saving
    /// time transitions. APIs like this enable callers to explore those
    /// transitions.
    ///
    /// A time zone transition refers to a specific point in time when the
    /// offset from UTC for a particular geographical region changes. This
    /// is usually a result of daylight saving time, but it can also occur
    /// when a geographic region changes its permanent offset from UTC.
    ///
    /// The iterator returned is not guaranteed to yield any elements. For
    /// example, this occurs with a fixed offset time zone. Logically, it
    /// would also be possible for the iterator to be infinite, except that
    /// eventually the timestamp would overflow Jiff's maximum timestamp
    /// value, at which point, iteration stops.
    ///
    /// # Example: time until the next transition
    ///
    /// This example shows how much time is left until the next time zone
    /// transition:
    ///
    /// ```
    /// use jiff::{Unit, Zoned};
    ///
    /// let now: Zoned = "2024-12-31 18:25-05[US/Eastern]".parse()?;
    /// let trans = now.time_zone().following(now.timestamp()).next().unwrap();
    /// let next_at = trans.timestamp().to_zoned(now.time_zone().clone());
    /// let span = now.until((Unit::Year, &next_at))?;
    /// assert_eq!(format!("{span:#}"), "2mo 8d 7h 35m");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: show the 5 next time zone transitions
    ///
    /// This shows how to find the 5 following time zone transitions (from a
    /// particular datetime) for a particular time zone:
    ///
    /// ```
    /// use jiff::{tz::offset, Zoned};
    ///
    /// let now: Zoned = "2024-12-31 18:25-05[US/Eastern]".parse()?;
    /// let transitions = now
    ///     .time_zone()
    ///     .following(now.timestamp())
    ///     .take(5)
    ///     .map(|t| (
    ///         t.timestamp().to_zoned(now.time_zone().clone()),
    ///         t.offset(),
    ///         t.abbreviation().to_string(),
    ///     ))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(transitions, vec![
    ///     ("2025-03-09 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
    ///     ("2025-11-02 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
    ///     ("2026-03-08 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
    ///     ("2026-11-01 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
    ///     ("2027-03-14 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
    /// ]);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn following<'t>(
        &'t self,
        timestamp: Timestamp,
    ) -> TimeZoneFollowingTransitions<'t> {
        TimeZoneFollowingTransitions { tz: self, cur: timestamp }
    }

    /// Used by the "preceding transitions" iterator.
    #[inline]
    fn previous_transition(
        &self,
        _timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        match **self.kind.as_ref()? {
            TimeZoneKind::Unknown => None,
            TimeZoneKind::Fixed(_) => None,
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(ref tz) => tz.previous_transition(_timestamp),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(ref tz) => tz.previous_transition(_timestamp),
        }
    }

    /// Used by the "following transitions" iterator.
    #[inline]
    fn next_transition(
        &self,
        _timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        match **self.kind.as_ref()? {
            TimeZoneKind::Unknown => None,
            TimeZoneKind::Fixed(_) => None,
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(ref tz) => tz.next_transition(_timestamp),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(ref tz) => tz.next_transition(_timestamp),
        }
    }

    /// Returns a short description about the kind of this time zone.
    ///
    /// This is useful in error messages.
    fn kind_description(&self) -> &str {
        let Some(ref kind) = self.kind else {
            return "UTC";
        };
        match **kind {
            TimeZoneKind::Unknown => "Etc/Unknown",
            TimeZoneKind::Fixed(_) => "fixed",
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(_) => "POSIX",
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(_) => "IANA",
        }
    }
}

impl core::fmt::Debug for TimeZone {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let field: &dyn core::fmt::Debug = match self.kind {
            None => &"UTC",
            Some(ref kind) => match &**kind {
                TimeZoneKind::Unknown => &"Etc/Unknown",
                TimeZoneKind::Fixed(ref tz) => tz,
                #[cfg(feature = "alloc")]
                TimeZoneKind::Posix(ref tz) => tz,
                #[cfg(feature = "alloc")]
                TimeZoneKind::Tzif(ref tz) => tz,
            },
        };
        f.debug_tuple("TimeZone").field(field).finish()
    }
}

#[derive(Debug, Eq, PartialEq)]
#[cfg_attr(not(feature = "alloc"), derive(Clone))]
enum TimeZoneKind {
    // It would be nice if we could represent this similarly to
    // `TimeZone::UTC`. That is, without putting it behind an `Arc`. But I
    // didn't see an easy way to do that while retaining the single-word size
    // of `TimeZone` without pointer tagging, since `Arc` only gives the
    // compiler a single niche value. Plus, it should be exceptionally rare
    // for a unknown time zone to be used anyway. It's generally an error
    // condition.
    Unknown,
    Fixed(TimeZoneFixed),
    #[cfg(feature = "alloc")]
    Posix(TimeZonePosix),
    #[cfg(feature = "alloc")]
    Tzif(TimeZoneTzif),
}

#[derive(Clone)]
struct TimeZoneFixed {
    offset: Offset,
}

impl TimeZoneFixed {
    #[inline]
    fn new(offset: Offset) -> TimeZoneFixed {
        TimeZoneFixed { offset }
    }

    #[inline]
    fn to_offset(&self) -> Offset {
        self.offset
    }

    #[inline]
    fn to_offset_info(&self) -> TimeZoneOffsetInfo<'_> {
        let abbreviation =
            TimeZoneAbbreviation::Owned(self.offset.to_array_str());
        TimeZoneOffsetInfo { offset: self.offset, dst: Dst::No, abbreviation }
    }
}

impl core::fmt::Debug for TimeZoneFixed {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_tuple("Fixed").field(&self.to_offset()).finish()
    }
}

impl core::fmt::Display for TimeZoneFixed {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.offset, f)
    }
}

impl Eq for TimeZoneFixed {}

impl PartialEq for TimeZoneFixed {
    #[inline]
    fn eq(&self, rhs: &TimeZoneFixed) -> bool {
        self.to_offset() == rhs.to_offset()
    }
}

#[cfg(feature = "alloc")]
#[derive(Clone, Eq, PartialEq)]
struct TimeZonePosix {
    posix: ReasonablePosixTimeZone,
}

#[cfg(feature = "alloc")]
impl TimeZonePosix {
    #[inline]
    fn to_offset(&self, timestamp: Timestamp) -> Offset {
        self.posix.to_offset(timestamp)
    }

    #[inline]
    fn to_offset_info(&self, timestamp: Timestamp) -> TimeZoneOffsetInfo<'_> {
        self.posix.to_offset_info(timestamp)
    }

    #[inline]
    fn to_ambiguous_kind(&self, dt: DateTime) -> AmbiguousOffset {
        self.posix.to_ambiguous_kind(dt)
    }

    #[inline]
    fn previous_transition(
        &self,
        timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        self.posix.previous_transition(timestamp)
    }

    #[inline]
    fn next_transition(
        &self,
        timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        self.posix.next_transition(timestamp)
    }
}

// This is implemented by hand because dumping out the full representation of
// a `ReasonablePosixTimeZone` is way too much noise for users of Jiff.
#[cfg(feature = "alloc")]
impl core::fmt::Debug for TimeZonePosix {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "Posix({})", self.posix)
    }
}

#[cfg(feature = "alloc")]
impl core::fmt::Display for TimeZonePosix {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.posix, f)
    }
}

#[cfg(feature = "alloc")]
#[derive(Eq, PartialEq)]
struct TimeZoneTzif {
    tzif: crate::tz::tzif::TzifOwned,
}

#[cfg(feature = "alloc")]
impl TimeZoneTzif {
    #[inline]
    fn new(
        name: Option<alloc::string::String>,
        bytes: &[u8],
    ) -> Result<TimeZoneTzif, Error> {
        let tzif = crate::tz::tzif::Tzif::parse(name, bytes)?;
        Ok(TimeZoneTzif { tzif })
    }

    #[inline]
    fn name(&self) -> Option<&str> {
        self.tzif.name()
    }

    #[inline]
    fn to_offset(&self, timestamp: Timestamp) -> Offset {
        self.tzif.to_offset(timestamp)
    }

    #[inline]
    fn to_offset_info(&self, timestamp: Timestamp) -> TimeZoneOffsetInfo<'_> {
        self.tzif.to_offset_info(timestamp)
    }

    #[inline]
    fn to_ambiguous_kind(&self, dt: DateTime) -> AmbiguousOffset {
        self.tzif.to_ambiguous_kind(dt)
    }

    #[inline]
    fn previous_transition(
        &self,
        timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        self.tzif.previous_transition(timestamp)
    }

    #[inline]
    fn next_transition(
        &self,
        timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        self.tzif.next_transition(timestamp)
    }
}

// This is implemented by hand because dumping out the full representation of
// all TZif data is too much noise for users of Jiff.
#[cfg(feature = "alloc")]
impl core::fmt::Debug for TimeZoneTzif {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_tuple("TZif").field(&self.name().unwrap_or("Local")).finish()
    }
}

/// A representation a single time zone transition.
///
/// A time zone transition is an instant in time the marks the beginning of
/// a change in the offset from UTC that civil time is computed from in a
/// particular time zone. For example, when daylight saving time comes into
/// effect (or goes away). Another example is when a geographic region changes
/// its permanent offset from UTC.
///
/// This is a low level type that you generally shouldn't need. It's useful in
/// cases where you need to know something about the specific instants at which
/// time zone transitions occur. For example, an embedded device might need to
/// be explicitly programmed with daylight saving time transitions. APIs like
/// this enable callers to explore those transitions.
///
/// This type is yielded by the iterators
/// [`TimeZonePrecedingTransitions`] and
/// [`TimeZoneFollowingTransitions`]. The iterators are created by
/// [`TimeZone::preceding`] and [`TimeZone::following`], respectively.
///
/// # Example
///
/// This shows a somewhat silly example that finds all of the unique civil
/// (or "clock" or "local") times at which a time zone transition has occurred
/// in a particular time zone:
///
/// ```
/// use std::collections::BTreeSet;
/// use jiff::{civil, tz::TimeZone};
///
/// let tz = TimeZone::get("America/New_York")?;
/// let now = civil::date(2024, 12, 31).at(18, 25, 0, 0).to_zoned(tz.clone())?;
/// let mut set = BTreeSet::new();
/// for trans in tz.preceding(now.timestamp()) {
///     let time = tz.to_datetime(trans.timestamp()).time();
///     set.insert(time);
/// }
/// assert_eq!(Vec::from_iter(set), vec![
///     civil::time(1, 0, 0, 0),  // typical transition out of DST
///     civil::time(3, 0, 0, 0),  // typical transition into DST
///     civil::time(12, 0, 0, 0), // from when IANA starts keeping track
///     civil::time(19, 0, 0, 0), // from World War 2
/// ]);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug)]
pub struct TimeZoneTransition<'t> {
    // We don't currently do anything smart to make iterating over
    // transitions faster. We could if we pushed the iterator impl down into
    // the respective modules (`posix` and `tzif`), but it's not clear such
    // optimization is really worth it. However, this API should permit that
    // kind of optimization in the future.
    pub(crate) timestamp: Timestamp,
    pub(crate) offset: Offset,
    pub(crate) abbrev: &'t str,
    pub(crate) dst: Dst,
}

impl<'t> TimeZoneTransition<'t> {
    /// Returns the timestamp at which this transition began.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("US/Eastern")?;
    /// // Look for the first time zone transition in `US/Eastern` following
    /// // 2023-03-09 00:00:00.
    /// let start = civil::date(2024, 3, 9).to_zoned(tz.clone())?.timestamp();
    /// let next = tz.following(start).next().unwrap();
    /// assert_eq!(
    ///     next.timestamp().to_zoned(tz.clone()).to_string(),
    ///     "2024-03-10T03:00:00-04:00[US/Eastern]",
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn timestamp(&self) -> Timestamp {
        self.timestamp
    }

    /// Returns the offset corresponding to this time zone transition. All
    /// instants at and following this transition's timestamp (and before the
    /// next transition's timestamp) need to apply this offset from UTC to get
    /// the civil or "local" time in the corresponding time zone.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, tz::{TimeZone, offset}};
    ///
    /// let tz = TimeZone::get("US/Eastern")?;
    /// // Get the offset of the next transition after
    /// // 2023-03-09 00:00:00.
    /// let start = civil::date(2024, 3, 9).to_zoned(tz.clone())?.timestamp();
    /// let next = tz.following(start).next().unwrap();
    /// assert_eq!(next.offset(), offset(-4));
    /// // Or go backwards to find the previous transition.
    /// let prev = tz.preceding(start).next().unwrap();
    /// assert_eq!(prev.offset(), offset(-5));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn offset(&self) -> Offset {
        self.offset
    }

    /// Returns the time zone abbreviation corresponding to this time
    /// zone transition. All instants at and following this transition's
    /// timestamp (and before the next transition's timestamp) may use this
    /// abbreviation when creating a human readable string. For example,
    /// this is the abbreviation used with the `%Z` specifier with Jiff's
    /// [`fmt::strtime`](crate::fmt::strtime) module.
    ///
    /// Note that abbreviations can to be ambiguous. For example, the
    /// abbreviation `CST` can be used for the time zones `Asia/Shanghai`,
    /// `America/Chicago` and `America/Havana`.
    ///
    /// The lifetime of the string returned is tied to this
    /// `TimeZoneTransition`, which may be shorter than `'t` (the lifetime of
    /// the time zone this transition was created from).
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("US/Eastern")?;
    /// // Get the abbreviation of the next transition after
    /// // 2023-03-09 00:00:00.
    /// let start = civil::date(2024, 3, 9).to_zoned(tz.clone())?.timestamp();
    /// let next = tz.following(start).next().unwrap();
    /// assert_eq!(next.abbreviation(), "EDT");
    /// // Or go backwards to find the previous transition.
    /// let prev = tz.preceding(start).next().unwrap();
    /// assert_eq!(prev.abbreviation(), "EST");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn abbreviation<'a>(&'a self) -> &'a str {
        self.abbrev
    }

    /// Returns whether daylight saving time is enabled for this time zone
    /// transition.
    ///
    /// Callers should generally treat this as informational only. In
    /// particular, not all time zone transitions are related to daylight
    /// saving time. For example, some transitions are a result of a region
    /// permanently changing their offset from UTC.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, tz::{Dst, TimeZone}};
    ///
    /// let tz = TimeZone::get("US/Eastern")?;
    /// // Get the DST status of the next transition after
    /// // 2023-03-09 00:00:00.
    /// let start = civil::date(2024, 3, 9).to_zoned(tz.clone())?.timestamp();
    /// let next = tz.following(start).next().unwrap();
    /// assert_eq!(next.dst(), Dst::Yes);
    /// // Or go backwards to find the previous transition.
    /// let prev = tz.preceding(start).next().unwrap();
    /// assert_eq!(prev.dst(), Dst::No);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn dst(&self) -> Dst {
        self.dst
    }
}

/// An offset along with DST status and a time zone abbreviation.
///
/// This information can be computed from a [`TimeZone`] given a [`Timestamp`]
/// via [`TimeZone::to_offset_info`].
///
/// Generally, the extra information associated with the offset is not commonly
/// needed. And indeed, inspecting the daylight saving time status of a
/// particular instant in a time zone _usually_ leads to bugs. For example, not
/// all time zone transitions are the result of daylight saving time. Some are
/// the result of permanent changes to the standard UTC offset of a region.
///
/// This information is available via an API distinct from
/// [`TimeZone::to_offset`] because it is not commonly needed and because it
/// can sometimes be more expensive to compute.
///
/// The main use case for daylight saving time status or time zone
/// abbreviations is for formatting datetimes in an end user's locale. If you
/// want this, consider using the [`icu`] crate via [`jiff-icu`].
///
/// The lifetime parameter `'t` corresponds to the lifetime of the `TimeZone`
/// that this info was extracted from.
///
/// # Example
///
/// ```
/// use jiff::{tz::{self, Dst, TimeZone}, Timestamp};
///
/// let tz = TimeZone::get("America/New_York")?;
///
/// // A timestamp in DST in New York.
/// let ts = Timestamp::from_second(1_720_493_204)?;
/// let info = tz.to_offset_info(ts);
/// assert_eq!(info.offset(), tz::offset(-4));
/// assert_eq!(info.dst(), Dst::Yes);
/// assert_eq!(info.abbreviation(), "EDT");
/// assert_eq!(
///     info.offset().to_datetime(ts).to_string(),
///     "2024-07-08T22:46:44",
/// );
///
/// // A timestamp *not* in DST in New York.
/// let ts = Timestamp::from_second(1_704_941_204)?;
/// let info = tz.to_offset_info(ts);
/// assert_eq!(info.offset(), tz::offset(-5));
/// assert_eq!(info.dst(), Dst::No);
/// assert_eq!(info.abbreviation(), "EST");
/// assert_eq!(
///     info.offset().to_datetime(ts).to_string(),
///     "2024-01-10T21:46:44",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// [`icu`]: https://docs.rs/icu
/// [`jiff-icu`]: https://docs.rs/jiff-icu
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TimeZoneOffsetInfo<'t> {
    pub(crate) offset: Offset,
    pub(crate) dst: Dst,
    pub(crate) abbreviation: TimeZoneAbbreviation<'t>,
}

impl<'t> TimeZoneOffsetInfo<'t> {
    /// Returns the offset.
    ///
    /// The offset is duration, from UTC, that should be used to offset the
    /// civil time in a particular location.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, tz::{TimeZone, offset}};
    ///
    /// let tz = TimeZone::get("US/Eastern")?;
    /// // Get the offset for 2023-03-10 00:00:00.
    /// let start = civil::date(2024, 3, 10).to_zoned(tz.clone())?.timestamp();
    /// let info = tz.to_offset_info(start);
    /// assert_eq!(info.offset(), offset(-5));
    /// // Go forward a day and notice the offset changes due to DST!
    /// let start = civil::date(2024, 3, 11).to_zoned(tz.clone())?.timestamp();
    /// let info = tz.to_offset_info(start);
    /// assert_eq!(info.offset(), offset(-4));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn offset(&self) -> Offset {
        self.offset
    }

    /// Returns the time zone abbreviation corresponding to this offset info.
    ///
    /// Note that abbreviations can to be ambiguous. For example, the
    /// abbreviation `CST` can be used for the time zones `Asia/Shanghai`,
    /// `America/Chicago` and `America/Havana`.
    ///
    /// The lifetime of the string returned is tied to this
    /// `TimeZoneOffsetInfo`, which may be shorter than `'t` (the lifetime of
    /// the time zone this transition was created from).
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, tz::TimeZone};
    ///
    /// let tz = TimeZone::get("US/Eastern")?;
    /// // Get the time zone abbreviation for 2023-03-10 00:00:00.
    /// let start = civil::date(2024, 3, 10).to_zoned(tz.clone())?.timestamp();
    /// let info = tz.to_offset_info(start);
    /// assert_eq!(info.abbreviation(), "EST");
    /// // Go forward a day and notice the abbreviation changes due to DST!
    /// let start = civil::date(2024, 3, 11).to_zoned(tz.clone())?.timestamp();
    /// let info = tz.to_offset_info(start);
    /// assert_eq!(info.abbreviation(), "EDT");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn abbreviation(&self) -> &str {
        self.abbreviation.as_str()
    }

    /// Returns whether daylight saving time is enabled for this offset
    /// info.
    ///
    /// Callers should generally treat this as informational only. In
    /// particular, not all time zone transitions are related to daylight
    /// saving time. For example, some transitions are a result of a region
    /// permanently changing their offset from UTC.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, tz::{Dst, TimeZone}};
    ///
    /// let tz = TimeZone::get("US/Eastern")?;
    /// // Get the DST status of 2023-03-11 00:00:00.
    /// let start = civil::date(2024, 3, 11).to_zoned(tz.clone())?.timestamp();
    /// let info = tz.to_offset_info(start);
    /// assert_eq!(info.dst(), Dst::Yes);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn dst(&self) -> Dst {
        self.dst
    }
}

/// An iterator over time zone transitions going backward in time.
///
/// This iterator is created by [`TimeZone::preceding`].
///
/// # Example: show the 5 previous time zone transitions
///
/// This shows how to find the 5 preceding time zone transitions (from a
/// particular datetime) for a particular time zone:
///
/// ```
/// use jiff::{tz::offset, Zoned};
///
/// let now: Zoned = "2024-12-31 18:25-05[US/Eastern]".parse()?;
/// let transitions = now
///     .time_zone()
///     .preceding(now.timestamp())
///     .take(5)
///     .map(|t| (
///         t.timestamp().to_zoned(now.time_zone().clone()),
///         t.offset(),
///         t.abbreviation().to_string(),
///     ))
///     .collect::<Vec<_>>();
/// assert_eq!(transitions, vec![
///     ("2024-11-03 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
///     ("2024-03-10 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
///     ("2023-11-05 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
///     ("2023-03-12 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
///     ("2022-11-06 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
/// ]);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug)]
pub struct TimeZonePrecedingTransitions<'t> {
    tz: &'t TimeZone,
    cur: Timestamp,
}

impl<'t> Iterator for TimeZonePrecedingTransitions<'t> {
    type Item = TimeZoneTransition<'t>;

    fn next(&mut self) -> Option<TimeZoneTransition<'t>> {
        let trans = self.tz.previous_transition(self.cur)?;
        self.cur = trans.timestamp();
        Some(trans)
    }
}

impl<'t> core::iter::FusedIterator for TimeZonePrecedingTransitions<'t> {}

/// An iterator over time zone transitions going forward in time.
///
/// This iterator is created by [`TimeZone::following`].
///
/// # Example: show the 5 next time zone transitions
///
/// This shows how to find the 5 following time zone transitions (from a
/// particular datetime) for a particular time zone:
///
/// ```
/// use jiff::{tz::offset, Zoned};
///
/// let now: Zoned = "2024-12-31 18:25-05[US/Eastern]".parse()?;
/// let transitions = now
///     .time_zone()
///     .following(now.timestamp())
///     .take(5)
///     .map(|t| (
///         t.timestamp().to_zoned(now.time_zone().clone()),
///         t.offset(),
///         t.abbreviation().to_string(),
///     ))
///     .collect::<Vec<_>>();
/// assert_eq!(transitions, vec![
///     ("2025-03-09 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
///     ("2025-11-02 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
///     ("2026-03-08 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
///     ("2026-11-01 01:00-05[US/Eastern]".parse()?, offset(-5), "EST".to_string()),
///     ("2027-03-14 03:00-04[US/Eastern]".parse()?, offset(-4), "EDT".to_string()),
/// ]);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug)]
pub struct TimeZoneFollowingTransitions<'t> {
    tz: &'t TimeZone,
    cur: Timestamp,
}

impl<'t> Iterator for TimeZoneFollowingTransitions<'t> {
    type Item = TimeZoneTransition<'t>;

    fn next(&mut self) -> Option<TimeZoneTransition<'t>> {
        let trans = self.tz.next_transition(self.cur)?;
        self.cur = trans.timestamp();
        Some(trans)
    }
}

impl<'t> core::iter::FusedIterator for TimeZoneFollowingTransitions<'t> {}

/// A helper type for converting a `TimeZone` to a succinct human readable
/// description.
///
/// This is principally used in error messages in various places.
///
/// A previous iteration of this was just an `as_str() -> &str` method on
/// `TimeZone`, but that's difficult to do without relying on dynamic memory
/// allocation (or chunky arrays).
pub(crate) struct DiagnosticName<'a>(&'a TimeZone);

impl<'a> core::fmt::Display for DiagnosticName<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let Some(ref kind) = self.0.kind else { return write!(f, "UTC") };
        match **kind {
            TimeZoneKind::Unknown => write!(f, "Etc/Unknown"),
            TimeZoneKind::Fixed(ref tz) => write!(f, "{tz}"),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Posix(ref tz) => write!(f, "{tz}"),
            #[cfg(feature = "alloc")]
            TimeZoneKind::Tzif(ref tz) => {
                write!(f, "{}", tz.name().unwrap_or("Local"))
            }
        }
    }
}

/// A light abstraction over different representations of a time zone
/// abbreviation.
///
/// The lifetime parameter `'t` corresponds to the lifetime of the time zone
/// that produced this abbreviation.
#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub(crate) enum TimeZoneAbbreviation<'t> {
    /// For when the abbreviation is borrowed directly from other data. For
    /// example, from TZif or from POSIX TZ strings.
    Borrowed(&'t str),
    /// For when the abbreviation has to be derived from other data. For
    /// example, from a fixed offset.
    ///
    /// The idea here is that a `TimeZone` shouldn't need to store the
    /// string representation of a fixed offset. Particularly in core-only
    /// environments, this is quite wasteful. So we make the string on-demand
    /// only when it's requested.
    ///
    /// An alternative design is to just implement `Display` and reuse
    /// `Offset`'s `Display` impl, but then we couldn't offer a `-> &str` API.
    /// I feel like that's just a bit overkill, and really just comes from the
    /// core-only straight-jacket.
    Owned(ArrayStr<9>),
}

impl<'t> TimeZoneAbbreviation<'t> {
    /// Returns this abbreviation as a string borrowed from `self`.
    ///
    /// Notice that, like `Cow`, the lifetime of the string returned is
    /// tied to `self` and thus may be shorter than `'t`.
    fn as_str<'a>(&'a self) -> &'a str {
        match *self {
            TimeZoneAbbreviation::Borrowed(s) => s,
            TimeZoneAbbreviation::Owned(ref s) => s.as_str(),
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use crate::tz::testdata::TzifTestFile;
    use crate::{civil::date, tz::offset};

    use super::*;

    fn unambiguous(offset_hours: i8) -> AmbiguousOffset {
        let offset = offset(offset_hours);
        o_unambiguous(offset)
    }

    fn gap(
        earlier_offset_hours: i8,
        later_offset_hours: i8,
    ) -> AmbiguousOffset {
        let earlier = offset(earlier_offset_hours);
        let later = offset(later_offset_hours);
        o_gap(earlier, later)
    }

    fn fold(
        earlier_offset_hours: i8,
        later_offset_hours: i8,
    ) -> AmbiguousOffset {
        let earlier = offset(earlier_offset_hours);
        let later = offset(later_offset_hours);
        o_fold(earlier, later)
    }

    fn o_unambiguous(offset: Offset) -> AmbiguousOffset {
        AmbiguousOffset::Unambiguous { offset }
    }

    fn o_gap(earlier: Offset, later: Offset) -> AmbiguousOffset {
        AmbiguousOffset::Gap { before: earlier, after: later }
    }

    fn o_fold(earlier: Offset, later: Offset) -> AmbiguousOffset {
        AmbiguousOffset::Fold { before: earlier, after: later }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_tzif_to_ambiguous_timestamp() {
        let tests: &[(&str, &[_])] = &[
            (
                "America/New_York",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), gap(-5, -4)),
                    ((2024, 3, 10, 2, 59, 59, 999_999_999), gap(-5, -4)),
                    ((2024, 3, 10, 3, 0, 0, 0), unambiguous(-4)),
                    ((2024, 11, 3, 0, 59, 59, 999_999_999), unambiguous(-4)),
                    ((2024, 11, 3, 1, 0, 0, 0), fold(-4, -5)),
                    ((2024, 11, 3, 1, 59, 59, 999_999_999), fold(-4, -5)),
                    ((2024, 11, 3, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            (
                "Europe/Dublin",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(1)),
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 1)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 1)),
                    ((2024, 3, 31, 2, 0, 0, 0), unambiguous(1)),
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(1)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(1, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(1, 0)),
                    ((2024, 10, 27, 2, 0, 0, 0), unambiguous(0)),
                ],
            ),
            (
                "Australia/Tasmania",
                &[
                    ((1970, 1, 1, 11, 0, 0, 0), unambiguous(11)),
                    ((2024, 4, 7, 1, 59, 59, 999_999_999), unambiguous(11)),
                    ((2024, 4, 7, 2, 0, 0, 0), fold(11, 10)),
                    ((2024, 4, 7, 2, 59, 59, 999_999_999), fold(11, 10)),
                    ((2024, 4, 7, 3, 0, 0, 0), unambiguous(10)),
                    ((2024, 10, 6, 1, 59, 59, 999_999_999), unambiguous(10)),
                    ((2024, 10, 6, 2, 0, 0, 0), gap(10, 11)),
                    ((2024, 10, 6, 2, 59, 59, 999_999_999), gap(10, 11)),
                    ((2024, 10, 6, 3, 0, 0, 0), unambiguous(11)),
                ],
            ),
            (
                "Antarctica/Troll",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(0)),
                    // test the gap
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 2)),
                    // still in the gap!
                    ((2024, 3, 31, 2, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 2, 59, 59, 999_999_999), gap(0, 2)),
                    // finally out
                    ((2024, 3, 31, 3, 0, 0, 0), unambiguous(2)),
                    // test the fold
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(2)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(2, 0)),
                    // still in the fold!
                    ((2024, 10, 27, 2, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 2, 59, 59, 999_999_999), fold(2, 0)),
                    // finally out
                    ((2024, 10, 27, 3, 0, 0, 0), unambiguous(0)),
                ],
            ),
            (
                "America/St_Johns",
                &[
                    (
                        (1969, 12, 31, 20, 30, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 0, 0, 0),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 59, 59, 999_999_999),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 0, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 0, 0, 0),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 2, 0, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                ],
            ),
            // This time zone has an interesting transition where it jumps
            // backwards a full day at 1867-10-19T15:30:00.
            (
                "America/Sitka",
                &[
                    ((1969, 12, 31, 16, 0, 0, 0), unambiguous(-8)),
                    (
                        (-9999, 1, 2, 16, 58, 46, 0),
                        o_unambiguous(Offset::hms(14, 58, 47)),
                    ),
                    (
                        (1867, 10, 18, 15, 29, 59, 0),
                        o_unambiguous(Offset::hms(14, 58, 47)),
                    ),
                    (
                        (1867, 10, 18, 15, 30, 0, 0),
                        // A fold of 24 hours!!!
                        o_fold(
                            Offset::hms(14, 58, 47),
                            -Offset::hms(9, 1, 13),
                        ),
                    ),
                    (
                        (1867, 10, 19, 15, 29, 59, 999_999_999),
                        // Still in the fold...
                        o_fold(
                            Offset::hms(14, 58, 47),
                            -Offset::hms(9, 1, 13),
                        ),
                    ),
                    (
                        (1867, 10, 19, 15, 30, 0, 0),
                        // Finally out.
                        o_unambiguous(-Offset::hms(9, 1, 13)),
                    ),
                ],
            ),
            // As with to_datetime, we test every possible transition
            // point here since this time zone has a small number of them.
            (
                "Pacific/Honolulu",
                &[
                    (
                        (1896, 1, 13, 11, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 31, 26)),
                    ),
                    (
                        (1896, 1, 13, 12, 0, 0, 0),
                        o_gap(
                            -Offset::hms(10, 31, 26),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1896, 1, 13, 12, 1, 25, 0),
                        o_gap(
                            -Offset::hms(10, 31, 26),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1896, 1, 13, 12, 1, 26, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 1, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 2, 0, 0, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 2, 59, 59, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 5, 21, 10, 59, 59, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 5, 21, 11, 0, 0, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1933, 5, 21, 11, 59, 59, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1933, 5, 21, 12, 0, 0, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 1, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 2, 0, 0, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 2, 59, 59, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 8, 14, 13, 29, 59, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 8, 14, 13, 30, 0, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 8, 14, 13, 30, 1, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 9, 30, 0, 59, 59, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 9, 30, 1, 0, 0, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1945, 9, 30, 1, 59, 59, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1945, 9, 30, 2, 0, 0, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1947, 6, 8, 1, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1947, 6, 8, 2, 0, 0, 0),
                        o_gap(-Offset::hms(10, 30, 0), -offset(10)),
                    ),
                    (
                        (1947, 6, 8, 2, 29, 59, 0),
                        o_gap(-Offset::hms(10, 30, 0), -offset(10)),
                    ),
                    ((1947, 6, 8, 2, 30, 0, 0), unambiguous(-10)),
                ],
            ),
        ];
        for &(tzname, datetimes_to_ambiguous) in tests {
            let test_file = TzifTestFile::get(tzname);
            let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
            for &(datetime, ambiguous_kind) in datetimes_to_ambiguous {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let dt = date(year, month, day).at(hour, min, sec, nano);
                let got = tz.to_ambiguous_zoned(dt);
                assert_eq!(
                    got.offset(),
                    ambiguous_kind,
                    "\nTZ: {tzname}\ndatetime: \
                     {year:04}-{month:02}-{day:02}T\
                     {hour:02}:{min:02}:{sec:02}.{nano:09}",
                );
            }
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_tzif_to_datetime() {
        let o = |hours| offset(hours);
        let tests: &[(&str, &[_])] = &[
            (
                "America/New_York",
                &[
                    ((0, 0), o(-5), "EST", (1969, 12, 31, 19, 0, 0, 0)),
                    (
                        (1710052200, 0),
                        o(-5),
                        "EST",
                        (2024, 3, 10, 1, 30, 0, 0),
                    ),
                    (
                        (1710053999, 999_999_999),
                        o(-5),
                        "EST",
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                    ),
                    ((1710054000, 0), o(-4), "EDT", (2024, 3, 10, 3, 0, 0, 0)),
                    (
                        (1710055800, 0),
                        o(-4),
                        "EDT",
                        (2024, 3, 10, 3, 30, 0, 0),
                    ),
                    ((1730610000, 0), o(-4), "EDT", (2024, 11, 3, 1, 0, 0, 0)),
                    (
                        (1730611800, 0),
                        o(-4),
                        "EDT",
                        (2024, 11, 3, 1, 30, 0, 0),
                    ),
                    (
                        (1730613599, 999_999_999),
                        o(-4),
                        "EDT",
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                    ),
                    ((1730613600, 0), o(-5), "EST", (2024, 11, 3, 1, 0, 0, 0)),
                    (
                        (1730615400, 0),
                        o(-5),
                        "EST",
                        (2024, 11, 3, 1, 30, 0, 0),
                    ),
                ],
            ),
            (
                "Australia/Tasmania",
                &[
                    ((0, 0), o(11), "AEDT", (1970, 1, 1, 11, 0, 0, 0)),
                    (
                        (1728142200, 0),
                        o(10),
                        "AEST",
                        (2024, 10, 6, 1, 30, 0, 0),
                    ),
                    (
                        (1728143999, 999_999_999),
                        o(10),
                        "AEST",
                        (2024, 10, 6, 1, 59, 59, 999_999_999),
                    ),
                    (
                        (1728144000, 0),
                        o(11),
                        "AEDT",
                        (2024, 10, 6, 3, 0, 0, 0),
                    ),
                    (
                        (1728145800, 0),
                        o(11),
                        "AEDT",
                        (2024, 10, 6, 3, 30, 0, 0),
                    ),
                    ((1712415600, 0), o(11), "AEDT", (2024, 4, 7, 2, 0, 0, 0)),
                    (
                        (1712417400, 0),
                        o(11),
                        "AEDT",
                        (2024, 4, 7, 2, 30, 0, 0),
                    ),
                    (
                        (1712419199, 999_999_999),
                        o(11),
                        "AEDT",
                        (2024, 4, 7, 2, 59, 59, 999_999_999),
                    ),
                    ((1712419200, 0), o(10), "AEST", (2024, 4, 7, 2, 0, 0, 0)),
                    (
                        (1712421000, 0),
                        o(10),
                        "AEST",
                        (2024, 4, 7, 2, 30, 0, 0),
                    ),
                ],
            ),
            // Pacific/Honolulu is small eough that we just test every
            // possible instant before, at and after each transition.
            (
                "Pacific/Honolulu",
                &[
                    (
                        (-2334101315, 0),
                        -Offset::hms(10, 31, 26),
                        "LMT",
                        (1896, 1, 13, 11, 59, 59, 0),
                    ),
                    (
                        (-2334101314, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1896, 1, 13, 12, 1, 26, 0),
                    ),
                    (
                        (-2334101313, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1896, 1, 13, 12, 1, 27, 0),
                    ),
                    (
                        (-1157283001, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1933, 4, 30, 1, 59, 59, 0),
                    ),
                    (
                        (-1157283000, 0),
                        -Offset::hms(9, 30, 0),
                        "HDT",
                        (1933, 4, 30, 3, 0, 0, 0),
                    ),
                    (
                        (-1157282999, 0),
                        -Offset::hms(9, 30, 0),
                        "HDT",
                        (1933, 4, 30, 3, 0, 1, 0),
                    ),
                    (
                        (-1155436201, 0),
                        -Offset::hms(9, 30, 0),
                        "HDT",
                        (1933, 5, 21, 11, 59, 59, 0),
                    ),
                    (
                        (-1155436200, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1933, 5, 21, 11, 0, 0, 0),
                    ),
                    (
                        (-1155436199, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1933, 5, 21, 11, 0, 1, 0),
                    ),
                    (
                        (-880198201, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1942, 2, 9, 1, 59, 59, 0),
                    ),
                    (
                        (-880198200, 0),
                        -Offset::hms(9, 30, 0),
                        "HWT",
                        (1942, 2, 9, 3, 0, 0, 0),
                    ),
                    (
                        (-880198199, 0),
                        -Offset::hms(9, 30, 0),
                        "HWT",
                        (1942, 2, 9, 3, 0, 1, 0),
                    ),
                    (
                        (-769395601, 0),
                        -Offset::hms(9, 30, 0),
                        "HWT",
                        (1945, 8, 14, 13, 29, 59, 0),
                    ),
                    (
                        (-769395600, 0),
                        -Offset::hms(9, 30, 0),
                        "HPT",
                        (1945, 8, 14, 13, 30, 0, 0),
                    ),
                    (
                        (-769395599, 0),
                        -Offset::hms(9, 30, 0),
                        "HPT",
                        (1945, 8, 14, 13, 30, 1, 0),
                    ),
                    (
                        (-765376201, 0),
                        -Offset::hms(9, 30, 0),
                        "HPT",
                        (1945, 9, 30, 1, 59, 59, 0),
                    ),
                    (
                        (-765376200, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1945, 9, 30, 1, 0, 0, 0),
                    ),
                    (
                        (-765376199, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1945, 9, 30, 1, 0, 1, 0),
                    ),
                    (
                        (-712150201, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1947, 6, 8, 1, 59, 59, 0),
                    ),
                    // At this point, we hit the last transition and the POSIX
                    // TZ string takes over.
                    (
                        (-712150200, 0),
                        -Offset::hms(10, 0, 0),
                        "HST",
                        (1947, 6, 8, 2, 30, 0, 0),
                    ),
                    (
                        (-712150199, 0),
                        -Offset::hms(10, 0, 0),
                        "HST",
                        (1947, 6, 8, 2, 30, 1, 0),
                    ),
                ],
            ),
            // This time zone has an interesting transition where it jumps
            // backwards a full day at 1867-10-19T15:30:00.
            (
                "America/Sitka",
                &[
                    ((0, 0), o(-8), "PST", (1969, 12, 31, 16, 0, 0, 0)),
                    (
                        (-377705023201, 0),
                        Offset::hms(14, 58, 47),
                        "LMT",
                        (-9999, 1, 2, 16, 58, 46, 0),
                    ),
                    (
                        (-3225223728, 0),
                        Offset::hms(14, 58, 47),
                        "LMT",
                        (1867, 10, 19, 15, 29, 59, 0),
                    ),
                    // Notice the 24 hour time jump backwards a whole day!
                    (
                        (-3225223727, 0),
                        -Offset::hms(9, 1, 13),
                        "LMT",
                        (1867, 10, 18, 15, 30, 0, 0),
                    ),
                    (
                        (-3225223726, 0),
                        -Offset::hms(9, 1, 13),
                        "LMT",
                        (1867, 10, 18, 15, 30, 1, 0),
                    ),
                ],
            ),
        ];
        for &(tzname, timestamps_to_datetimes) in tests {
            let test_file = TzifTestFile::get(tzname);
            let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
            for &((unix_sec, unix_nano), offset, abbrev, datetime) in
                timestamps_to_datetimes
            {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let timestamp = Timestamp::new(unix_sec, unix_nano).unwrap();
                let info = tz.to_offset_info(timestamp);
                assert_eq!(
                    info.offset(),
                    offset,
                    "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
                );
                assert_eq!(
                    info.abbreviation(),
                    abbrev,
                    "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
                );
                assert_eq!(
                    info.offset().to_datetime(timestamp),
                    date(year, month, day).at(hour, min, sec, nano),
                    "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
                );
            }
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_posix_to_ambiguous_timestamp() {
        let tests: &[(&str, &[_])] = &[
            // America/New_York, but a utopia in which DST is abolished.
            (
                "EST5",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            // The standard DST rule for America/New_York.
            (
                "EST5EDT,M3.2.0,M11.1.0",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), gap(-5, -4)),
                    ((2024, 3, 10, 2, 59, 59, 999_999_999), gap(-5, -4)),
                    ((2024, 3, 10, 3, 0, 0, 0), unambiguous(-4)),
                    ((2024, 11, 3, 0, 59, 59, 999_999_999), unambiguous(-4)),
                    ((2024, 11, 3, 1, 0, 0, 0), fold(-4, -5)),
                    ((2024, 11, 3, 1, 59, 59, 999_999_999), fold(-4, -5)),
                    ((2024, 11, 3, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            // A bit of a nonsensical America/New_York that has DST, but whose
            // offset is equivalent to standard time. Having the same offset
            // means there's never any ambiguity.
            (
                "EST5EDT5,M3.2.0,M11.1.0",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 2, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 3, 0, 0, 0), unambiguous(-5)),
                    ((2024, 11, 3, 0, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 11, 3, 1, 0, 0, 0), unambiguous(-5)),
                    ((2024, 11, 3, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 11, 3, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            // This is Europe/Dublin's rule. It's interesting because its
            // DST is an offset behind standard time. (DST is usually one hour
            // ahead of standard time.)
            (
                "IST-1GMT0,M10.5.0,M3.5.0/1",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(0)),
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 1)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 1)),
                    ((2024, 3, 31, 2, 0, 0, 0), unambiguous(1)),
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(1)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(1, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(1, 0)),
                    ((2024, 10, 27, 2, 0, 0, 0), unambiguous(0)),
                ],
            ),
            // This is Australia/Tasmania's rule. We chose this because it's
            // in the southern hemisphere where DST still skips ahead one hour,
            // but it usually starts in the fall and ends in the spring.
            (
                "AEST-10AEDT,M10.1.0,M4.1.0/3",
                &[
                    ((1970, 1, 1, 11, 0, 0, 0), unambiguous(11)),
                    ((2024, 4, 7, 1, 59, 59, 999_999_999), unambiguous(11)),
                    ((2024, 4, 7, 2, 0, 0, 0), fold(11, 10)),
                    ((2024, 4, 7, 2, 59, 59, 999_999_999), fold(11, 10)),
                    ((2024, 4, 7, 3, 0, 0, 0), unambiguous(10)),
                    ((2024, 10, 6, 1, 59, 59, 999_999_999), unambiguous(10)),
                    ((2024, 10, 6, 2, 0, 0, 0), gap(10, 11)),
                    ((2024, 10, 6, 2, 59, 59, 999_999_999), gap(10, 11)),
                    ((2024, 10, 6, 3, 0, 0, 0), unambiguous(11)),
                ],
            ),
            // This is Antarctica/Troll's rule. We chose this one because its
            // DST transition is 2 hours instead of the standard 1 hour. This
            // means gaps and folds are twice as long as they usually are. And
            // it means there are 22 hour and 26 hour days, respectively. Wow!
            (
                "<+00>0<+02>-2,M3.5.0/1,M10.5.0/3",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(0)),
                    // test the gap
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 2)),
                    // still in the gap!
                    ((2024, 3, 31, 2, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 2, 59, 59, 999_999_999), gap(0, 2)),
                    // finally out
                    ((2024, 3, 31, 3, 0, 0, 0), unambiguous(2)),
                    // test the fold
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(2)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(2, 0)),
                    // still in the fold!
                    ((2024, 10, 27, 2, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 2, 59, 59, 999_999_999), fold(2, 0)),
                    // finally out
                    ((2024, 10, 27, 3, 0, 0, 0), unambiguous(0)),
                ],
            ),
            // This is America/St_Johns' rule, which has an offset with
            // non-zero minutes *and* a DST transition rule. (Indian Standard
            // Time is the one I'm more familiar with, but it turns out IST
            // does not have DST!)
            (
                "NST3:30NDT,M3.2.0,M11.1.0",
                &[
                    (
                        (1969, 12, 31, 20, 30, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 0, 0, 0),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 59, 59, 999_999_999),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 0, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 0, 0, 0),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 2, 0, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                ],
            ),
        ];
        for &(posix_tz, datetimes_to_ambiguous) in tests {
            let tz = TimeZone::posix(posix_tz).unwrap();
            for &(datetime, ambiguous_kind) in datetimes_to_ambiguous {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let dt = date(year, month, day).at(hour, min, sec, nano);
                let got = tz.to_ambiguous_zoned(dt);
                assert_eq!(
                    got.offset(),
                    ambiguous_kind,
                    "\nTZ: {posix_tz}\ndatetime: \
                     {year:04}-{month:02}-{day:02}T\
                     {hour:02}:{min:02}:{sec:02}.{nano:09}",
                );
            }
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_posix_to_datetime() {
        let o = |hours| offset(hours);
        let tests: &[(&str, &[_])] = &[
            ("EST5", &[((0, 0), o(-5), (1969, 12, 31, 19, 0, 0, 0))]),
            (
                // From America/New_York
                "EST5EDT,M3.2.0,M11.1.0",
                &[
                    ((0, 0), o(-5), (1969, 12, 31, 19, 0, 0, 0)),
                    ((1710052200, 0), o(-5), (2024, 3, 10, 1, 30, 0, 0)),
                    (
                        (1710053999, 999_999_999),
                        o(-5),
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                    ),
                    ((1710054000, 0), o(-4), (2024, 3, 10, 3, 0, 0, 0)),
                    ((1710055800, 0), o(-4), (2024, 3, 10, 3, 30, 0, 0)),
                    ((1730610000, 0), o(-4), (2024, 11, 3, 1, 0, 0, 0)),
                    ((1730611800, 0), o(-4), (2024, 11, 3, 1, 30, 0, 0)),
                    (
                        (1730613599, 999_999_999),
                        o(-4),
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                    ),
                    ((1730613600, 0), o(-5), (2024, 11, 3, 1, 0, 0, 0)),
                    ((1730615400, 0), o(-5), (2024, 11, 3, 1, 30, 0, 0)),
                ],
            ),
            (
                // From Australia/Tasmania
                //
                // We chose this because it's a time zone in the southern
                // hemisphere with DST. Unlike the northern hemisphere, its DST
                // starts in the fall and ends in the spring. In the northern
                // hemisphere, we typically start DST in the spring and end it
                // in the fall.
                "AEST-10AEDT,M10.1.0,M4.1.0/3",
                &[
                    ((0, 0), o(11), (1970, 1, 1, 11, 0, 0, 0)),
                    ((1728142200, 0), o(10), (2024, 10, 6, 1, 30, 0, 0)),
                    (
                        (1728143999, 999_999_999),
                        o(10),
                        (2024, 10, 6, 1, 59, 59, 999_999_999),
                    ),
                    ((1728144000, 0), o(11), (2024, 10, 6, 3, 0, 0, 0)),
                    ((1728145800, 0), o(11), (2024, 10, 6, 3, 30, 0, 0)),
                    ((1712415600, 0), o(11), (2024, 4, 7, 2, 0, 0, 0)),
                    ((1712417400, 0), o(11), (2024, 4, 7, 2, 30, 0, 0)),
                    (
                        (1712419199, 999_999_999),
                        o(11),
                        (2024, 4, 7, 2, 59, 59, 999_999_999),
                    ),
                    ((1712419200, 0), o(10), (2024, 4, 7, 2, 0, 0, 0)),
                    ((1712421000, 0), o(10), (2024, 4, 7, 2, 30, 0, 0)),
                ],
            ),
            (
                // Uses the maximum possible offset. A sloppy read of POSIX
                // seems to indicate the maximum offset is 24:59:59, but since
                // DST defaults to 1 hour ahead of standard time, it's possible
                // to use 24:59:59 for standard time, omit the DST offset, and
                // thus get a DST offset of 25:59:59.
                "XXX-24:59:59YYY,M3.2.0,M11.1.0",
                &[
                    // 2024-01-05T00:00:00+00
                    (
                        (1704412800, 0),
                        Offset::hms(24, 59, 59),
                        (2024, 1, 6, 0, 59, 59, 0),
                    ),
                    // 2024-06-05T00:00:00+00 (DST)
                    (
                        (1717545600, 0),
                        Offset::hms(25, 59, 59),
                        (2024, 6, 6, 1, 59, 59, 0),
                    ),
                ],
            ),
        ];
        for &(posix_tz, timestamps_to_datetimes) in tests {
            let tz = TimeZone::posix(posix_tz).unwrap();
            for &((unix_sec, unix_nano), offset, datetime) in
                timestamps_to_datetimes
            {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let timestamp = Timestamp::new(unix_sec, unix_nano).unwrap();
                assert_eq!(
                    tz.to_offset(timestamp),
                    offset,
                    "\ntimestamp({unix_sec}, {unix_nano})",
                );
                assert_eq!(
                    tz.to_datetime(timestamp),
                    date(year, month, day).at(hour, min, sec, nano),
                    "\ntimestamp({unix_sec}, {unix_nano})",
                );
            }
        }
    }

    #[test]
    fn time_zone_fixed_to_datetime() {
        let tz = offset(-5).to_time_zone();
        let unix_epoch = Timestamp::new(0, 0).unwrap();
        assert_eq!(
            tz.to_datetime(unix_epoch),
            date(1969, 12, 31).at(19, 0, 0, 0),
        );

        let tz = Offset::from_seconds(93_599).unwrap().to_time_zone();
        let timestamp = Timestamp::new(253402207200, 999_999_999).unwrap();
        assert_eq!(
            tz.to_datetime(timestamp),
            date(9999, 12, 31).at(23, 59, 59, 999_999_999),
        );

        let tz = Offset::from_seconds(-93_599).unwrap().to_time_zone();
        let timestamp = Timestamp::new(-377705023201, 0).unwrap();
        assert_eq!(
            tz.to_datetime(timestamp),
            date(-9999, 1, 1).at(0, 0, 0, 0),
        );
    }

    #[test]
    fn time_zone_fixed_to_timestamp() {
        let tz = offset(-5).to_time_zone();
        let dt = date(1969, 12, 31).at(19, 0, 0, 0);
        assert_eq!(
            tz.to_zoned(dt).unwrap().timestamp(),
            Timestamp::new(0, 0).unwrap()
        );

        let tz = Offset::from_seconds(93_599).unwrap().to_time_zone();
        let dt = date(9999, 12, 31).at(23, 59, 59, 999_999_999);
        assert_eq!(
            tz.to_zoned(dt).unwrap().timestamp(),
            Timestamp::new(253402207200, 999_999_999).unwrap(),
        );
        let tz = Offset::from_seconds(93_598).unwrap().to_time_zone();
        assert!(tz.to_zoned(dt).is_err());

        let tz = Offset::from_seconds(-93_599).unwrap().to_time_zone();
        let dt = date(-9999, 1, 1).at(0, 0, 0, 0);
        assert_eq!(
            tz.to_zoned(dt).unwrap().timestamp(),
            Timestamp::new(-377705023201, 0).unwrap(),
        );
        let tz = Offset::from_seconds(-93_598).unwrap().to_time_zone();
        assert!(tz.to_zoned(dt).is_err());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_tzif_previous_transition() {
        let tests: &[(&str, &[(&str, Option<&str>)])] = &[
            (
                "UTC",
                &[
                    ("1969-12-31T19Z", None),
                    ("2024-03-10T02Z", None),
                    ("-009999-12-01 00Z", None),
                    ("9999-12-01 00Z", None),
                ],
            ),
            (
                "America/New_York",
                &[
                    ("2024-03-10 08Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 07:00:00.000000001Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 07Z", Some("2023-11-05 06Z")),
                    ("2023-11-05 06Z", Some("2023-03-12 07Z")),
                    ("-009999-01-31 00Z", None),
                    ("9999-12-01 00Z", Some("9999-11-07 06Z")),
                    // While at present we have "fat" TZif files for our
                    // testdata, it's conceivable they could be swapped to
                    // "slim." In which case, the tests above will mostly just
                    // be testing POSIX TZ strings and not the TZif logic. So
                    // below, we include times that will be in slim (i.e.,
                    // historical times the precede the current DST rule).
                    ("1969-12-31 19Z", Some("1969-10-26 06Z")),
                    ("2000-04-02 08Z", Some("2000-04-02 07Z")),
                    ("2000-04-02 07:00:00.000000001Z", Some("2000-04-02 07Z")),
                    ("2000-04-02 07Z", Some("1999-10-31 06Z")),
                    ("1999-10-31 06Z", Some("1999-04-04 07Z")),
                ],
            ),
            (
                "Australia/Tasmania",
                &[
                    ("2010-04-03 17Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 16:00:00.000000001Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 16Z", Some("2009-10-03 16Z")),
                    ("2009-10-03 16Z", Some("2009-04-04 16Z")),
                    ("-009999-01-31 00Z", None),
                    ("9999-12-01 00Z", Some("9999-10-02 16Z")),
                    // Tests for historical data from tzdb. No POSIX TZ.
                    ("2000-03-25 17Z", Some("2000-03-25 16Z")),
                    ("2000-03-25 16:00:00.000000001Z", Some("2000-03-25 16Z")),
                    ("2000-03-25 16Z", Some("1999-10-02 16Z")),
                    ("1999-10-02 16Z", Some("1999-03-27 16Z")),
                ],
            ),
            // This is Europe/Dublin's rule. It's interesting because its
            // DST is an offset behind standard time. (DST is usually one hour
            // ahead of standard time.)
            (
                "Europe/Dublin",
                &[
                    ("2010-03-28 02Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 01:00:00.000000001Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 01Z", Some("2009-10-25 01Z")),
                    ("2009-10-25 01Z", Some("2009-03-29 01Z")),
                    ("-009999-01-31 00Z", None),
                    ("9999-12-01 00Z", Some("9999-10-31 01Z")),
                    // Tests for historical data from tzdb. No POSIX TZ.
                    ("1990-03-25 02Z", Some("1990-03-25 01Z")),
                    ("1990-03-25 01:00:00.000000001Z", Some("1990-03-25 01Z")),
                    ("1990-03-25 01Z", Some("1989-10-29 01Z")),
                    ("1989-10-25 01Z", Some("1989-03-26 01Z")),
                ],
            ),
        ];
        for &(tzname, prev_trans) in tests {
            let test_file = TzifTestFile::get(tzname);
            let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
            for (given, expected) in prev_trans {
                let given: Timestamp = given.parse().unwrap();
                let expected =
                    expected.map(|s| s.parse::<Timestamp>().unwrap());
                let got = tz.previous_transition(given).map(|t| t.timestamp());
                assert_eq!(got, expected, "\nTZ: {tzname}\ngiven: {given}");
            }
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_tzif_next_transition() {
        let tests: &[(&str, &[(&str, Option<&str>)])] = &[
            (
                "UTC",
                &[
                    ("1969-12-31T19Z", None),
                    ("2024-03-10T02Z", None),
                    ("-009999-12-01 00Z", None),
                    ("9999-12-01 00Z", None),
                ],
            ),
            (
                "America/New_York",
                &[
                    ("2024-03-10 06Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 06:59:59.999999999Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 07Z", Some("2024-11-03 06Z")),
                    ("2024-11-03 06Z", Some("2025-03-09 07Z")),
                    ("-009999-12-01 00Z", Some("1883-11-18 17Z")),
                    ("9999-12-01 00Z", None),
                    // While at present we have "fat" TZif files for our
                    // testdata, it's conceivable they could be swapped to
                    // "slim." In which case, the tests above will mostly just
                    // be testing POSIX TZ strings and not the TZif logic. So
                    // below, we include times that will be in slim (i.e.,
                    // historical times the precede the current DST rule).
                    ("1969-12-31 19Z", Some("1970-04-26 07Z")),
                    ("2000-04-02 06Z", Some("2000-04-02 07Z")),
                    ("2000-04-02 06:59:59.999999999Z", Some("2000-04-02 07Z")),
                    ("2000-04-02 07Z", Some("2000-10-29 06Z")),
                    ("2000-10-29 06Z", Some("2001-04-01 07Z")),
                ],
            ),
            (
                "Australia/Tasmania",
                &[
                    ("2010-04-03 15Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 15:59:59.999999999Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 16Z", Some("2010-10-02 16Z")),
                    ("2010-10-02 16Z", Some("2011-04-02 16Z")),
                    ("-009999-12-01 00Z", Some("1895-08-31 14:10:44Z")),
                    ("9999-12-01 00Z", None),
                    // Tests for historical data from tzdb. No POSIX TZ.
                    ("2000-03-25 15Z", Some("2000-03-25 16Z")),
                    ("2000-03-25 15:59:59.999999999Z", Some("2000-03-25 16Z")),
                    ("2000-03-25 16Z", Some("2000-08-26 16Z")),
                    ("2000-08-26 16Z", Some("2001-03-24 16Z")),
                ],
            ),
            (
                "Europe/Dublin",
                &[
                    ("2010-03-28 00Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 00:59:59.999999999Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 01Z", Some("2010-10-31 01Z")),
                    ("2010-10-31 01Z", Some("2011-03-27 01Z")),
                    ("-009999-12-01 00Z", Some("1880-08-02 00:25:21Z")),
                    ("9999-12-01 00Z", None),
                    // Tests for historical data from tzdb. No POSIX TZ.
                    ("1990-03-25 00Z", Some("1990-03-25 01Z")),
                    ("1990-03-25 00:59:59.999999999Z", Some("1990-03-25 01Z")),
                    ("1990-03-25 01Z", Some("1990-10-28 01Z")),
                    ("1990-10-28 01Z", Some("1991-03-31 01Z")),
                ],
            ),
        ];
        for &(tzname, next_trans) in tests {
            let test_file = TzifTestFile::get(tzname);
            let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
            for (given, expected) in next_trans {
                let given: Timestamp = given.parse().unwrap();
                let expected =
                    expected.map(|s| s.parse::<Timestamp>().unwrap());
                let got = tz.next_transition(given).map(|t| t.timestamp());
                assert_eq!(got, expected, "\nTZ: {tzname}\ngiven: {given}");
            }
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_posix_previous_transition() {
        let tests: &[(&str, &[(&str, Option<&str>)])] = &[
            // America/New_York, but a utopia in which DST is abolished. There
            // are no time zone transitions, so next_transition always returns
            // None.
            (
                "EST5",
                &[
                    ("1969-12-31T19Z", None),
                    ("2024-03-10T02Z", None),
                    ("-009999-12-01 00Z", None),
                    ("9999-12-01 00Z", None),
                ],
            ),
            // The standard DST rule for America/New_York.
            (
                "EST5EDT,M3.2.0,M11.1.0",
                &[
                    ("1969-12-31 19Z", Some("1969-11-02 06Z")),
                    ("2024-03-10 08Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 07:00:00.000000001Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 07Z", Some("2023-11-05 06Z")),
                    ("2023-11-05 06Z", Some("2023-03-12 07Z")),
                    ("-009999-01-31 00Z", None),
                    ("9999-12-01 00Z", Some("9999-11-07 06Z")),
                ],
            ),
            (
                // From Australia/Tasmania
                "AEST-10AEDT,M10.1.0,M4.1.0/3",
                &[
                    ("2010-04-03 17Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 16:00:00.000000001Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 16Z", Some("2009-10-03 16Z")),
                    ("2009-10-03 16Z", Some("2009-04-04 16Z")),
                    ("-009999-01-31 00Z", None),
                    ("9999-12-01 00Z", Some("9999-10-02 16Z")),
                ],
            ),
            // This is Europe/Dublin's rule. It's interesting because its
            // DST is an offset behind standard time. (DST is usually one hour
            // ahead of standard time.)
            (
                "IST-1GMT0,M10.5.0,M3.5.0/1",
                &[
                    ("2010-03-28 02Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 01:00:00.000000001Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 01Z", Some("2009-10-25 01Z")),
                    ("2009-10-25 01Z", Some("2009-03-29 01Z")),
                    ("-009999-01-31 00Z", None),
                    ("9999-12-01 00Z", Some("9999-10-31 01Z")),
                ],
            ),
        ];
        for &(posix_tz, prev_trans) in tests {
            let tz = TimeZone::posix(posix_tz).unwrap();
            for (given, expected) in prev_trans {
                let given: Timestamp = given.parse().unwrap();
                let expected =
                    expected.map(|s| s.parse::<Timestamp>().unwrap());
                let got = tz.previous_transition(given).map(|t| t.timestamp());
                assert_eq!(got, expected, "\nTZ: {posix_tz}\ngiven: {given}");
            }
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn time_zone_posix_next_transition() {
        let tests: &[(&str, &[(&str, Option<&str>)])] = &[
            // America/New_York, but a utopia in which DST is abolished. There
            // are no time zone transitions, so next_transition always returns
            // None.
            (
                "EST5",
                &[
                    ("1969-12-31T19Z", None),
                    ("2024-03-10T02Z", None),
                    ("-009999-12-01 00Z", None),
                    ("9999-12-01 00Z", None),
                ],
            ),
            // The standard DST rule for America/New_York.
            (
                "EST5EDT,M3.2.0,M11.1.0",
                &[
                    ("1969-12-31 19Z", Some("1970-03-08 07Z")),
                    ("2024-03-10 06Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 06:59:59.999999999Z", Some("2024-03-10 07Z")),
                    ("2024-03-10 07Z", Some("2024-11-03 06Z")),
                    ("2024-11-03 06Z", Some("2025-03-09 07Z")),
                    ("-009999-12-01 00Z", Some("-009998-03-10 07Z")),
                    ("9999-12-01 00Z", None),
                ],
            ),
            (
                // From Australia/Tasmania
                "AEST-10AEDT,M10.1.0,M4.1.0/3",
                &[
                    ("2010-04-03 15Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 15:59:59.999999999Z", Some("2010-04-03 16Z")),
                    ("2010-04-03 16Z", Some("2010-10-02 16Z")),
                    ("2010-10-02 16Z", Some("2011-04-02 16Z")),
                    ("-009999-12-01 00Z", Some("-009998-04-06 16Z")),
                    ("9999-12-01 00Z", None),
                ],
            ),
            // This is Europe/Dublin's rule. It's interesting because its
            // DST is an offset behind standard time. (DST is usually one hour
            // ahead of standard time.)
            (
                "IST-1GMT0,M10.5.0,M3.5.0/1",
                &[
                    ("2010-03-28 00Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 00:59:59.999999999Z", Some("2010-03-28 01Z")),
                    ("2010-03-28 01Z", Some("2010-10-31 01Z")),
                    ("2010-10-31 01Z", Some("2011-03-27 01Z")),
                    ("-009999-12-01 00Z", Some("-009998-03-31 01Z")),
                    ("9999-12-01 00Z", None),
                ],
            ),
        ];
        for &(posix_tz, next_trans) in tests {
            let tz = TimeZone::posix(posix_tz).unwrap();
            for (given, expected) in next_trans {
                let given: Timestamp = given.parse().unwrap();
                let expected =
                    expected.map(|s| s.parse::<Timestamp>().unwrap());
                let got = tz.next_transition(given).map(|t| t.timestamp());
                assert_eq!(got, expected, "\nTZ: {posix_tz}\ngiven: {given}");
            }
        }
    }

    /// This tests that the size of a time zone is kept at a single word.
    ///
    /// This is important because every jiff::Zoned has a TimeZone inside of
    /// it, and we want to keep its size as small as we can.
    #[test]
    fn time_zone_size() {
        #[cfg(feature = "alloc")]
        {
            let word = core::mem::size_of::<usize>();
            assert_eq!(word, core::mem::size_of::<TimeZone>());
        }
        #[cfg(all(target_pointer_width = "64", not(feature = "alloc")))]
        {
            #[cfg(debug_assertions)]
            {
                assert_eq!(16, core::mem::size_of::<TimeZone>());
            }
            #[cfg(not(debug_assertions))]
            {
                // This asserts the same value as the alloc value above, but
                // it wasn't always this way, which is why it's written out
                // separately. Moreover, in theory, I'd be open to regressing
                // this value if it led to an improvement in alloc-mode. But
                // more likely, it would be nice to decrease this size in
                // non-alloc modes.
                assert_eq!(8, core::mem::size_of::<TimeZone>());
            }
        }
    }

    /// This tests a few other cases for `TimeZone::to_offset` that
    /// probably aren't worth showing in doctest examples.
    #[test]
    fn time_zone_to_offset() {
        let ts = Timestamp::from_second(123456789).unwrap();

        let tz = TimeZone::fixed(offset(-5));
        let info = tz.to_offset_info(ts);
        assert_eq!(info.offset(), offset(-5));
        assert_eq!(info.dst(), Dst::No);
        assert_eq!(info.abbreviation(), "-05");

        let tz = TimeZone::fixed(offset(5));
        let info = tz.to_offset_info(ts);
        assert_eq!(info.offset(), offset(5));
        assert_eq!(info.dst(), Dst::No);
        assert_eq!(info.abbreviation(), "+05");

        let tz = TimeZone::fixed(offset(-12));
        let info = tz.to_offset_info(ts);
        assert_eq!(info.offset(), offset(-12));
        assert_eq!(info.dst(), Dst::No);
        assert_eq!(info.abbreviation(), "-12");

        let tz = TimeZone::fixed(offset(12));
        let info = tz.to_offset_info(ts);
        assert_eq!(info.offset(), offset(12));
        assert_eq!(info.dst(), Dst::No);
        assert_eq!(info.abbreviation(), "+12");

        let tz = TimeZone::fixed(offset(0));
        let info = tz.to_offset_info(ts);
        assert_eq!(info.offset(), offset(0));
        assert_eq!(info.dst(), Dst::No);
        assert_eq!(info.abbreviation(), "UTC");
    }

    /// This tests a few other cases for `TimeZone::to_fixed_offset` that
    /// probably aren't worth showing in doctest examples.
    #[test]
    fn time_zone_to_fixed_offset() {
        let tz = TimeZone::UTC;
        assert_eq!(tz.to_fixed_offset().unwrap(), Offset::UTC);

        let offset = Offset::from_hours(1).unwrap();
        let tz = TimeZone::fixed(offset);
        assert_eq!(tz.to_fixed_offset().unwrap(), offset);

        #[cfg(feature = "alloc")]
        {
            let tz = TimeZone::posix("EST5").unwrap();
            assert!(tz.to_fixed_offset().is_err());

            let test_file = TzifTestFile::get("America/New_York");
            let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
            assert!(tz.to_fixed_offset().is_err());
        }
    }
}
