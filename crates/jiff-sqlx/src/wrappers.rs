/// A trait for convenient conversions from Jiff types to SQLx types.
///
/// # Example
///
/// This shows how to convert a [`jiff::Timestamp`] to a [`Timestamp`]:
///
/// ```
/// use jiff_sqlx::ToSqlx;
///
/// let ts: jiff::Timestamp = "2025-02-20T17:00-05".parse()?;
/// let wrapper = ts.to_sqlx();
/// assert_eq!(format!("{wrapper:?}"), "Timestamp(2025-02-20T22:00:00Z)");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub trait ToSqlx {
    /// The wrapper type to convert to.
    type Target;

    /// A conversion method that converts a Jiff type to a SQLx wrapper type.
    fn to_sqlx(self) -> Self::Target;
}

// We currently don't support `Zoned` integration in this wrapper crate. To
// briefly explain why, a `Zoned` is _both_ a timestamp and a time zone. And
// it isn't necessarily a dumb time zone like `-05:00`. It is intended to be a
// real time zone like `America/New_York` or `Australia/Tasmania`.
//
// However, PostgreSQL doesn't really have a primitive type that specifically
// supports "timestamp with time zone." Comically, it does have a `TIMESTAMP
// WITH TIME ZONE` type (from the SQL standard, as I understand it), but it's
// actually just a timestamp. It doesn't store any other data than a timestamp.
// The difference between `TIMESTAMP WITHOUT TIME ZONE` and `TIMESTAMP WITH
// TIME ZONE` is, principally, that fixed offsets are respected in the former
// but completely ignored in the latter. (PostgreSQL's documentation refers
// to fixed offsets as "time zones," which is rather antiquated IMO.) And,
// conventionally, `TIMESTAMP WITHOUT TIME ZONE` is civil (local) time.
//
// So what's the problem? Well, if we try to stuff a `Zoned` into a
// `TIMESTAMP WITH TIME ZONE`, then the *only* thing that actually
// gets stored is a timestamp. No time zone. No offset. Nothing. That
// means the time zone attached to `Zoned` gets dropped. So if you put
// `2025-02-15T17:00-05[America/New_york]` into the database, then you'll
// always get `2025-02-15T22:00+00[UTC]` out. That's a silent dropping of the
// time zone data. I personally think this would be extremely surprising,
// and it could lead to bugs if you assume the time zone is correctly
// round-tripped. (For example, DST safe arithmetic would no longer apply.)
// And indeed, this is a principle design goal of Jiff: `Zoned` values can be
// losslessly transmitted.
//
// An alternative here is to provide a `Zoned` wrapper, but store it in
// a `TEXT` field as an RFC 9557 timestamp. This would permit lossless
// round-tripping. The problem is that this may also violate user expectations
// because a datetime is not stored in a datetime field. Thus, you won't be
// able to use PostgreSQL native functionality to handle it as a date.
//
// So for now, I opted to take the conservative choice and just not provide a
// `Zoned` impl. This way, we can gather use cases and make a better informed
// decision of what to do. Plus, the maintainer of `sqlx` seemed unconvinced
// that a `Zoned` impl that drops time zone data was a problem, so out of
// deference there, I started with this more conservative strategy.
//
// Of course, if you want to store something in `TIMESTAMP WITHOUT TIME ZONE`,
// then you can just use `Timestamp`.
//
// Ref: https://github.com/launchbadge/sqlx/issues/3487#issuecomment-2636542379
/*
#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Zoned(jiff::Zoned);

impl Zoned {
    pub fn to_jiff(&self) -> jiff::Zoned {
        self.0.clone()
    }
}

impl<'a> ToSqlx for &'a jiff::Zoned {
    type Target = Zoned;

    fn to_sqlx(self) -> Zoned {
        Zoned(self.clone())
    }
}

impl From<jiff::Zoned> for Zoned {
    fn from(x: jiff::Zoned) -> Zoned {
        Zoned(x)
    }
}

impl From<Zoned> for jiff::Zoned {
    fn from(x: Zoned) -> jiff::Zoned {
        x.0
    }
}

impl core::ops::Deref for Zoned {
    type Target = jiff::Zoned;

    fn deref(&self) -> &jiff::Zoned {
        &self.0
    }
}
*/

/// A wrapper type for [`jiff::Timestamp`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Timestamp(jiff::Timestamp);

impl Timestamp {
    /// Converts this wrapper to a [`jiff::Timestamp`].
    pub fn to_jiff(self) -> jiff::Timestamp {
        self.0
    }
}

impl ToSqlx for jiff::Timestamp {
    type Target = Timestamp;

    fn to_sqlx(self) -> Timestamp {
        Timestamp(self)
    }
}

impl From<jiff::Timestamp> for Timestamp {
    fn from(x: jiff::Timestamp) -> Timestamp {
        Timestamp(x)
    }
}

impl From<Timestamp> for jiff::Timestamp {
    fn from(x: Timestamp) -> jiff::Timestamp {
        x.0
    }
}

/// A wrapper type for [`jiff::civil::DateTime`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct DateTime(jiff::civil::DateTime);

impl DateTime {
    /// Converts this wrapper to a [`jiff::civil::DateTime`].
    pub fn to_jiff(self) -> jiff::civil::DateTime {
        self.0
    }
}

impl ToSqlx for jiff::civil::DateTime {
    type Target = DateTime;

    fn to_sqlx(self) -> DateTime {
        DateTime(self)
    }
}

impl From<jiff::civil::DateTime> for DateTime {
    fn from(x: jiff::civil::DateTime) -> DateTime {
        DateTime(x)
    }
}

impl From<DateTime> for jiff::civil::DateTime {
    fn from(x: DateTime) -> jiff::civil::DateTime {
        x.0
    }
}

/// A wrapper type for [`jiff::civil::Date`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Date(jiff::civil::Date);

impl Date {
    /// Converts this wrapper to a [`jiff::civil::Date`].
    pub fn to_jiff(self) -> jiff::civil::Date {
        self.0
    }
}

impl ToSqlx for jiff::civil::Date {
    type Target = Date;

    fn to_sqlx(self) -> Date {
        Date(self)
    }
}

impl From<jiff::civil::Date> for Date {
    fn from(x: jiff::civil::Date) -> Date {
        Date(x)
    }
}

impl From<Date> for jiff::civil::Date {
    fn from(x: Date) -> jiff::civil::Date {
        x.0
    }
}

/// A wrapper type for [`jiff::civil::Time`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Time(jiff::civil::Time);

impl Time {
    /// Converts this wrapper to a [`jiff::civil::Time`].
    pub fn to_jiff(self) -> jiff::civil::Time {
        self.0
    }
}

impl ToSqlx for jiff::civil::Time {
    type Target = Time;

    fn to_sqlx(self) -> Time {
        Time(self)
    }
}

impl From<jiff::civil::Time> for Time {
    fn from(x: jiff::civil::Time) -> Time {
        Time(x)
    }
}

impl From<Time> for jiff::civil::Time {
    fn from(x: Time) -> jiff::civil::Time {
        x.0
    }
}

/// A wrapper type for [`jiff::Span`].
///
/// # PostgreSQL: Limited support
///
/// This type _only_ has a [`sqlx_core::decode::Decode`] trait implementation
/// for PostgreSQL. The reason for this is that encoding an arbitrary
/// `Span` into a PostgreSQL interval requires a relative datetime.
/// Therefore, users wanting to store a `Span` will need to explicitly use a
/// [`sqlx_postgres::types::PgInterval`] at least at encoding time.
#[derive(Clone, Copy, Debug)]
pub struct Span(jiff::Span);

impl Span {
    /// Converts this wrapper to a [`jiff::Span`].
    pub fn to_jiff(self) -> jiff::Span {
        self.0
    }
}

impl ToSqlx for jiff::Span {
    type Target = Span;

    fn to_sqlx(self) -> Span {
        Span(self)
    }
}

impl From<jiff::Span> for Span {
    fn from(x: jiff::Span) -> Span {
        Span(x)
    }
}

impl From<Span> for jiff::Span {
    fn from(x: Span) -> jiff::Span {
        x.0
    }
}
