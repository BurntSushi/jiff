/// A trait for convenient conversions from Jiff types to Diesel types.
///
/// # Example
///
/// This shows how to convert a [`jiff::Timestamp`] to a [`Timestamp`]:
///
/// ```
/// use jiff_diesel::ToDiesel;
///
/// let ts: jiff::Timestamp = "2025-02-20T17:00-05".parse()?;
/// let wrapper = ts.to_diesel();
/// assert_eq!(format!("{wrapper:?}"), "Timestamp(2025-02-20T22:00:00Z)");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub trait ToDiesel {
    /// The wrapper type to convert to.
    type Target;

    /// A conversion method that converts a Jiff type to a Diesel wrapper type.
    fn to_diesel(self) -> Self::Target;
}

/// A wrapper type for [`jiff::Timestamp`].
#[derive(
    Clone,
    Copy,
    Debug,
    Eq,
    Hash,
    PartialEq,
    PartialOrd,
    Ord,
    diesel::deserialize::FromSqlRow,
)]
#[cfg_attr(
    any(feature = "mysql", feature = "postgres", feature = "sqlite"),
    derive(diesel::expression::AsExpression)
)]
#[cfg_attr(feature = "mysql", diesel(sql_type = diesel::sql_types::Datetime))]
#[cfg_attr(feature = "postgres", diesel(sql_type = diesel::sql_types::Timestamptz))]
#[cfg_attr(feature = "sqlite", diesel(sql_type = diesel::sql_types::TimestamptzSqlite))]
pub struct Timestamp(jiff::Timestamp);

impl Timestamp {
    /// Converts this wrapper to a [`jiff::Timestamp`].
    pub fn to_jiff(self) -> jiff::Timestamp {
        self.0
    }
}

impl ToDiesel for jiff::Timestamp {
    type Target = Timestamp;

    fn to_diesel(self) -> Timestamp {
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
#[derive(
    Clone,
    Copy,
    Debug,
    Eq,
    Hash,
    PartialEq,
    PartialOrd,
    Ord,
    diesel::expression::AsExpression,
    diesel::deserialize::FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Timestamp)]
pub struct DateTime(jiff::civil::DateTime);

impl DateTime {
    /// Converts this wrapper to a [`jiff::civil::DateTime`].
    pub fn to_jiff(self) -> jiff::civil::DateTime {
        self.0
    }
}

impl ToDiesel for jiff::civil::DateTime {
    type Target = DateTime;

    fn to_diesel(self) -> DateTime {
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
#[derive(
    Clone,
    Copy,
    Debug,
    Eq,
    Hash,
    PartialEq,
    PartialOrd,
    Ord,
    diesel::expression::AsExpression,
    diesel::deserialize::FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Date)]
pub struct Date(jiff::civil::Date);

impl Date {
    /// Converts this wrapper to a [`jiff::civil::Date`].
    pub fn to_jiff(self) -> jiff::civil::Date {
        self.0
    }
}

impl ToDiesel for jiff::civil::Date {
    type Target = Date;

    fn to_diesel(self) -> Date {
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
#[derive(
    Clone,
    Copy,
    Debug,
    Eq,
    Hash,
    PartialEq,
    PartialOrd,
    Ord,
    diesel::expression::AsExpression,
    diesel::deserialize::FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Time)]
pub struct Time(jiff::civil::Time);

impl Time {
    /// Converts this wrapper to a [`jiff::civil::Time`].
    pub fn to_jiff(self) -> jiff::civil::Time {
        self.0
    }
}

impl ToDiesel for jiff::civil::Time {
    type Target = Time;

    fn to_diesel(self) -> Time {
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
/// This type _only_ has a [`diesel::deserialize::FromSql`] trait implementation
/// for PostgreSQL. The reason for this is that encoding an arbitrary
/// `Span` into a PostgreSQL interval requires a relative datetime.
/// Therefore, users wanting to store a `Span` will need to explicitly use a
/// [`diesel::pg::data_types::PgInterval`] at least at encoding time.
#[derive(Clone, Copy, Debug, diesel::deserialize::FromSqlRow)]
pub struct Span(jiff::Span);

impl Span {
    /// Converts this wrapper to a [`jiff::Span`].
    pub fn to_jiff(self) -> jiff::Span {
        self.0
    }
}

impl ToDiesel for jiff::Span {
    type Target = Span;

    fn to_diesel(self) -> Span {
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
