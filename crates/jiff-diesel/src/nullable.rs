use diesel::{
    backend::Backend,
    deserialize::FromSql,
    serialize::{Output, ToSql},
};

use crate::ToDiesel;

/// A wrapper type for `Option<jiff::Timestamp>`.
///
/// This can be used when deriving [`diesel::deserialize::Queryable`]
/// or [`diesel::deserialize::QueryableByName`] trait implementations.
#[derive(Clone, Copy, Debug, diesel::deserialize::FromSqlRow)]
pub struct NullableTimestamp(Option<crate::Timestamp>);

impl NullableTimestamp {
    /// Converts this wrapper to an `Option<jiff::Timestamp>`.
    pub fn to_jiff(self) -> Option<jiff::Timestamp> {
        self.into()
    }
}

impl ToDiesel for Option<jiff::Timestamp> {
    type Target = NullableTimestamp;

    fn to_diesel(self) -> NullableTimestamp {
        NullableTimestamp(self.map(ToDiesel::to_diesel))
    }
}

impl From<Option<jiff::Timestamp>> for NullableTimestamp {
    fn from(x: Option<jiff::Timestamp>) -> Self {
        Self(x.map(Into::into))
    }
}

impl From<NullableTimestamp> for Option<jiff::Timestamp> {
    fn from(x: NullableTimestamp) -> Self {
        x.0.map(Into::into)
    }
}

impl<DB: Backend, ST> ToSql<ST, DB> for NullableTimestamp
where
    Option<crate::Timestamp>: ToSql<ST, DB>,
{
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, DB>,
    ) -> diesel::serialize::Result {
        self.0.to_sql(out)
    }
}

impl<DB: Backend, ST> FromSql<ST, DB> for NullableTimestamp
where
    Option<crate::Timestamp>: FromSql<ST, DB>,
{
    fn from_sql(
        bytes: <DB as Backend>::RawValue<'_>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_sql(bytes).map(NullableTimestamp)
    }

    fn from_nullable_sql(
        bytes: Option<<DB as Backend>::RawValue<'_>>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_nullable_sql(bytes).map(NullableTimestamp)
    }
}

/// A wrapper type for `Option<jiff::civil::DateTime>`.
///
/// This can be used when deriving [`diesel::deserialize::Queryable`]
/// or [`diesel::deserialize::QueryableByName`] trait implementations.
#[derive(Clone, Copy, Debug, diesel::deserialize::FromSqlRow)]
pub struct NullableDateTime(Option<crate::DateTime>);

impl NullableDateTime {
    /// Converts this wrapper to an `Option<jiff::civil::DateTime>`.
    pub fn to_jiff(self) -> Option<jiff::civil::DateTime> {
        self.into()
    }
}

impl ToDiesel for Option<jiff::civil::DateTime> {
    type Target = NullableDateTime;

    fn to_diesel(self) -> NullableDateTime {
        NullableDateTime(self.map(ToDiesel::to_diesel))
    }
}

impl From<Option<jiff::civil::DateTime>> for NullableDateTime {
    fn from(x: Option<jiff::civil::DateTime>) -> Self {
        Self(x.map(Into::into))
    }
}

impl From<NullableDateTime> for Option<jiff::civil::DateTime> {
    fn from(x: NullableDateTime) -> Self {
        x.0.map(Into::into)
    }
}

impl<DB: Backend, ST> ToSql<ST, DB> for NullableDateTime
where
    Option<crate::DateTime>: ToSql<ST, DB>,
{
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, DB>,
    ) -> diesel::serialize::Result {
        self.0.to_sql(out)
    }
}

impl<DB: Backend, ST> FromSql<ST, DB> for NullableDateTime
where
    Option<crate::DateTime>: FromSql<ST, DB>,
{
    fn from_sql(
        bytes: <DB as Backend>::RawValue<'_>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_sql(bytes).map(NullableDateTime)
    }

    fn from_nullable_sql(
        bytes: Option<<DB as Backend>::RawValue<'_>>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_nullable_sql(bytes).map(NullableDateTime)
    }
}

/// A wrapper type for `Option<jiff::civil::Date>`.
///
/// This can be used when deriving [`diesel::deserialize::Queryable`]
/// or [`diesel::deserialize::QueryableByName`] trait implementations.
#[derive(Clone, Copy, Debug, diesel::deserialize::FromSqlRow)]
pub struct NullableDate(Option<crate::Date>);

impl NullableDate {
    /// Converts this wrapper to an `Option<jiff::civil::Date>`.
    pub fn to_jiff(self) -> Option<jiff::civil::Date> {
        self.into()
    }
}

impl ToDiesel for Option<jiff::civil::Date> {
    type Target = NullableDate;

    fn to_diesel(self) -> NullableDate {
        NullableDate(self.map(ToDiesel::to_diesel))
    }
}

impl From<Option<jiff::civil::Date>> for NullableDate {
    fn from(x: Option<jiff::civil::Date>) -> Self {
        Self(x.map(Into::into))
    }
}

impl From<NullableDate> for Option<jiff::civil::Date> {
    fn from(x: NullableDate) -> Self {
        x.0.map(Into::into)
    }
}

impl<DB: Backend, ST> ToSql<ST, DB> for NullableDate
where
    Option<crate::Date>: ToSql<ST, DB>,
{
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, DB>,
    ) -> diesel::serialize::Result {
        self.0.to_sql(out)
    }
}

impl<DB: Backend, ST> FromSql<ST, DB> for NullableDate
where
    Option<crate::Date>: FromSql<ST, DB>,
{
    fn from_sql(
        bytes: <DB as Backend>::RawValue<'_>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_sql(bytes).map(NullableDate)
    }

    fn from_nullable_sql(
        bytes: Option<<DB as Backend>::RawValue<'_>>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_nullable_sql(bytes).map(NullableDate)
    }
}

/// A wrapper type for `Option<jiff::civil::Time>`.
///
/// This can be used when deriving [`diesel::deserialize::Queryable`]
/// or [`diesel::deserialize::QueryableByName`] trait implementations.
#[derive(Clone, Copy, Debug, diesel::deserialize::FromSqlRow)]
pub struct NullableTime(Option<crate::Time>);

impl NullableTime {
    /// Converts this wrapper to an `Option<jiff::civil::Time>`.
    pub fn to_jiff(self) -> Option<jiff::civil::Time> {
        self.into()
    }
}

impl ToDiesel for Option<jiff::civil::Time> {
    type Target = NullableTime;

    fn to_diesel(self) -> NullableTime {
        NullableTime(self.map(ToDiesel::to_diesel))
    }
}

impl From<Option<jiff::civil::Time>> for NullableTime {
    fn from(x: Option<jiff::civil::Time>) -> Self {
        Self(x.map(Into::into))
    }
}

impl From<NullableTime> for Option<jiff::civil::Time> {
    fn from(x: NullableTime) -> Self {
        x.0.map(Into::into)
    }
}

impl<DB: Backend, ST> ToSql<ST, DB> for NullableTime
where
    Option<crate::Time>: ToSql<ST, DB>,
{
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, DB>,
    ) -> diesel::serialize::Result {
        self.0.to_sql(out)
    }
}

impl<DB: Backend, ST> FromSql<ST, DB> for NullableTime
where
    Option<crate::Time>: FromSql<ST, DB>,
{
    fn from_sql(
        bytes: <DB as Backend>::RawValue<'_>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_sql(bytes).map(NullableTime)
    }

    fn from_nullable_sql(
        bytes: Option<<DB as Backend>::RawValue<'_>>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_nullable_sql(bytes).map(NullableTime)
    }
}

/// A wrapper type for `Option<jiff::Span>`.
///
/// This can be used when deriving [`diesel::deserialize::Queryable`]
/// or [`diesel::deserialize::QueryableByName`] trait implementations.
#[derive(Clone, Copy, Debug, diesel::deserialize::FromSqlRow)]
pub struct NullableSpan(Option<crate::Span>);

impl NullableSpan {
    /// Converts this wrapper to an `Option<jiff::Span>`.
    pub fn to_jiff(self) -> Option<jiff::Span> {
        self.into()
    }
}

impl ToDiesel for Option<jiff::Span> {
    type Target = NullableSpan;

    fn to_diesel(self) -> NullableSpan {
        NullableSpan(self.map(ToDiesel::to_diesel))
    }
}

impl From<Option<jiff::Span>> for NullableSpan {
    fn from(x: Option<jiff::Span>) -> Self {
        Self(x.map(Into::into))
    }
}

impl From<NullableSpan> for Option<jiff::Span> {
    fn from(x: NullableSpan) -> Self {
        x.0.map(Into::into)
    }
}

impl<DB: Backend, ST> ToSql<ST, DB> for NullableSpan
where
    Option<crate::Span>: ToSql<ST, DB>,
{
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, DB>,
    ) -> diesel::serialize::Result {
        self.0.to_sql(out)
    }
}

impl<DB: Backend, ST> FromSql<ST, DB> for NullableSpan
where
    Option<crate::Span>: FromSql<ST, DB>,
{
    fn from_sql(
        bytes: <DB as Backend>::RawValue<'_>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_sql(bytes).map(NullableSpan)
    }

    fn from_nullable_sql(
        bytes: Option<<DB as Backend>::RawValue<'_>>,
    ) -> diesel::deserialize::Result<Self> {
        FromSql::from_nullable_sql(bytes).map(NullableSpan)
    }
}
