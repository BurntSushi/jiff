use diesel::{
    deserialize::{self, FromSql},
    pg::{
        data_types::{PgDate, PgInterval, PgTime, PgTimestamp},
        Pg, PgValue,
    },
    serialize::{self, Output, ToSql},
    sql_types,
};
use jiff::{civil, tz};

use crate::{Date, DateTime, Span, Time, Timestamp, ToDiesel};

/// Apparently the actual format of values on the wire is not
/// a documented guarantee of PostgreSQL.[1] Instead, I just `sqlx`'s
/// source code for `chrono` to figure out what the type of the source
/// data is. (And this is fine for Diesel integration too.)
///
/// [1]: https://www.postgresql.org/docs/current/protocol-overview.html#PROTOCOL-FORMAT-CODES
static POSTGRES_EPOCH_DATE: civil::Date = civil::date(2000, 1, 1);
static POSTGRES_EPOCH_DATETIME: civil::DateTime =
    civil::date(2000, 1, 1).at(0, 0, 0, 0);
static POSTGRES_EPOCH_TIMESTAMP: i64 = 946684800;
static MIDNIGHT: civil::Time = civil::Time::midnight();
static UTC: tz::TimeZone = tz::TimeZone::UTC;

impl ToSql<sql_types::Timestamptz, Pg> for Timestamp {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Pg>,
    ) -> serialize::Result {
        // I guess the encoding here, based on Diesel, is the same as civil
        // time. But the assumption is that the civil time is in UTC.
        let dt = UTC.to_datetime(self.to_jiff()).to_diesel();
        ToSql::<sql_types::Timestamp, Pg>::to_sql(&dt, &mut out.reborrow())
    }
}

impl FromSql<sql_types::Timestamp, Pg> for Timestamp {
    fn from_sql(bytes: PgValue<'_>) -> deserialize::Result<Timestamp> {
        // The encoding is the number of *microseconds* since
        // POSTGRES_EPOCH_DATETIME.
        let PgTimestamp(micros) =
            FromSql::<sql_types::Timestamp, Pg>::from_sql(bytes)?;
        let micros = jiff::SignedDuration::from_micros(micros);
        // OK because the timestamp is known to be valid and in range.
        let epoch =
            jiff::Timestamp::from_second(POSTGRES_EPOCH_TIMESTAMP).unwrap();
        Ok(epoch.checked_add(micros)?.to_diesel())
    }
}

impl FromSql<sql_types::Timestamptz, Pg> for Timestamp {
    fn from_sql(bytes: PgValue<'_>) -> deserialize::Result<Timestamp> {
        // The encoding is the number of *microseconds* since
        // POSTGRES_EPOCH_DATETIME.
        let PgTimestamp(micros) =
            FromSql::<sql_types::Timestamptz, Pg>::from_sql(bytes)?;
        let micros = jiff::SignedDuration::from_micros(micros);
        // OK because the timestamp is known to be valid and in range.
        let epoch =
            jiff::Timestamp::from_second(POSTGRES_EPOCH_TIMESTAMP).unwrap();
        Ok(epoch.checked_add(micros)?.to_diesel())
    }
}

impl ToSql<sql_types::Timestamp, Pg> for DateTime {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Pg>,
    ) -> serialize::Result {
        // The encoding is the number of *microseconds* since
        // POSTGRES_EPOCH_DATETIME.
        let micros =
            self.to_jiff().duration_since(POSTGRES_EPOCH_DATETIME).as_micros();
        // OK because the maximum duration between two Jiff civil datetimes
        // is 631,107,417,599,999,999, which is less than i64::MAX.
        let micros = i64::try_from(micros).unwrap();
        ToSql::<sql_types::Timestamp, Pg>::to_sql(
            &PgTimestamp(micros),
            &mut out.reborrow(),
        )
    }
}

impl FromSql<sql_types::Timestamp, Pg> for DateTime {
    fn from_sql(bytes: PgValue<'_>) -> deserialize::Result<DateTime> {
        // The encoding is the number of *microseconds* since
        // POSTGRES_EPOCH_DATETIME.
        let PgTimestamp(micros) =
            FromSql::<sql_types::Timestamp, Pg>::from_sql(bytes)?;
        let micros = jiff::SignedDuration::from_micros(micros);
        Ok(POSTGRES_EPOCH_DATETIME.checked_add(micros)?.to_diesel())
    }
}

impl ToSql<sql_types::Date, Pg> for Date {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Pg>,
    ) -> serialize::Result {
        // The encoding is the number of days since
        // POSTGRES_EPOCH_DATE.
        let days = (self.to_jiff() - POSTGRES_EPOCH_DATE).get_days();
        ToSql::<sql_types::Date, Pg>::to_sql(
            &PgDate(days),
            &mut out.reborrow(),
        )
    }
}

impl FromSql<sql_types::Date, Pg> for Date {
    fn from_sql(bytes: PgValue<'_>) -> deserialize::Result<Date> {
        let PgDate(days) = FromSql::<sql_types::Date, Pg>::from_sql(bytes)?;
        let span = jiff::Span::new().try_days(days)?;
        Ok(POSTGRES_EPOCH_DATE.checked_add(span)?.to_diesel())
    }
}

impl ToSql<sql_types::Time, Pg> for Time {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Pg>,
    ) -> serialize::Result {
        // The encoding is the number of *microseconds* since midnight.
        let micros = self.to_jiff().duration_since(MIDNIGHT).as_micros();
        // OK since the max number of microseconds here is
        // 86399999999, which always fits into an `i64`.
        let micros = i64::try_from(micros).unwrap();
        ToSql::<sql_types::Time, Pg>::to_sql(
            &PgTime(micros),
            &mut out.reborrow(),
        )
    }
}

impl FromSql<sql_types::Time, Pg> for Time {
    fn from_sql(bytes: PgValue<'_>) -> deserialize::Result<Time> {
        // The encoding is the number of *microseconds* since midnight.
        let PgTime(micros) = FromSql::<sql_types::Time, Pg>::from_sql(bytes)?;
        let micros = jiff::SignedDuration::from_micros(micros);
        Ok(MIDNIGHT.checked_add(micros)?.to_diesel())
    }
}

impl FromSql<sql_types::Interval, Pg> for Span {
    fn from_sql(bytes: PgValue<'_>) -> deserialize::Result<Span> {
        let interval: PgInterval =
            FromSql::<sql_types::Interval, Pg>::from_sql(bytes)?;
        let span = jiff::Span::new()
            .try_months(interval.months)?
            .try_days(interval.days)?
            .try_microseconds(interval.microseconds)?;
        Ok(span.to_diesel())
    }
}
