use diesel::{
    deserialize::{self, FromSql, Queryable},
    serialize::{self, IsNull, Output, ToSql},
    sql_types,
    sqlite::{Sqlite, SqliteValue},
};
use jiff::fmt::temporal::DateTimeParser;

use crate::{Date, DateTime, Time, Timestamp, ToDiesel};

static PARSER: DateTimeParser = DateTimeParser::new();

impl Queryable<sql_types::TimestamptzSqlite, Sqlite> for Timestamp {
    type Row = Timestamp;

    fn build(row: Timestamp) -> deserialize::Result<Timestamp> {
        Ok(row)
    }
}

impl ToSql<sql_types::TimestamptzSqlite, Sqlite> for Timestamp {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Sqlite>,
    ) -> serialize::Result {
        out.set_value(self.to_jiff().to_string());
        Ok(IsNull::No)
    }
}

impl FromSql<sql_types::TimestamptzSqlite, Sqlite> for Timestamp {
    fn from_sql(
        value: SqliteValue<'_, '_, '_>,
    ) -> deserialize::Result<Timestamp> {
        // Apparently the Diesel internal implementations get to use
        // `RawValue::parse_string`, which avoids creating a new alloc.
        // But I guess we have to get a full alloc here? Pretty lame if
        // you ask me. Ideally we could get a `&str` and parse straight
        // from that. Jiff can parse from `&[u8]`, but we also use
        // std's float parsing, which only works on `&str`.
        let text: String =
            FromSql::<sql_types::Timestamp, Sqlite>::from_sql(value)?;
        // If there's a `:` somewhere, then it must be a textual timestamp.
        // Moreover, a textual timestamp requires that a `:` be present
        // somewhere for Jiff to parse it. (SQLite might not strictly require
        // this though...)
        if text.contains(':') {
            let date = PARSER.parse_timestamp(text)?;
            return Ok(date.to_diesel());
        }
        let julian_days = text.parse::<f64>()?;
        julian_days_to_timestamp(julian_days).map(jiff::Timestamp::to_diesel)
    }
}

impl Queryable<sql_types::Timestamp, Sqlite> for DateTime {
    type Row = DateTime;

    fn build(row: DateTime) -> deserialize::Result<DateTime> {
        Ok(row)
    }
}

impl ToSql<sql_types::Timestamp, Sqlite> for DateTime {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Sqlite>,
    ) -> serialize::Result {
        out.set_value(self.to_jiff().to_string());
        Ok(IsNull::No)
    }
}

impl FromSql<sql_types::Timestamp, Sqlite> for DateTime {
    fn from_sql(
        value: SqliteValue<'_, '_, '_>,
    ) -> deserialize::Result<DateTime> {
        // Apparently the Diesel internal implementations get to use
        // `RawValue::parse_string`, which avoids creating a new alloc.
        // But I guess we have to get a full alloc here? Pretty lame
        // if you ask me. Ideally we could get a `&[u8]` and parse
        // straight from that (Jiff doesn't need a `&str`).
        let text: String =
            FromSql::<sql_types::Timestamp, Sqlite>::from_sql(value)?;
        let dt = PARSER.parse_datetime(text)?;
        Ok(dt.to_diesel())
    }
}

impl Queryable<sql_types::Date, Sqlite> for Date {
    type Row = Date;

    fn build(row: Date) -> deserialize::Result<Date> {
        Ok(row)
    }
}

impl ToSql<sql_types::Date, Sqlite> for Date {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Sqlite>,
    ) -> serialize::Result {
        out.set_value(self.to_jiff().to_string());
        Ok(IsNull::No)
    }
}

impl FromSql<sql_types::Date, Sqlite> for Date {
    fn from_sql(value: SqliteValue<'_, '_, '_>) -> deserialize::Result<Date> {
        // Apparently the Diesel internal implementations get to use
        // `RawValue::parse_string`, which avoids creating a new alloc.
        // But I guess we have to get a full alloc here? Pretty lame
        // if you ask me. Ideally we could get a `&[u8]` and parse
        // straight from that (Jiff doesn't need a `&str`).
        let text: String =
            FromSql::<sql_types::Date, Sqlite>::from_sql(value)?;
        let date = PARSER.parse_date(text)?;
        Ok(date.to_diesel())
    }
}

impl Queryable<sql_types::Time, Sqlite> for Time {
    type Row = Time;

    fn build(row: Time) -> deserialize::Result<Time> {
        Ok(row)
    }
}

impl ToSql<sql_types::Time, Sqlite> for Time {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Sqlite>,
    ) -> serialize::Result {
        out.set_value(self.to_jiff().to_string());
        Ok(IsNull::No)
    }
}

impl FromSql<sql_types::Time, Sqlite> for Time {
    fn from_sql(value: SqliteValue<'_, '_, '_>) -> deserialize::Result<Time> {
        // Apparently the Diesel internal implementations get to use
        // `RawValue::parse_string`, which avoids creating a new alloc.
        // But I guess we have to get a full alloc here? Pretty lame
        // if you ask me. Ideally we could get a `&[u8]` and parse
        // straight from that (Jiff doesn't need a `&str`).
        let text: String =
            FromSql::<sql_types::Time, Sqlite>::from_sql(value)?;
        let time = PARSER.parse_time(text)?;
        Ok(time.to_diesel())
    }
}

fn julian_days_to_timestamp(
    days: f64,
) -> deserialize::Result<jiff::Timestamp> {
    // The Unix epoch in terms of SQLite julian days:
    //
    //     sqlite> select julianday('1970-01-01T00:00:00Z');
    //     julianday('1970-01-01T00:00:00Z')
    //     ---------------------------------
    //     2440587.5
    static UNIX_EPOCH_AS_JULIAN_DAYS: f64 = 2440587.5;
    // SQLite assumes 24 hours in every day.
    static SECONDS_PER_DAY: f64 = 86400.0;

    let timestamp = (days - UNIX_EPOCH_AS_JULIAN_DAYS) * SECONDS_PER_DAY;
    let sdur = jiff::SignedDuration::try_from_secs_f64(timestamp)?;
    Ok(jiff::Timestamp::from_duration(sdur)?)
}
