use crate::{civil, Timestamp};
use sqlx_traits::{
    unexpected_sql_value, BoxDynError, HasSqlType, SqlDate, SqlDateTime,
    SqlDecode, SqlEncode, SqlTime, SqlTimestamp, SqlType, SqlValue,
};

impl HasSqlType for Timestamp {
    const SQL_TYPE: SqlType = SqlType::TimestampTz;
}

impl SqlEncode for Timestamp {
    fn encode_sql(&self) -> Result<SqlValue, BoxDynError> {
        Ok(SqlValue::TimestampTz(SqlTimestamp::from_unix_nanoseconds(
            self.as_nanosecond(),
        )))
    }
}

impl SqlDecode for Timestamp {
    fn decode_sql(value: SqlValue) -> Result<Self, BoxDynError> {
        match value {
            SqlValue::TimestampTz(timestamp) => {
                Ok(Timestamp::from_nanosecond(timestamp.unix_nanoseconds())?)
            }
            SqlValue::Text(text) => Ok(text.parse()?),
            value => {
                Err(unexpected_sql_value("timestamp with time zone", &value))
            }
        }
    }
}

impl HasSqlType for civil::DateTime {
    const SQL_TYPE: SqlType = SqlType::Timestamp;
}

impl SqlEncode for civil::DateTime {
    fn encode_sql(&self) -> Result<SqlValue, BoxDynError> {
        Ok(SqlValue::Timestamp(SqlDateTime::new(
            encode_date(self.date()),
            encode_time(self.time()),
        )))
    }
}

impl SqlDecode for civil::DateTime {
    fn decode_sql(value: SqlValue) -> Result<Self, BoxDynError> {
        match value {
            SqlValue::Timestamp(datetime) => decode_datetime(datetime),
            SqlValue::Text(text) => Ok(text.parse()?),
            value => Err(unexpected_sql_value("timestamp", &value)),
        }
    }
}

impl HasSqlType for civil::Date {
    const SQL_TYPE: SqlType = SqlType::Date;
}

impl SqlEncode for civil::Date {
    fn encode_sql(&self) -> Result<SqlValue, BoxDynError> {
        Ok(SqlValue::Date(encode_date(*self)))
    }
}

impl SqlDecode for civil::Date {
    fn decode_sql(value: SqlValue) -> Result<Self, BoxDynError> {
        match value {
            SqlValue::Date(date) => decode_date(date),
            SqlValue::Text(text) => Ok(text.parse()?),
            value => Err(unexpected_sql_value("date", &value)),
        }
    }
}

impl HasSqlType for civil::Time {
    const SQL_TYPE: SqlType = SqlType::Time;
}

impl SqlEncode for civil::Time {
    fn encode_sql(&self) -> Result<SqlValue, BoxDynError> {
        Ok(SqlValue::Time(encode_time(*self)))
    }
}

impl SqlDecode for civil::Time {
    fn decode_sql(value: SqlValue) -> Result<Self, BoxDynError> {
        match value {
            SqlValue::Time(time) => decode_time(time),
            SqlValue::Text(text) => Ok(text.parse()?),
            value => Err(unexpected_sql_value("time", &value)),
        }
    }
}

fn encode_date(date: civil::Date) -> SqlDate {
    SqlDate::from_ymd_unchecked(
        i32::from(date.year()),
        u8::try_from(date.month()).expect("Jiff month is in range 1..=12"),
        u8::try_from(date.day()).expect("Jiff day is in range 1..=31"),
    )
}

fn decode_date(date: SqlDate) -> Result<civil::Date, BoxDynError> {
    Ok(civil::Date::new(
        i16::try_from(date.year)?,
        i8::try_from(date.month)?,
        i8::try_from(date.day)?,
    )?)
}

fn encode_time(time: civil::Time) -> SqlTime {
    SqlTime::from_hms_nano_unchecked(
        u8::try_from(time.hour()).expect("Jiff hour is in range 0..=23"),
        u8::try_from(time.minute()).expect("Jiff minute is in range 0..=59"),
        u8::try_from(time.second()).expect("Jiff second is in range 0..=59"),
        u32::try_from(time.subsec_nanosecond())
            .expect("Jiff subsecond nanosecond is in range 0..=999999999"),
    )
}

fn decode_time(time: SqlTime) -> Result<civil::Time, BoxDynError> {
    Ok(civil::Time::new(
        i8::try_from(time.hour)?,
        i8::try_from(time.minute)?,
        i8::try_from(time.second)?,
        i32::try_from(time.nanosecond)?,
    )?)
}

fn decode_datetime(
    datetime: SqlDateTime,
) -> Result<civil::DateTime, BoxDynError> {
    let date = datetime.date;
    let time = datetime.time;

    Ok(civil::DateTime::new(
        i16::try_from(date.year)?,
        i8::try_from(date.month)?,
        i8::try_from(date.day)?,
        i8::try_from(time.hour)?,
        i8::try_from(time.minute)?,
        i8::try_from(time.second)?,
        i32::try_from(time.nanosecond)?,
    )?)
}
