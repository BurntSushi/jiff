use jiff::fmt::temporal::DateTimeParser;
use sqlx_core::{
    decode::Decode,
    encode::{Encode, IsNull},
    error::BoxDynError,
    types::Type,
};
use sqlx_sqlite::{
    Sqlite, SqliteArgumentValue, SqliteTypeInfo, SqliteValueRef,
};

use crate::{Date, DateTime, Time, Timestamp, ToSqlx};

static PARSER: DateTimeParser = DateTimeParser::new();

impl Type<Sqlite> for Timestamp {
    fn type_info() -> SqliteTypeInfo {
        <str as Type<Sqlite>>::type_info()
    }

    fn compatible(ty: &SqliteTypeInfo) -> bool {
        <str as Type<Sqlite>>::compatible(ty)
            || <f64 as Type<Sqlite>>::compatible(ty)
    }
}

impl Encode<'_, Sqlite> for Timestamp {
    fn encode_by_ref(
        &self,
        buf: &mut Vec<SqliteArgumentValue<'_>>,
    ) -> Result<IsNull, BoxDynError> {
        Encode::<Sqlite>::encode(self.to_jiff().to_string(), buf)
    }
}

impl<'r> Decode<'r, Sqlite> for Timestamp {
    fn decode(value: SqliteValueRef<'r>) -> Result<Self, BoxDynError> {
        // We use a `&str` here because we might need to parse an `f64` from
        // it. std doesn't support parsing `f64` from `&[u8]` AND it seems like
        // we can pass `value` by reference or clone it, so we are limited
        // to exactly one decode. WTF.
        let text = <&str as Decode<Sqlite>>::decode(value)?;
        // If there's a `:` somewhere, then it must be a textual timestamp.
        // Moreover, a textual timestamp requires that a `:` be present
        // somewhere for Jiff to parse it. (SQLite might not strictly require
        // this though...)
        if text.contains(':') {
            let date = PARSER.parse_timestamp(text)?;
            return Ok(date.to_sqlx());
        }
        let julian_days = text.parse::<f64>()?;
        julian_days_to_timestamp(julian_days).map(jiff::Timestamp::to_sqlx)
    }
}

impl Type<Sqlite> for DateTime {
    fn type_info() -> SqliteTypeInfo {
        <str as Type<Sqlite>>::type_info()
    }
}

impl Encode<'_, Sqlite> for DateTime {
    fn encode_by_ref(
        &self,
        buf: &mut Vec<SqliteArgumentValue<'_>>,
    ) -> Result<IsNull, BoxDynError> {
        Encode::<Sqlite>::encode(self.to_jiff().to_string(), buf)
    }
}

impl<'r> Decode<'r, Sqlite> for DateTime {
    fn decode(value: SqliteValueRef<'r>) -> Result<Self, BoxDynError> {
        let text = <&[u8] as Decode<Sqlite>>::decode(value)?;
        let date = PARSER.parse_datetime(text)?;
        Ok(date.to_sqlx())
    }
}

impl Type<Sqlite> for Date {
    fn type_info() -> SqliteTypeInfo {
        <str as Type<Sqlite>>::type_info()
    }
}

impl Encode<'_, Sqlite> for Date {
    fn encode_by_ref(
        &self,
        buf: &mut Vec<SqliteArgumentValue<'_>>,
    ) -> Result<IsNull, BoxDynError> {
        Encode::<Sqlite>::encode(self.to_jiff().to_string(), buf)
    }
}

impl<'r> Decode<'r, Sqlite> for Date {
    fn decode(value: SqliteValueRef<'r>) -> Result<Self, BoxDynError> {
        let text = <&[u8] as Decode<Sqlite>>::decode(value)?;
        let date = PARSER.parse_date(text)?;
        Ok(date.to_sqlx())
    }
}

impl Type<Sqlite> for Time {
    fn type_info() -> SqliteTypeInfo {
        <str as Type<Sqlite>>::type_info()
    }
}

impl Encode<'_, Sqlite> for Time {
    fn encode_by_ref(
        &self,
        buf: &mut Vec<SqliteArgumentValue<'_>>,
    ) -> Result<IsNull, BoxDynError> {
        Encode::<Sqlite>::encode(self.to_jiff().to_string(), buf)
    }
}

impl<'r> Decode<'r, Sqlite> for Time {
    fn decode(value: SqliteValueRef<'r>) -> Result<Self, BoxDynError> {
        static PARSER: DateTimeParser = DateTimeParser::new();

        let text = <&[u8] as Decode<Sqlite>>::decode(value)?;
        let date = PARSER.parse_time(text)?;
        Ok(date.to_sqlx())
    }
}

fn julian_days_to_timestamp(
    days: f64,
) -> Result<jiff::Timestamp, BoxDynError> {
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
