use jiff::{civil, tz};
use sqlx::postgres::{
    types::{Oid, PgInterval},
    PgArgumentBuffer, PgHasArrayType, PgTypeInfo, PgValueFormat, PgValueRef,
    Postgres,
};
use sqlx::{
    decode::Decode,
    encode::{Encode, IsNull},
    error::BoxDynError,
    types::Type,
};

use crate::{Date, DateTime, Span, Time, Timestamp, ToSqlx};

/// Apparently the actual format of values on the wire is not
/// a documented guarantee of PostgreSQL.[1] Instead, I just `sqlx`'s
/// source code for `chrono` to figure out what the type of the source
/// data is.
///
/// [1]: https://www.postgresql.org/docs/current/protocol-overview.html#PROTOCOL-FORMAT-CODES
static POSTGRES_EPOCH_DATE: civil::Date = civil::date(2000, 1, 1);
static POSTGRES_EPOCH_DATETIME: civil::DateTime =
    civil::date(2000, 1, 1).at(0, 0, 0, 0);
static POSTGRES_EPOCH_TIMESTAMP: jiff::Timestamp =
    jiff::Timestamp::constant(946684800, 0);
static MIDNIGHT: civil::Time = civil::Time::midnight();
static UTC: tz::TimeZone = tz::TimeZone::UTC;

// We currently don't support `Zoned` integration in this wrapper crate.
// See comments in `src/wrappers.rs`.
//
// Ref: https://github.com/launchbadge/sqlx/issues/3487#issuecomment-2636542379
/*
impl Type<Postgres> for Zoned {
    fn type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L473
        PgTypeInfo::with_oid(Oid(25))
    }
}

impl PgHasArrayType for Zoned {
    fn array_type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L503
        PgTypeInfo::with_oid(Oid(1009))
    }
}

impl Encode<'_, Postgres> for Zoned {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        // There's no PostgreSQL data type for storing timestamps with time
        // zones (despite the existence of a `TIMESTAMP WITH TIME ZONE` type,
        // which is in fact just a timestamp), so we just use strings and
        // RFC 9557 timestamps.
        Encode::<Postgres>::encode(self.to_jiff().to_string(), buf)
    }
}

impl<'r> Decode<'r, Postgres> for Zoned {
    fn decode(value: PgValueRef<'r>) -> Result<Zoned, BoxDynError> {
        Ok(value.as_str()?.parse::<jiff::Zoned>()?.to_sqlx())
    }
}
*/

impl Type<Postgres> for Timestamp {
    fn type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L525
        PgTypeInfo::with_oid(Oid(1184))
    }
}

impl PgHasArrayType for Timestamp {
    fn array_type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L526
        PgTypeInfo::with_oid(Oid(1185))
    }
}

impl Encode<'_, Postgres> for Timestamp {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        // I guess the encoding here, based on sqlx, is the same as civil time.
        // But the assumption is that the civil time is in UTC.
        let dt = UTC.to_datetime(self.to_jiff()).to_sqlx();
        Encode::<Postgres>::encode(dt, buf)
    }
}

impl<'r> Decode<'r, Postgres> for Timestamp {
    fn decode(value: PgValueRef<'r>) -> Result<Timestamp, BoxDynError> {
        match value.format() {
            PgValueFormat::Binary => {
                // The encoding is the number of *microseconds* since
                // POSTGRES_EPOCH_DATETIME.
                let micros: i64 = Decode::<Postgres>::decode(value)?;
                let micros = jiff::SignedDuration::from_micros(micros);
                Ok(POSTGRES_EPOCH_TIMESTAMP.checked_add(micros)?.to_sqlx())
            }
            PgValueFormat::Text => {
                // The encoding is just ISO 8601 I think? Close to RFC 3339,
                // but not quite I think. Either way, Jiff's default parser
                // will handle it.
                //
                // This does swallow the offset (but respects it correctl so
                // that the proper instant is parsed). If one needs the offset,
                // we'll need to expose a new `TimestampWithOffset` wrapper
                // type. Please file an issue. (But this seems fraught since
                // it's only available in text mode I guess? WTF.)
                Ok(value.as_str()?.parse::<jiff::Timestamp>()?.to_sqlx())
            }
        }
    }
}

impl Type<Postgres> for DateTime {
    fn type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L521
        // Note that we use the oid for a type called "timestamp," even
        // though this is clearly not a timestamp. It's a civil datetime.
        // But that's PostgreSQL (or I guess just SQL) for you.
        PgTypeInfo::with_oid(Oid(1114))
    }
}

impl PgHasArrayType for DateTime {
    fn array_type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L522
        PgTypeInfo::with_oid(Oid(1115))
    }
}

impl Encode<'_, Postgres> for DateTime {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        // The encoding is the number of *microseconds* since
        // POSTGRES_EPOCH_DATETIME.
        let micros =
            self.to_jiff().duration_since(POSTGRES_EPOCH_DATETIME).as_micros();
        // OK because the maximum duration between two Jiff civil datetimes
        // is 631,107,417,599,999,999, which is less than i64::MAX.
        let micros = i64::try_from(micros).unwrap();
        Encode::<Postgres>::encode(micros, buf)
    }
}

impl<'r> Decode<'r, Postgres> for DateTime {
    fn decode(value: PgValueRef<'r>) -> Result<DateTime, BoxDynError> {
        match value.format() {
            PgValueFormat::Binary => {
                // The encoding is the number of *microseconds* since
                // POSTGRES_EPOCH_DATETIME.
                let micros: i64 = Decode::<Postgres>::decode(value)?;
                let micros = jiff::SignedDuration::from_micros(micros);
                Ok(POSTGRES_EPOCH_DATETIME.checked_add(micros)?.to_sqlx())
            }
            PgValueFormat::Text => {
                // The encoding is just ISO 8601 I think?
                // The `chrono` implementation in `sqlx` does a dance with
                // trying to parse offsets, but Jiff's `civil::DateTime`
                // parser will handle that automatically.
                Ok(value.as_str()?.parse::<civil::DateTime>()?.to_sqlx())
            }
        }
    }
}

impl Type<Postgres> for Date {
    fn type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L519
        PgTypeInfo::with_oid(Oid(1082))
    }
}

impl PgHasArrayType for Date {
    fn array_type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L523
        PgTypeInfo::with_oid(Oid(1182))
    }
}

impl Encode<'_, Postgres> for Date {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        // The encoding is the number of days since
        // POSTGRES_EPOCH_DATE.
        let days = (self.to_jiff() - POSTGRES_EPOCH_DATE).get_days();
        Encode::<Postgres>::encode(days, buf)
    }
}

impl<'r> Decode<'r, Postgres> for Date {
    fn decode(value: PgValueRef<'r>) -> Result<Date, BoxDynError> {
        match value.format() {
            PgValueFormat::Binary => {
                // The encoding is the number of days since
                // POSTGRES_EPOCH_DATE.
                let days: i32 = Decode::<Postgres>::decode(value)?;
                let span = jiff::Span::new().try_days(days)?;
                Ok(POSTGRES_EPOCH_DATE.checked_add(span)?.to_sqlx())
            }
            PgValueFormat::Text => {
                // The encoding is just ISO 8601.
                Ok(value.as_str()?.parse::<civil::Date>()?.to_sqlx())
            }
        }
    }
}

impl Type<Postgres> for Time {
    fn type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L520
        PgTypeInfo::with_oid(Oid(1083))
    }
}

impl PgHasArrayType for Time {
    fn array_type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L524
        PgTypeInfo::with_oid(Oid(1183))
    }
}

impl Encode<'_, Postgres> for Time {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        // The encoding is the number of *microseconds* since midnight.
        let micros = self.to_jiff().duration_since(MIDNIGHT).as_micros();
        // OK since the max number of microseconds here is
        // 86399999999, which always fits into an `i64`.
        let micros = i64::try_from(micros).unwrap();
        Encode::<Postgres>::encode(micros, buf)
    }
}

impl<'r> Decode<'r, Postgres> for Time {
    fn decode(value: PgValueRef<'r>) -> Result<Self, BoxDynError> {
        match value.format() {
            PgValueFormat::Binary => {
                // The encoding is the number of *microseconds* since midnight.
                let micros: i64 = Decode::<Postgres>::decode(value)?;
                let micros = jiff::SignedDuration::from_micros(micros);
                Ok(MIDNIGHT.checked_add(micros)?.to_sqlx())
            }
            PgValueFormat::Text => {
                // The encoding is just ISO 8601.
                Ok(value.as_str()?.parse::<civil::Time>()?.to_sqlx())
            }
        }
    }
}

impl Type<Postgres> for Span {
    fn type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L527
        PgTypeInfo::with_oid(Oid(1186))
    }
}

impl PgHasArrayType for Span {
    fn array_type_info() -> PgTypeInfo {
        // https://github.com/launchbadge/sqlx/blob/65229f7ff91ecd38be7c10fb61ff3e05bedabe87/sqlx-postgres/src/type_info.rs#L528
        PgTypeInfo::with_oid(Oid(1187))
    }
}

impl<'r> Decode<'r, Postgres> for Span {
    fn decode(value: PgValueRef<'r>) -> Result<Self, BoxDynError> {
        let interval: PgInterval = Decode::<Postgres>::decode(value)?;
        let span = jiff::Span::new()
            .try_months(interval.months)?
            .try_days(interval.days)?
            .try_microseconds(interval.microseconds)?;
        Ok(span.to_sqlx())
    }
}
