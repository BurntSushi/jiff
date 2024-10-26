use crate::{DateTime, ToDateTime};
use jiff::SignedDuration;
use sqlx::encode::IsNull;
use sqlx::error::BoxDynError;
use sqlx::postgres::types::Oid;
use sqlx::postgres::{
    PgArgumentBuffer, PgHasArrayType, PgTypeInfo, PgValueFormat, PgValueRef,
};
use sqlx::{Decode, Encode, Postgres, Type};
use std::str::FromStr;

impl Type<Postgres> for DateTime {
    fn type_info() -> PgTypeInfo {
        // 1114 => PgType::Timestamp
        PgTypeInfo::with_oid(Oid(1114))
    }
}

impl PgHasArrayType for DateTime {
    fn array_type_info() -> PgTypeInfo {
        // 1115 => PgType::TimestampArray
        PgTypeInfo::with_oid(Oid(1115))
    }
}

impl Encode<'_, Postgres> for DateTime {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        let datetime = self.to_jiff();

        // TIMESTAMP is encoded as the microseconds since the epoch
        let micros =
            datetime.duration_since(postgres_epoch_datetime()).as_micros();
        let micros = i64::try_from(micros).map_err(|_| {
            format!("DateTime {datetime} out of range for Postgres: {micros}")
        })?;
        Encode::<Postgres>::encode(micros, buf)
    }

    fn size_hint(&self) -> usize {
        size_of::<i64>()
    }
}

impl<'r> Decode<'r, Postgres> for DateTime {
    fn decode(value: PgValueRef<'r>) -> Result<Self, BoxDynError> {
        Ok(match value.format() {
            PgValueFormat::Binary => {
                // TIMESTAMP is encoded as the microseconds since the epoch
                let us = Decode::<Postgres>::decode(value)?;
                let datetime = postgres_epoch_datetime()
                    .checked_add(SignedDuration::from_micros(us))?;
                datetime.to_sqlx()
            }
            PgValueFormat::Text => {
                let s = value.as_str()?;
                let datetime = jiff::civil::DateTime::from_str(s)?;
                datetime.to_sqlx()
            }
        })
    }
}

const fn postgres_epoch_datetime() -> jiff::civil::DateTime {
    jiff::civil::DateTime::constant(2000, 1, 1, 0, 0, 0, 0)
}
