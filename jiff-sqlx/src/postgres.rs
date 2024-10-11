use crate::Timestamp;
use jiff::SignedDuration;
use sqlx::encode::IsNull;
use sqlx::error::BoxDynError;
use sqlx::postgres::types::Oid;
use sqlx::postgres::{
    PgArgumentBuffer, PgHasArrayType, PgTypeInfo, PgValueFormat,
};
use sqlx::{Database, Decode, Encode, Postgres, Type};
use std::str::FromStr;

impl Type<Postgres> for Timestamp {
    fn type_info() -> PgTypeInfo {
        // 1184 => PgType::Timestamptz
        PgTypeInfo::with_oid(Oid(1184))
    }
}

impl PgHasArrayType for Timestamp {
    fn array_type_info() -> PgTypeInfo {
        // 1185 => PgType::TimestamptzArray
        PgTypeInfo::with_oid(Oid(1185))
    }
}

impl Encode<'_, Postgres> for Timestamp {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        // TIMESTAMP is encoded as the microseconds since the epoch
        let micros =
            self.0.duration_since(postgres_epoch_timestamp()).as_micros();
        let micros = i64::try_from(micros).map_err(|_| {
            format!("Timestamp {} out of range for Postgres: {micros}", self.0)
        })?;
        Encode::<Postgres>::encode(micros, buf)
    }

    fn size_hint(&self) -> usize {
        size_of::<i64>()
    }
}

impl<'r> Decode<'r, Postgres> for Timestamp {
    fn decode(
        value: <Postgres as Database>::ValueRef<'r>,
    ) -> Result<Self, BoxDynError> {
        Ok(match value.format() {
            PgValueFormat::Binary => {
                // TIMESTAMP is encoded as the microseconds since the epoch
                let us = Decode::<Postgres>::decode(value)?;
                let ts = postgres_epoch_timestamp()
                    .checked_add(SignedDuration::from_micros(us))?;
                Timestamp(ts)
            }
            PgValueFormat::Text => {
                let s = value.as_str()?;
                let ts = jiff::Timestamp::from_str(s)?;
                Timestamp(ts)
            }
        })
    }
}

fn postgres_epoch_timestamp() -> jiff::Timestamp {
    jiff::Timestamp::from_str("2000-01-01T00:00:00Z")
        .expect("2000-01-01T00:00:00Z is a valid timestamp")
}
