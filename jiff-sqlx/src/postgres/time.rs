use crate::{Time, ToTime};
use jiff::SignedDuration;
use sqlx::encode::IsNull;
use sqlx::error::BoxDynError;
use sqlx::postgres::types::Oid;
use sqlx::postgres::{
    PgArgumentBuffer, PgHasArrayType, PgTypeInfo, PgValueFormat, PgValueRef,
};
use sqlx::{Decode, Encode, Postgres, Type};

impl Type<Postgres> for Time {
    fn type_info() -> PgTypeInfo {
        // 1083 => PgType::Time
        PgTypeInfo::with_oid(Oid(1083))
    }
}

impl PgHasArrayType for Time {
    fn array_type_info() -> PgTypeInfo {
        // 1183 => PgType::TimeArray
        PgTypeInfo::with_oid(Oid(1183))
    }
}

impl Encode<'_, Postgres> for Time {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        let time = self.to_jiff();

        // TIME is encoded as the microseconds since midnight
        let micros =
            time.duration_since(jiff::civil::Time::midnight()).as_micros();
        let micros = i64::try_from(micros).map_err(|_| {
            format!("Time {time} out of range for Postgres: {micros}")
        })?;
        Encode::<Postgres>::encode(micros, buf)
    }

    fn size_hint(&self) -> usize {
        size_of::<i64>()
    }
}

impl<'r> Decode<'r, Postgres> for Time {
    fn decode(value: PgValueRef<'r>) -> Result<Self, BoxDynError> {
        Ok(match value.format() {
            PgValueFormat::Binary => {
                // TIME is encoded as the microseconds since midnight
                let us: i64 = Decode::<Postgres>::decode(value)?;
                let time = jiff::civil::Time::midnight()
                    .checked_add(SignedDuration::from_micros(us))?;
                time.to_sqlx()
            }
            PgValueFormat::Text => {
                let s = value.as_str()?;
                let time = jiff::civil::Time::strptime("%H:%M:%S%.f", s)?;
                time.to_sqlx()
            }
        })
    }
}
