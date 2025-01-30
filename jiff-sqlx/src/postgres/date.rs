use crate::{Date, ToDate};
use sqlx::encode::IsNull;
use sqlx::error::BoxDynError;
use sqlx::postgres::types::Oid;
use sqlx::postgres::{
    PgArgumentBuffer, PgHasArrayType, PgTypeInfo, PgValueFormat, PgValueRef,
};
use sqlx::{Decode, Encode, Postgres, Type};

impl Type<Postgres> for Date {
    fn type_info() -> PgTypeInfo {
        // 1082 => PgType::Date
        PgTypeInfo::with_oid(Oid(1082))
    }
}

impl PgHasArrayType for Date {
    fn array_type_info() -> PgTypeInfo {
        // 1182 => PgType::DateArray
        PgTypeInfo::with_oid(Oid(1182))
    }
}

impl Encode<'_, Postgres> for Date {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        let date = self.to_jiff();

        // DATE is encoded as the days since epoch
        let days = date.since(postgres_epoch_date())?.get_days();
        Encode::<Postgres>::encode(days, buf)
    }

    fn size_hint(&self) -> usize {
        size_of::<i32>()
    }
}

impl<'r> Decode<'r, Postgres> for Date {
    fn decode(value: PgValueRef<'r>) -> Result<Self, BoxDynError> {
        Ok(match value.format() {
            PgValueFormat::Binary => {
                // DATE is encoded as the days since epoch
                let days: i32 = Decode::<Postgres>::decode(value)?;
                let date = jiff::Span::new()
                    .try_days(days)
                    .and_then(|s| postgres_epoch_date().checked_add(s))?;
                date.to_sqlx()
            }
            PgValueFormat::Text => {
                let s = value.as_str()?;
                let date = jiff::civil::Date::strptime("%Y-%m-%d", s)?;
                date.to_sqlx()
            }
        })
    }
}

const fn postgres_epoch_date() -> jiff::civil::Date {
    jiff::civil::Date::constant(2000, 1, 1)
}
