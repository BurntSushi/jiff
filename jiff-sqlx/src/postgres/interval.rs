use crate::SignedDuration;
use sqlx::encode::IsNull;
use sqlx::error::BoxDynError;
use sqlx::postgres::types::{Oid, PgInterval};
use sqlx::postgres::{PgArgumentBuffer, PgHasArrayType, PgTypeInfo};
use sqlx::{Database, Decode, Encode, Postgres, Type};

impl Type<Postgres> for SignedDuration {
    fn type_info() -> PgTypeInfo {
        // 1186 => PgType::Interval
        PgTypeInfo::with_oid(Oid(1186))
    }
}

impl PgHasArrayType for SignedDuration {
    fn array_type_info() -> PgTypeInfo {
        // 1187 => PgType::IntervalArray
        PgTypeInfo::with_oid(Oid(1187))
    }
}

impl TryFrom<SignedDuration> for PgInterval {
    type Error = BoxDynError;

    /// Convert a `SignedDuration` to a `PgInterval`.
    ///
    /// This returns an error if there is a loss of precision using nanoseconds or if there is a
    /// microseconds overflow.
    fn try_from(value: SignedDuration) -> Result<Self, BoxDynError> {
        let value = value.to_jiff();

        if value.subsec_nanos() % 1000 != 0 {
            return Err(
                "PostgreSQL `INTERVAL` does not support nanoseconds precision"
                    .into(),
            );
        }

        let micros = value.as_micros();
        if micros >= i64::MIN as i128 && micros <= i64::MAX as i128 {
            Ok(Self { months: 0, days: 0, microseconds: micros as i64 })
        } else {
            Err("Overflow has occurred for PostgreSQL `INTERVAL`".into())
        }
    }
}

impl Encode<'_, Postgres> for SignedDuration {
    fn encode_by_ref(
        &self,
        buf: &mut PgArgumentBuffer,
    ) -> Result<IsNull, BoxDynError> {
        let pg_interval = PgInterval::try_from(*self)?;
        pg_interval.encode_by_ref(buf)
    }

    fn size_hint(&self) -> usize {
        2 * size_of::<i64>()
    }
}

impl<'r> Decode<'r, Postgres> for SignedDuration {
    fn decode(
        value: <Postgres as Database>::ValueRef<'r>,
    ) -> Result<Self, BoxDynError> {
        let pg_interval = PgInterval::decode(value)?;

        if pg_interval.months != 0 {
            return Err(
                "Cannot convert months in `INTERVAL` to SignedDuration".into(),
            );
        }

        if pg_interval.days != 0 {
            return Err(
                "Cannot convert days in `INTERVAL` to SignedDuration".into()
            );
        }

        let micros = pg_interval.microseconds;
        Ok(SignedDuration(jiff::SignedDuration::from_micros(micros)))
    }
}

#[cfg(test)]
mod tests {
    use crate::ToSignedDuration;
    use sqlx::postgres::types::PgInterval;

    #[test]
    fn test_pginterval_jiff() {
        // Case for positive duration
        let interval = PgInterval { days: 0, months: 0, microseconds: 27_000 };
        assert_eq!(
            &PgInterval::try_from(
                jiff::SignedDuration::from_micros(27_000).to_sqlx()
            )
            .unwrap(),
            &interval
        );

        // Case for negative duration
        let interval =
            PgInterval { days: 0, months: 0, microseconds: -27_000 };
        assert_eq!(
            &PgInterval::try_from(
                jiff::SignedDuration::from_micros(-27_000).to_sqlx()
            )
            .unwrap(),
            &interval
        );

        // Case when precision loss occurs
        assert!(PgInterval::try_from(
            jiff::SignedDuration::from_nanos(27_000_001).to_sqlx()
        )
        .is_err());
        assert!(PgInterval::try_from(
            jiff::SignedDuration::from_nanos(-27_000_001).to_sqlx()
        )
        .is_err());

        // Case when microseconds overflow occurs
        assert!(PgInterval::try_from(
            jiff::SignedDuration::from_secs(10_000_000_000_000).to_sqlx()
        )
        .is_err());
        assert!(PgInterval::try_from(
            jiff::SignedDuration::from_secs(-10_000_000_000_000).to_sqlx()
        )
        .is_err());
    }
}
