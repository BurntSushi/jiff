use jiff::civil;
use jiff_sqlx::ToSqlx;
use sqlx::postgres::{PgPool, PgPoolOptions};

type Record = (
    jiff_sqlx::Timestamp,
    jiff_sqlx::DateTime,
    jiff_sqlx::Date,
    jiff_sqlx::Time,
);

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let pool = PgPoolOptions::new()
        .max_connections(1)
        .connect("postgres://postgres:password@localhost/test")
        .await?;

    example_datetime_roundtrip(&pool).await?;
    example_span_decode(&pool).await?;
    example_time_zone_setting(&pool).await?;

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
async fn example_datetime_roundtrip(pool: &PgPool) -> anyhow::Result<()> {
    let given = (
        "1970-01-01T00:00:00Z".parse::<jiff::Timestamp>()?.to_sqlx(),
        civil::date(2025, 7, 20).at(0, 0, 0, 0).to_sqlx(),
        civil::date(1999, 1, 8).to_sqlx(),
        civil::time(23, 59, 59, 999_999_000).to_sqlx(),
    );
    let query = "SELECT $1, $2, $3, $4";
    let got: Record = sqlx::query_as(query)
        .bind(&given.0)
        .bind(given.1)
        .bind(given.2)
        .bind(given.3)
        .fetch_one(pool)
        .await?;
    assert_eq!(got, given);
    Ok(())
}

/// Shows how to decode a PostgreSQL interval into a Jiff `Span`.
///
/// Jiff doesn't support encoding a `Span` as a PostgreSQL interval, but
/// Jiff can decode a PostgreSQL interval into a `Span`. The reason for this
/// is that encoding an arbitrary `Span` into a PostgreSQL interval requires
/// a relative datetime. Therefore, users wanting to store a `Span` will
/// need to explicitly use a `sqlx::postgres::types::PgInterval` at least at
/// encoding time.
async fn example_span_decode(pool: &PgPool) -> anyhow::Result<()> {
    let query =
        "SELECT '2 years 15 months 100 weeks 99 hours 123456789 milliseconds'::interval;";
    let (span,): (jiff_sqlx::Span,) =
        sqlx::query_as(query).fetch_one(pool).await?;
    assert_eq!(
        span.to_jiff().fieldwise(),
        // The reason the span is in months/days/micros is because this
        // is how te interval is transmitted from PostgreSQL. Years and
        // months collapse into months, weeks and days collapses into days
        // and everything else collapses into microseconds. If you need to
        // preserve a `Span` as-is, then you'll need to encode it using Jiff's
        // "friendly" duration format.
        jiff::Span::new().months(39).days(700).microseconds(479856789000i64),
    );
    Ok(())
}

/// Demonstrates that PostgreSQL's time zone session setting doesn't fuck up
/// decoding.
///
/// Ref: https://github.com/launchbadge/sqlx/issues/703#issuecomment-939133588
async fn example_time_zone_setting(pool: &PgPool) -> anyhow::Result<()> {
    use sqlx::{Executor, Row};

    sqlx::query("SET TIME ZONE 'Australia/Tasmania'")
        .fetch_optional(pool)
        .await?;

    let row =
        pool.fetch_one("SELECT '2020-01-01 05:01:01+00'::timestamptz").await?;
    let ts = "2020-01-01T05:01:01Z".parse::<jiff::Timestamp>()?.to_sqlx();
    assert_eq!(row.get::<jiff_sqlx::Timestamp, _>(0), ts);

    let row =
        pool.fetch_one("SELECT '2020-01-01 05:01:01+00'::timestamp").await?;
    let dt = "2020-01-01T05:01:01".parse::<jiff::civil::DateTime>()?.to_sqlx();
    assert_eq!(row.get::<jiff_sqlx::DateTime, _>(0), dt);

    Ok(())
}
