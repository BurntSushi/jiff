use anyhow::Context;
use jiff::civil;
use jiff_sqlx::ToSqlx;
use sqlx::SqlitePool;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let tmpfile = tempfile::NamedTempFile::new()?;
    let path = tmpfile.path().to_str().context("invalid temporary file")?;
    let pool = SqlitePool::connect(path).await?;

    example_datetime_roundtrip(&pool).await?;
    example_timestamp_julian(&pool).await?;

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
async fn example_datetime_roundtrip(pool: &SqlitePool) -> anyhow::Result<()> {
    type Record = (
        jiff_sqlx::Timestamp,
        jiff_sqlx::DateTime,
        jiff_sqlx::Date,
        jiff_sqlx::Time,
    );

    let given = (
        "1970-01-01T00:00:00Z".parse::<jiff::Timestamp>()?.to_sqlx(),
        civil::date(2025, 7, 20).at(0, 0, 0, 0).to_sqlx(),
        civil::date(1999, 1, 8).to_sqlx(),
        civil::time(23, 59, 59, 999_999_999).to_sqlx(),
    );
    let query = "SELECT $1, $2, $3, $4";
    let got: Record = sqlx::query_as(query)
        .bind(&given.0)
        .bind(&given.1)
        .bind(&given.2)
        .bind(&given.3)
        .fetch_one(pool)
        .await?;
    assert_eq!(got, given);
    Ok(())
}

/// Demonstrates that Jiff works with SQLite's "julian day" format.
///
/// Here's a sample transcript to show how SQLite itself works:
///
/// ```text
/// sqlite> select julianday('2025-02-06T21:33:30-05:00');
/// julianday('2025-02-06T21:33:30-05:00')
/// --------------------------------------
/// 2460713.60659722
/// sqlite> select datetime(2460713.60659722);
/// datetime(2460713.60659722)
/// --------------------------
/// 2025-02-07 02:33:30
/// sqlite> select unixepoch(2460713.60659722);
/// unixepoch(2460713.60659722)
/// ---------------------------
/// 1738895610
/// ```
async fn example_timestamp_julian(pool: &SqlitePool) -> anyhow::Result<()> {
    let given = "2025-02-06T21:33:30-05".parse::<jiff::Timestamp>()?.to_sqlx();
    let query = "SELECT julianday($1);";
    let (got,): (jiff_sqlx::Timestamp,) =
        sqlx::query_as(query).bind(&given).fetch_one(pool).await?;

    // Play stupid games, win stupid prizes. The loss of precision here
    // is what you get when you use floating point to represent datetimes.
    let expected =
        "2025-02-07T02:33:29.99981308Z".parse::<jiff::Timestamp>()?.to_sqlx();
    assert_eq!(got, expected);

    Ok(())
}
