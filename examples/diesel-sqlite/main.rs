use anyhow::Context;
use diesel::{
    connection::Connection, dsl::sql, query_dsl::RunQueryDsl, select,
    sql_types, sqlite::SqliteConnection,
};
use jiff::civil;
use jiff_diesel::ToDiesel;

fn main() -> anyhow::Result<()> {
    let tmpfile = tempfile::NamedTempFile::new()?;
    let path = tmpfile.path().to_str().context("invalid temporary file")?;
    let mut conn = SqliteConnection::establish(path)?;

    example_datetime_roundtrip(&mut conn)?;
    example_timestamp_julian(&mut conn)?;

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
fn example_datetime_roundtrip(
    conn: &mut SqliteConnection,
) -> anyhow::Result<()> {
    // Integration with jiff::Timestamp
    let ts = "1970-01-01T00:00:00Z".parse::<jiff::Timestamp>()?.to_diesel();
    let query =
        select(sql::<sql_types::TimestamptzSqlite>("'1970-01-01 00:00:00Z'"));
    let got: jiff_diesel::Timestamp = query.get_result(conn)?;
    assert_eq!(ts, got);

    // Integration with jiff::civil::DateTime
    let dt = civil::date(2025, 7, 20).at(0, 0, 0, 0).to_diesel();
    let query = select(sql::<sql_types::Timestamp>("'2025-07-20 00:00:00'"));
    let got: jiff_diesel::DateTime = query.get_result(conn)?;
    assert_eq!(dt, got);

    // Integration with jiff::civil::Date
    let date = civil::date(1999, 1, 8).to_diesel();
    let query = select(sql::<sql_types::Date>("'1999-01-08'"));
    let got: jiff_diesel::Date = query.get_result(conn)?;
    assert_eq!(date, got);

    // Integration with jiff::civil::Time
    let time = civil::time(23, 59, 59, 999_999_000).to_diesel();
    let query = select(sql::<sql_types::Time>("'23:59:59.999999'"));
    let got: jiff_diesel::Time = query.get_result(conn)?;
    assert_eq!(time, got);

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
fn example_timestamp_julian(
    conn: &mut SqliteConnection,
) -> anyhow::Result<()> {
    let query = select(sql::<sql_types::TimestamptzSqlite>(
        "julianday('2025-02-06T21:33:30-05:00')",
    ));
    let got: jiff_diesel::Timestamp = query.get_result(conn)?;

    // Play stupid games, win stupid prizes. The loss of precision here
    // is what you get when you use floating point to represent datetimes.
    let expected = "2025-02-07T02:33:29.99981308Z"
        .parse::<jiff::Timestamp>()?
        .to_diesel();
    assert_eq!(got, expected);

    Ok(())
}
