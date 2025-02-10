use anyhow::Context;
use diesel::{
    connection::Connection, dsl::sql, query_dsl::RunQueryDsl, select,
    sql_query, sql_types, sqlite::SqliteConnection, QueryableByName,
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
    diesel::table! {
        jiffs {
            id -> Integer, // Diesel tables require an ID column.
            ts -> TimestamptzSqlite,
            dt -> Timestamp,
            d -> Date,
            t -> Time
        }
    }

    #[derive(Debug, PartialEq, QueryableByName)]
    #[diesel(check_for_backend(diesel::sqlite::Sqlite))]
    struct Jiff {
        #[diesel(deserialize_as = jiff_diesel::Timestamp)]
        pub ts: jiff::Timestamp,
        #[diesel(deserialize_as = jiff_diesel::DateTime)]
        pub dt: jiff::civil::DateTime,
        #[diesel(deserialize_as = jiff_diesel::Date)]
        pub d: jiff::civil::Date,
        #[diesel(deserialize_as = jiff_diesel::Time)]
        pub t: jiff::civil::Time,
    }

    let given = Jiff {
        ts: "1970-01-01T00:00:00Z".parse()?,
        dt: civil::date(2025, 7, 20).at(0, 0, 0, 0),
        d: civil::date(1999, 1, 8),
        t: civil::time(23, 59, 59, 999_999_000),
    };

    // We need to name the columns as Diesel's sql_query matches fields by name.
    let got = sql_query("select $1 as ts, $2 as dt, $3 as d, $4 as t")
        .bind::<sql_types::TimestamptzSqlite, _>(&given.ts.to_diesel())
        .bind::<sql_types::Timestamp, _>(&given.dt.to_diesel())
        .bind::<sql_types::Date, _>(&given.d.to_diesel())
        .bind::<sql_types::Time, _>(&given.t.to_diesel())
        .get_result(conn)?;
    assert_eq!(given, got);

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
