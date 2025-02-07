use diesel::{
    connection::Connection, dsl::sql, pg::PgConnection,
    query_dsl::RunQueryDsl, select, sql_query, sql_types,
};
use jiff::civil;
use jiff_diesel::ToDiesel;

fn main() -> anyhow::Result<()> {
    let mut conn = PgConnection::establish(
        "postgres://postgres:password@localhost/test",
    )?;

    example_datetime_roundtrip(&mut conn)?;
    example_span_decode(&mut conn)?;
    example_time_zone_setting(&mut conn)?;

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
fn example_datetime_roundtrip(conn: &mut PgConnection) -> anyhow::Result<()> {
    // Integration with jiff::Timestamp
    let ts = "1970-01-01T00:00:00Z".parse::<jiff::Timestamp>()?.to_diesel();
    let query = select(sql::<sql_types::Timestamptz>(
        "'1970-01-01 00:00:00Z'::timestamp with time zone",
    ));
    let got: jiff_diesel::Timestamp = query.get_result(conn)?;
    assert_eq!(ts, got);

    // Integration with jiff::civil::DateTime
    let dt = civil::date(2025, 7, 20).at(0, 0, 0, 0).to_diesel();
    let query = select(sql::<sql_types::Timestamp>(
        "'2025-07-20 00:00:00'::timestamp without time zone",
    ));
    let got: jiff_diesel::DateTime = query.get_result(conn)?;
    assert_eq!(dt, got);

    // Integration with jiff::civil::Date
    let date = civil::date(1999, 1, 8).to_diesel();
    let query = select(sql::<sql_types::Date>("'1999-01-08'::date"));
    let got: jiff_diesel::Date = query.get_result(conn)?;
    assert_eq!(date, got);

    // Integration with jiff::civil::Time
    let time = civil::time(23, 59, 59, 999_999_000).to_diesel();
    let query = select(sql::<sql_types::Time>("'23:59:59.999999'::time"));
    let got: jiff_diesel::Time = query.get_result(conn)?;
    assert_eq!(time, got);

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
fn example_span_decode(conn: &mut PgConnection) -> anyhow::Result<()> {
    let query = select(sql::<sql_types::Interval>(
        "'2 years 15 months 100 weeks 99 hours 123456789 milliseconds'::interval",
    ));
    let got: jiff_diesel::Span = query.get_result(conn)?;

    // The reason the span is in months/days/micros is because this
    // is how the interval is transmitted from PostgreSQL. Years and
    // months collapse into months, weeks and days collapses into days
    // and everything else collapses into microseconds. If you need to
    // preserve a `Span` as-is, then you'll need to encode it using Jiff's
    // "friendly" duration format.
    let span =
        jiff::Span::new().months(39).days(700).microseconds(479856789000i64);
    assert_eq!(span.fieldwise(), got.to_jiff());

    Ok(())
}

/// Demonstrates that PostgreSQL's time zone session setting doesn't fuck up
/// decoding.
///
/// This doesn't seem to trigger the same "text" decoding path that happens
/// in SQLx. No clue why. And the Diesel impls for datetime types don't seem
/// to have handling for text decoding, so maybe Diesel is doing something
/// that forces binary data. ¯\_(ツ)_/¯
///
/// Ref: https://github.com/launchbadge/sqlx/issues/703#issuecomment-939133588
fn example_time_zone_setting(conn: &mut PgConnection) -> anyhow::Result<()> {
    sql_query("SET TIME ZONE 'Australia/Tasmania'").execute(conn)?;

    let ts = "2020-01-01T05:01:01Z".parse::<jiff::Timestamp>()?.to_diesel();
    let query = select(sql::<sql_types::Timestamptz>(
        "'2020-01-01 05:01:01+00'::timestamp with time zone",
    ));
    let got: jiff_diesel::Timestamp = query.get_result(conn)?;
    assert_eq!(ts, got);

    let dt =
        "2020-01-01T05:01:01".parse::<jiff::civil::DateTime>()?.to_diesel();
    let query = select(sql::<sql_types::Timestamp>(
        "'2020-01-01 05:01:01+00'::timestamp without time zone",
    ));
    let got: jiff_diesel::DateTime = query.get_result(conn)?;
    assert_eq!(dt, got);

    Ok(())
}
