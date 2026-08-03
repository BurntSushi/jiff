use serde_test::{
    Compact, Configure, Token, assert_de_tokens_error, assert_tokens,
};

use jiff::{
    SignedDuration, Span, Timestamp,
    civil::{DateTime, date, datetime, time},
};

#[test]
fn civil_date() {
    let date = date(2024, 2, 29);
    assert_tokens(&date.readable(), &[Token::Str("2024-02-29")]);
    assert_tokens(&date.compact(), &[Token::I32(19_782)]);

    assert_de_tokens_error::<Compact<jiff::civil::Date>>(
        &[Token::I32(i32::MAX)],
        "binary Date day is outside Jiff's supported range",
    );
}

#[test]
fn civil_time() {
    let time = time(12, 34, 56, 789_012_345);
    assert_tokens(&time.readable(), &[Token::Str("12:34:56.789012345")]);
    assert_tokens(&time.compact(), &[Token::U64(45_296_789_012_345)]);

    assert_de_tokens_error::<Compact<jiff::civil::Time>>(
        &[Token::U64(86_400_000_000_000)],
        "binary Time nanosecond is outside 0..=86,399,999,999,999",
    );
}

#[test]
fn civil_datetime() {
    let datetime = datetime(2024, 2, 29, 12, 34, 56, 789_012_345);
    assert_tokens(
        &datetime.readable(),
        &[Token::Str("2024-02-29T12:34:56.789012345")],
    );
    assert_tokens(
        &datetime.compact(),
        &[
            Token::Tuple { len: 2 },
            Token::I32(19_782),
            Token::U64(45_296_789_012_345),
            Token::TupleEnd,
        ],
    );

    assert_de_tokens_error::<Compact<DateTime>>(
        &[
            Token::Tuple { len: 2 },
            Token::I32(0),
            Token::U64(86_400_000_000_000),
            Token::TupleEnd,
        ],
        "binary DateTime time is outside 0..=86,399,999,999,999 nanoseconds",
    );
}

#[test]
fn timestamp() {
    let timestamp = Timestamp::new(1, 2).unwrap();
    assert_tokens(
        &timestamp.readable(),
        &[Token::Str("1970-01-01T00:00:01.000000002Z")],
    );
    assert_tokens(
        &timestamp.compact(),
        &[
            Token::Tuple { len: 2 },
            Token::I64(1),
            Token::I32(2),
            Token::TupleEnd,
        ],
    );

    assert_de_tokens_error::<Compact<Timestamp>>(
        &[
            Token::Tuple { len: 2 },
            Token::I64(1),
            Token::I32(-1),
            Token::TupleEnd,
        ],
        "binary Timestamp components must have the same sign unless either is zero",
    );
}

#[test]
fn signed_duration() {
    let duration = SignedDuration::new(1, 2);
    assert_tokens(&duration.readable(), &[Token::Str("PT1.000000002S")]);
    assert_tokens(
        &duration.compact(),
        &[
            Token::Tuple { len: 2 },
            Token::I64(1),
            Token::I32(2),
            Token::TupleEnd,
        ],
    );

    assert_de_tokens_error::<Compact<SignedDuration>>(
        &[
            Token::Tuple { len: 2 },
            Token::I64(i64::MAX),
            Token::I32(1_000_000_000),
            Token::TupleEnd,
        ],
        "binary SignedDuration nanosecond must be in -999,999,999..=999,999,999",
    );
}

#[test]
fn span() {
    let span = Span::new()
        .years(1)
        .months(2)
        .weeks(3)
        .days(4)
        .hours(5)
        .minutes(6)
        .seconds(7)
        .milliseconds(8)
        .microseconds(9)
        .nanoseconds(10);
    assert_tokens(
        &FieldwiseSpan(span).readable(),
        &[Token::Str("P1Y2M3W4DT5H6M7.00800901S")],
    );
    assert_tokens(
        &FieldwiseSpan(span).compact(),
        &[
            Token::Tuple { len: 10 },
            Token::I16(1),
            Token::I32(2),
            Token::I32(3),
            Token::I32(4),
            Token::I32(5),
            Token::I64(6),
            Token::I64(7),
            Token::I64(8),
            Token::I64(9),
            Token::I64(10),
            Token::TupleEnd,
        ],
    );

    assert_de_tokens_error::<Compact<FieldwiseSpan>>(
        &[
            Token::Tuple { len: 10 },
            Token::I16(1),
            Token::I32(-2),
            Token::I32(0),
            Token::I32(0),
            Token::I32(0),
            Token::I64(0),
            Token::I64(0),
            Token::I64(0),
            Token::I64(0),
            Token::I64(0),
            Token::TupleEnd,
        ],
        "binary Span non-zero components must all have the same sign",
    );
}

#[derive(Clone, Copy, Debug)]
struct FieldwiseSpan(Span);

impl PartialEq for FieldwiseSpan {
    fn eq(&self, other: &FieldwiseSpan) -> bool {
        self.0.fieldwise() == other.0.fieldwise()
    }
}

impl serde_core::Serialize for FieldwiseSpan {
    fn serialize<S: serde_core::Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serde_core::Serialize::serialize(&self.0, serializer)
    }
}

impl<'de> serde_core::Deserialize<'de> for FieldwiseSpan {
    fn deserialize<D: serde_core::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<FieldwiseSpan, D::Error> {
        serde_core::Deserialize::deserialize(deserializer).map(FieldwiseSpan)
    }
}
