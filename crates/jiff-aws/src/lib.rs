/*!
This crate provides type convertion for [Jiff](jiff) and
Aws Smithy Type [DateTime] used
in the [AWS SDK for Rust](https://aws.amazon.com/sdk-for-rust/).

```
use jiff_aws::ConvertAwsDateTime;
use jiff_aws::ConvertJiffTypes;
use jiff::Timestamp;
use jiff::Zoned;
use aws_smithy_types::DateTime;

let datetime = DateTime::from_secs_and_nanos(1627680004,123000000);
let timestamp: Timestamp = datetime.try_into_timestamp().unwrap();
assert_eq!( "2021-07-30T21:20:04.123Z".parse::<Timestamp>().unwrap(), timestamp);

let timestamp = Timestamp::try_from_aws(datetime).unwrap();
assert_eq!( "2021-07-30T21:20:04.123Z".parse::<Timestamp>().unwrap(), timestamp);

let zoned = datetime.try_into_zoned().unwrap();
assert_eq!( "2021-07-30T21:20:04.123+00:00[UTC]".parse::<Zoned>().unwrap(), zoned);

let zoned = Zoned::try_from_aws(datetime).unwrap();
assert_eq!( "2021-07-30T21:20:04.123+00:00[UTC]".parse::<Zoned>().unwrap(), zoned);

let other: DateTime = timestamp.into_aws_datetime();
assert_eq!(datetime, other);

let other = DateTime::from_timestamp(timestamp);
assert_eq!(datetime, other);

let other: DateTime = zoned.clone().into_aws_datetime();
assert_eq!(datetime, other);

let other = DateTime::from_zoned(zoned);
assert_eq!(datetime, other);

```
*/

use aws_smithy_types::DateTime;
use jiff::{tz::TimeZone, Timestamp, Zoned};
pub use traits::{ConvertAwsDateTime, ConvertJiffTypes};
mod traits;

impl ConvertAwsDateTime for Timestamp {
    type Error = jiff::Error;

    fn into_aws_datetime(self) -> DateTime {
        DateTime::from_timestamp(self)
    }

    fn try_from_aws(value: DateTime) -> Result<Self, Self::Error> {
        jiff::Timestamp::new(value.secs(), value.subsec_nanos() as i32)
    }
}

impl ConvertAwsDateTime for Zoned {
    type Error = jiff::Error;

    fn into_aws_datetime(self) -> DateTime {
        DateTime::from_zoned(self)
    }

    fn try_from_aws(value: DateTime) -> Result<Self, Self::Error> {
        let timestamp =
            jiff::Timestamp::new(value.secs(), value.subsec_nanos() as i32)?;
        Ok(timestamp.to_zoned(TimeZone::UTC))
    }
}

impl ConvertJiffTypes for DateTime {
    type Error = jiff::Error;

    fn from_timestamp(timestamp: Timestamp) -> Self {
        let (seconds, nanos) = if timestamp.subsec_nanosecond() < 0 {
            (
                timestamp.as_second() - 1,
                (1_000_000_000 + timestamp.subsec_nanosecond()) as u32,
            )
        } else {
            (timestamp.as_second(), timestamp.subsec_nanosecond() as u32)
        };

        DateTime::from_secs_and_nanos(seconds, nanos)
    }

    fn from_zoned(zoned: Zoned) -> Self {
        let timestamp = zoned.timestamp();
        Self::from_timestamp(timestamp)
    }

    fn try_into_zoned(self) -> Result<Zoned, Self::Error> {
        Zoned::try_from_aws(self)
    }

    fn try_into_timestamp(self) -> Result<Timestamp, Self::Error> {
        Timestamp::try_from_aws(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::{traits::ConvertJiffTypes, ConvertAwsDateTime};
    use aws_smithy_types::DateTime;
    use jiff::{Timestamp, ToSpan};

    #[test]
    fn epoch() -> Result<(), jiff::Error> {
        //Epoch
        let ts = Timestamp::UNIX_EPOCH;
        let dt = ts.into_aws_datetime();
        assert_eq!(DateTime::from_secs_and_nanos(0, 0), dt);

        //Roundtrip Epoch
        let ts2 = dt.try_into_timestamp()?;
        assert_eq!(Timestamp::UNIX_EPOCH, ts2);

        Ok(())
    }

    #[test]
    fn epoch_minus_one_nano() -> Result<(), jiff::Error> {
        // Epoch -1 nanosecond
        let ts = Timestamp::UNIX_EPOCH - 1.nanosecond();
        let dt = ts.into_aws_datetime();
        assert_eq!(DateTime::from_secs_and_nanos(-1, 999_999_999), dt);

        // Roundtrip -1 nanosecond
        let ts2 = dt.try_into_timestamp()?;
        assert_eq!(Timestamp::UNIX_EPOCH - 1.nanosecond(), ts2);

        Ok(())
    }

    #[test]
    fn epoch_minus_one_sec() -> Result<(), jiff::Error> {
        // Epoch -1 second
        let ts = Timestamp::UNIX_EPOCH - 1.second();
        let dt = ts.into_aws_datetime();
        assert_eq!(DateTime::from_secs_and_nanos(-1, 0), dt);

        // Roundtrip epoch -1 second
        let ts2 = dt.try_into_timestamp()?;
        assert_eq!(Timestamp::UNIX_EPOCH - 1.second(), ts2);

        Ok(())
    }

    #[test]
    fn epoch_plus_1_sec_1_nano() -> Result<(), jiff::Error> {
        // Epoch + 1 second and 1 nanosecond
        let ts = Timestamp::UNIX_EPOCH + 1.second() + 1.nanosecond();
        let dt = ts.into_aws_datetime();
        assert_eq!(DateTime::from_secs_and_nanos(1, 1), dt);

        // Roundtrip epoch + 1 second and 1 nanosecond
        let ts2 = dt.try_into_timestamp()?;
        assert_eq!(Timestamp::UNIX_EPOCH + 1.second() + 1.nanosecond(), ts2);

        Ok(())
    }
}
