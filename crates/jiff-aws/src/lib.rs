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
        DateTime::from_secs_and_nanos(
            timestamp.as_second(),
            timestamp.subsec_nanosecond() as u32,
        )
    }

    fn from_zoned(zoned: Zoned) -> Self {
        let timestamp = zoned.timestamp();
        DateTime::from_secs_and_nanos(
            timestamp.as_second(),
            timestamp.subsec_nanosecond() as u32,
        )
    }

    fn try_into_zoned(self) -> Result<Zoned, Self::Error> {
        Zoned::try_from_aws(self)
    }

    fn try_into_timestamp(self) -> Result<Timestamp, Self::Error> {
        Timestamp::try_from_aws(self)
    }
}
