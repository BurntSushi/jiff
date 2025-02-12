use aws_smithy_types::DateTime;
use jiff::{Timestamp, Zoned};

/// A trait for adding methods to convert types into the [Jiff](jiff) types
/// [Timestamp](jiff::Timestamp) and [Zoned](jiff::Zoned)
pub trait ConvertJiffTypes: Sized {
    type Error;
    /// Infallibly creates a value of type `Self` from a Jiff [`Timestamp`](jiff::Timestamp)
    fn from_timestamp(value: Timestamp) -> Self;
    /// Infallibly creates a value of type `Self` from a Jiff [`Zoned`](jiff::Zoned)
    fn from_zoned(value: Zoned) -> Self;
    /// Fallibly creates a Jiff [`Zoned`](jiff::Zoned) (in TimeZone UTC) from `Self`
    fn try_into_zoned(self) -> Result<Zoned, Self::Error>;
    /// Fallibly creates a Jiff [`Timestamp`](jiff::Timestamp) from `Self`
    fn try_into_timestamp(self) -> Result<Timestamp, Self::Error>;
}

/// A trait for adding methods to convert types into the aws smithy type [DateTime](aws_smithy_types::DateTime)
pub trait ConvertAwsDateTime: Sized {
    type Error;
    /// Infallibly converts a value of type `Self` to a value of type Aws Smithy
    /// [`DateTime`](aws_smithy_types::DateTime).
    fn into_aws_datetime(self) -> DateTime;

    /// Fallibly converts a value of Aws Smithy type [`DateTime`](aws_smithy_types::DateTime) to a value of type `Self`.
    fn try_from_aws(value: DateTime) -> Result<Self, Self::Error>;
}
