use core::convert::Infallible;

/// Adds infallible conversions between crates that mirrors [`From`].
pub trait ConvertFrom<F>: Sized {
    /// Infallibly converts a value of type `F` to a value of type `Self`.
    fn convert_from(value: F) -> Self;
}

/// Adds infallible conversions between crates that mirrors [`Into`].
pub trait ConvertInto<T>: Sized {
    /// Infallibly converts a value of type `Self` to a value of type `T`.
    fn convert_into(self) -> T;
}

/// Adds fallible conversions between crates that mirrors [`TryFrom`].
pub trait ConvertTryFrom<F>: Sized {
    /// The type of an error that can occur during a conversion.
    ///
    /// In this crate, all errors correspond to the [`Error`](crate::Error)
    /// type.
    type Error;

    /// Fallibly converts a value of type `F` to a value of type `Self`.
    fn convert_try_from(value: F) -> Result<Self, Self::Error>;
}

/// Adds fallible conversions between crates that mirrors [`TryInto`].
pub trait ConvertTryInto<T>: Sized {
    /// The type of an error that can occur during a conversion.
    ///
    /// In this crate, all errors correspond to the [`Error`](crate::Error)
    /// type.
    type Error;

    /// Fallibly converts a value of type `Self` to a value of type `T`.
    fn convert_try_into(self) -> Result<T, Self::Error>;
}

impl<F: ConvertInto<T>, T> ConvertTryFrom<F> for T {
    type Error = Infallible;

    fn convert_try_from(value: F) -> Result<T, Infallible> {
        Ok(value.convert_into())
    }
}

impl<F, T: ConvertFrom<F>> ConvertInto<T> for F {
    fn convert_into(self) -> T {
        T::convert_from(self)
    }
}

impl<F, T: ConvertTryFrom<F>> ConvertTryInto<T> for F {
    type Error = T::Error;

    fn convert_try_into(self) -> Result<T, T::Error> {
        T::convert_try_from(self)
    }
}
