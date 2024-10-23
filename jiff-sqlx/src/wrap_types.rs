macro_rules! define_wrap_type {
    ($wrapper:ident, $wrapper_trait:ident, $origin:ty) => {
        pub trait $wrapper_trait {
            fn to_sqlx(self) -> $wrapper;
        }

        #[derive(Debug, Clone, Copy)]
        pub struct $wrapper($origin);

        impl $wrapper {
            pub fn to_jiff(self) -> $origin {
                self.0
            }
        }

        impl $wrapper_trait for $origin {
            fn to_sqlx(self) -> $wrapper {
                $wrapper(self)
            }
        }

        impl From<$wrapper> for $origin {
            fn from(value: $wrapper) -> Self {
                value.0
            }
        }

        impl From<$origin> for $wrapper {
            fn from(value: $origin) -> Self {
                Self(value)
            }
        }
    };
}

define_wrap_type!(Timestamp, ToTimestamp, jiff::Timestamp);
define_wrap_type!(SignedDuration, ToSignedDuration, jiff::SignedDuration);
define_wrap_type!(Date, ToDate, jiff::civil::Date);
define_wrap_type!(Time, ToTime, jiff::civil::Time);
define_wrap_type!(DateTime, ToDateTime, jiff::civil::DateTime);
