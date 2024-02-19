// The `MaybeBox` type is kind of suspect. It's mostly used to shrink error
// types whenever we have `alloc` available. But it might actually make more
// sense to reduce the amount of error information available when `alloc`
// isn't enabled, since presumably the size of types is *more* of an issue in
// environments without `alloc`. If you find yourself in this conundrum, please
// file an issue.

/// A conditional `Box` for some type.
///
/// This uses a `Box` internally when the `alloc` crate feature is enabled,
/// and inlines the `T` into this type otherwise. This is useful for reducing
/// the size of types when dynamic memory allocation is available.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MaybeBox<T>(
    #[cfg(feature = "alloc")] alloc::boxed::Box<T>,
    #[cfg(not(feature = "alloc"))] T,
);

impl<T> MaybeBox<T> {
    /// Create a new conditional box for `T`.
    pub(crate) fn new(t: T) -> MaybeBox<T> {
        #[cfg(feature = "alloc")]
        {
            MaybeBox(alloc::boxed::Box::new(t))
        }
        #[cfg(not(feature = "alloc"))]
        {
            MaybeBox(t)
        }
    }

    /// Move out of this box.
    pub(crate) fn into_inner(this: MaybeBox<T>) -> T {
        #[cfg(feature = "alloc")]
        {
            *this.0
        }
        #[cfg(not(feature = "alloc"))]
        {
            this.0
        }
    }
}

impl<T> core::ops::Deref for MaybeBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> core::ops::DerefMut for MaybeBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}
