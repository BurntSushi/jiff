/*!
This module re-exports a "dumb" version of `std::borrow::Cow`.

It doesn't have any of the generic goodness and doesn't support dynamically
sized types. It's just either a `T` or a `&T`.

We have pretty simplistic needs, and we use this simpler type that works
in core-only mode.
*/

#[derive(Clone, Debug)]
pub(crate) enum DumbCow<'a, T> {
    Owned(T),
    Borrowed(&'a T),
}

impl<'a, T> core::ops::Deref for DumbCow<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        match *self {
            DumbCow::Owned(ref t) => t,
            DumbCow::Borrowed(t) => t,
        }
    }
}

impl<'a, T: core::fmt::Display> core::fmt::Display for DumbCow<'a, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(core::ops::Deref::deref(self), f)
    }
}
