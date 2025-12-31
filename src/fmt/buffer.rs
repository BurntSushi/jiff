use core::mem::MaybeUninit;

use crate::{fmt::Write, Error};

const MAX_CAPACITY: usize = u16::MAX as usize;
// From `u64::MAX.to_string().len()`.
const MAX_INTEGER_LEN: u8 = 20;
const MAX_PRECISION: usize = 9;

/// An uninitialized slice of bytes of fixed size.
///
/// This is typically used with `BorrowedBuffer`.
#[derive(Clone, Copy)]
pub(crate) struct ArrayBuffer<const N: usize> {
    data: [MaybeUninit<u8>; N],
}

impl<const N: usize> ArrayBuffer<N> {
    /// Return a writable buffer into this storage.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn as_borrowed<'data>(&mut self) -> BorrowedBuffer<'_> {
        BorrowedBuffer::from(&mut self.data)
    }

    /// Assume this entire buffer is initialized and return it as an array.
    ///
    /// # Safety
    ///
    /// Callers must ensure the entire buffer is initialized.
    unsafe fn assume_init(self) -> [u8; N] {
        // SAFETY: Callers are responsible for ensuring that `self.data`
        // is initialized. Otherwise, `MaybeUninit<u8>` and `u8` have the
        // same representation.
        unsafe {
            *(&self.data as *const [MaybeUninit<u8>; N] as *const [u8; N])
        }
    }
}

/// Construct an uninitialized buffer of data of size `N`.
impl<const N: usize> Default for ArrayBuffer<N> {
    #[cfg_attr(feature = "perf-inline", inline(always))]
    fn default() -> ArrayBuffer<N> {
        ArrayBuffer { data: [MaybeUninit::uninit(); N] }
    }
}

/// A borrowed buffer for writing into an uninitialized slice of bytes.
///
/// This can be used with, e.g., an `ArrayBuffer` as backing storage. This
/// type will managed actually writing to the backing storage, keeping track
/// of how much data has been written and exposing a safe API.
///
/// This type is principally used in Jiff's printer implementations. In
/// particular, this helps printers generate tighter and more efficient code.
/// Once printing is done, the data in the buffer is then copied to the caller
/// provided implementation of `jiff::fmt::Write`. This double write is
/// unfortunate, but it turned out that threading a `jiff::fmt::Write` down
/// through the printers and using it directly leads to slower code overall
/// *and* more code bloat. This is because a `BorrowedBuffer` is an incredibly
/// lightweight abstraction that never has to deal with I/O or growing an
/// allocation.
///
/// # Design
///
/// * Requires valid UTF-8 so that we can provide higher level safe APIs for
/// interfacing with `String`.
/// * Specifically panics when a write would exceed available capacity. This
/// introduces a branch, but effectively decouples "get the maximum size
/// correct" from "is memory safe."
#[derive(Debug)]
pub(crate) struct BorrowedBuffer<'data> {
    data: &'data mut [MaybeUninit<u8>],
    filled: u16,
}

impl<'data> BorrowedBuffer<'data> {
    /// A high level API for writing to a `jiff::fmt::Write` via a buffer of
    /// uninitialized bytes.
    ///
    /// When the `alloc` crate feature is enabled and `W` provides a
    /// `&mut Vec<u8>`, then the buffer is extracted directly from the
    /// spare capacity of the `Vec<u8>`.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn with_writer<const N: usize>(
        wtr: &mut dyn Write,
        runtime_allocation: usize,
        mut with: impl FnMut(&mut BorrowedBuffer<'_>) -> Result<(), Error>,
    ) -> Result<(), Error> {
        // Specialize for the common case of `W = String` or `W = Vec<u8>`.
        // In effect, we write directly into the excess capacity of `W`
        // instead of first writing into a stack array and then copying that
        // into `W`.
        //
        // This can provide up to a 40% improvement in runtime in some
        // microbenchmarks.
        //
        // SAFETY: We only ever write valid UTF-8. Namely, `BorrowedBuffer`
        // enforces this invariant.
        #[cfg(feature = "alloc")]
        if let Some(buf) = unsafe { wtr.as_mut_vec() } {
            buf.reserve(runtime_allocation);
            return BorrowedBuffer::with_vec_spare_capacity(buf, with);
        }
        let mut buf = ArrayBuffer::<N>::default();
        let mut bbuf = buf.as_borrowed();
        with(&mut bbuf)?;
        wtr.write_str(bbuf.filled())?;
        Ok(())
    }

    /// Provides a borrowed buffer into the first 255 bytes of the spare
    /// capacity in the given `String` and updates the length on `String` after
    /// the closure completes to account for any new data written.
    ///
    /// In effect, this safely encapsulates writing into the uninitialized
    /// portion of a `String`.
    ///
    /// If the provided closure panics, then there is no guarantee that the
    /// `string`'s length will be updated to reflect what has been written.
    /// However, it is guaranteed that the length setting will not lead to
    /// undefined behavior.
    #[cfg(feature = "alloc")]
    #[cfg_attr(feature = "perf-inline", inline(always))]
    #[allow(dead_code)]
    pub(crate) fn with_string_spare_capacity<T>(
        string: &'data mut alloc::string::String,
        with: impl FnMut(&mut BorrowedBuffer<'_>) -> T,
    ) -> T {
        // SAFETY: A `BorrowedBuffer` guarantees that we only ever write valid
        // UTF-8.
        let buf = unsafe { string.as_mut_vec() };
        BorrowedBuffer::with_vec_spare_capacity(buf, with)
    }

    /// Provides a borrowed buffer into the first 255 bytes of the spare
    /// capacity in the given `Vec<u8>` and updates the length on `Vec<u8>`
    /// after the closure completes to account for any new data written.
    ///
    /// In effect, this safely encapsulates writing into the uninitialized
    /// portion of a `Vec<u8>`.
    ///
    /// If the provided closure panics, then there is no guarantee that the
    /// `buf`'s length will be updated to reflect what has been written.
    /// However, it is guaranteed that the length setting will not lead to
    /// undefined behavior.
    #[cfg(feature = "alloc")]
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn with_vec_spare_capacity<T>(
        buf: &'data mut alloc::vec::Vec<u8>,
        mut with: impl FnMut(&mut BorrowedBuffer<'_>) -> T,
    ) -> T {
        let mut bbuf = BorrowedBuffer::from_vec_spare_capacity(buf);
        let returned = with(&mut bbuf);
        let new_len = bbuf.len();
        // SAFETY: `BorrowedBuffer::len()` always reflects the number of
        // bytes that have been written to. Thus, the data up to the given new
        // length is guaranteed to be initialized.
        unsafe {
            buf.set_len(new_len);
        }
        returned
    }

    /// Build a borrowed buffer for writing into the spare capacity of a
    /// `String` allocation.
    ///
    /// This is limited only to the first `255` bytes of the spare capacity.
    #[cfg(feature = "alloc")]
    #[cfg_attr(feature = "perf-inline", inline(always))]
    #[allow(dead_code)]
    pub(crate) fn from_string_spare_capacity(
        string: &'data mut alloc::string::String,
    ) -> BorrowedBuffer<'data> {
        // SAFETY: A `BorrowedBuffer` never writes anything other than valid
        // UTF-8. And specifically, callers are prevented from doing so.
        unsafe { BorrowedBuffer::from_vec_spare_capacity(string.as_mut_vec()) }
    }

    /// Build a borrowed buffer for writing into the spare capacity of a
    /// `Vec<u8>` allocation.
    ///
    /// This is limited only to the first `255` bytes of the spare capacity.
    #[cfg(feature = "alloc")]
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn from_vec_spare_capacity(
        vec: &'data mut alloc::vec::Vec<u8>,
    ) -> BorrowedBuffer<'data> {
        let data = vec.spare_capacity_mut();
        let len = data.len().min(MAX_CAPACITY);
        BorrowedBuffer::from(&mut data[..len])
    }

    /// Write the provided string to the available space in this buffer.
    ///
    /// # Panics
    ///
    /// When the available space is shorter than the length of the provided
    /// string. That is, when `capacity() - filled().len() < string.len()`.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_str(&mut self, string: &str) {
        // SAFETY: A `&str`, `&[u8]` and `&[MaybeUninit<u8>]` all have the
        // same representation in memory.
        let data: &[MaybeUninit<u8>] = unsafe {
            core::slice::from_raw_parts(
                string.as_ptr().cast::<MaybeUninit<u8>>(),
                string.len(),
            )
        };
        self.available()
            .get_mut(..string.len())
            .expect("string data exceeds available buffer space")
            .copy_from_slice(data);
        // Cast here will never truncate because `BorrowedBuffer` is limited
        // to `u16::MAX` in total capacity. Above will panic if `string.len()`
        // exceeds available capacity, which can never be above total capacity.
        // Thus, if we're here, `string.len() <= u16::MAX` is guaranteed to
        // hold.
        self.filled += string.len() as u16;
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_ascii_char(&mut self, byte: u8) {
        assert!(byte.is_ascii());
        *self
            .available()
            .get_mut(0)
            .expect("insufficient buffer space to write one byte") =
            MaybeUninit::new(byte);
        self.filled += 1;
    }

    /// Writes the given `u8` integer to this buffer. No padding is performed.
    ///
    /// # Panics
    ///
    /// When the available space is insufficient to encode the number of
    /// digits in the decimal representation of `n`.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_int(&mut self, mut n: u64) {
        let digits = digits(n);
        let mut remaining_digits = usize::from(digits);
        let available = self
            .available()
            .get_mut(..remaining_digits)
            .expect("u8 integer digits exceeds available buffer space");
        while remaining_digits > 0 {
            remaining_digits -= 1;
            // SAFETY: The assert above guarantees that `remaining_digits` is
            // always in bounds.
            unsafe {
                *available.get_unchecked_mut(remaining_digits) =
                    MaybeUninit::new(b'0' + ((n % 10) as u8));
            }
            n /= 10;
        }
        self.filled += u16::from(digits);
    }

    /// Writes the given `u8` integer to this buffer using the given padding.
    ///
    /// The maximum allowed padding is `20`. Any values bigger than that are
    /// silently clamped to `20`.
    ///
    /// This always pads with zeroes.
    ///
    /// # Panics
    ///
    /// When the available space is insufficient to encode the number of
    /// digits in the decimal representation of `n`.
    ///
    /// This also panics when `pad_byte` is not ASCII.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_int_pad0(&mut self, mut n: u64, pad_len: u8) {
        let pad_len = pad_len.min(MAX_INTEGER_LEN);
        let digits = pad_len.max(digits(n));
        let mut remaining_digits = usize::from(digits);
        let available = self
            .available()
            .get_mut(..remaining_digits)
            .expect("u8 integer digits exceeds available buffer space");
        while remaining_digits > 0 {
            remaining_digits -= 1;
            // SAFETY: The assert above guarantees that `remaining_digits` is
            // always in bounds.
            unsafe {
                *available.get_unchecked_mut(remaining_digits) =
                    MaybeUninit::new(b'0' + ((n % 10) as u8));
            }
            n /= 10;
        }
        self.filled += u16::from(digits);
    }

    /// Writes the given `u8` integer to this buffer using the given padding.
    ///
    /// The maximum allowed padding is `20`. Any values bigger than that are
    /// silently clamped to `20`.
    ///
    /// # Panics
    ///
    /// When the available space is insufficient to encode the number of
    /// digits in the decimal representation of `n`.
    ///
    /// This also panics when `pad_byte` is not ASCII.
    #[allow(dead_code)]
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_int_pad(
        &mut self,
        mut n: u64,
        pad_byte: u8,
        pad_len: u8,
    ) {
        assert!(pad_byte.is_ascii(), "padding byte must be ASCII");

        let pad_len = pad_len.min(MAX_INTEGER_LEN);
        let digits = pad_len.max(digits(n));
        let mut remaining_digits = usize::from(digits);
        let available = self
            .available()
            .get_mut(..remaining_digits)
            .expect("u8 integer digits exceeds available buffer space");
        while remaining_digits > 0 {
            remaining_digits -= 1;
            // SAFETY: The assert above guarantees that `remaining_digits` is
            // always in bounds.
            unsafe {
                *available.get_unchecked_mut(remaining_digits) =
                    MaybeUninit::new(b'0' + ((n % 10) as u8));
            }
            n /= 10;
            if n == 0 {
                break;
            }
        }
        while remaining_digits > 0 {
            remaining_digits -= 1;
            // SAFETY: The assert above guarantees that `remaining_digits` is
            // always in bounds.
            unsafe {
                *available.get_unchecked_mut(remaining_digits) =
                    MaybeUninit::new(pad_byte);
            }
        }
        self.filled += u16::from(digits);
    }

    /// Writes the given integer as a 2-digit zero padded integer to this
    /// buffer.
    ///
    /// # Panics
    ///
    /// When the available space is shorter than 2 or if `n > 99`.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_int_pad2(&mut self, mut n: u64) {
        // This is required for correctness. When `n > 9999`, then the
        // last `n as u8` below could result in writing an invalid UTF-8
        // byte. We don't mind incorrect results, but writing invalid
        // UTF-8 can lead to undefined behavior, and we want this API
        // to be sound.
        //
        // We omit the final `% 10` because it makes micro-benchmark results
        // worse. This panicking check has a more modest impact.
        assert!(n <= 99);

        let dst = self
            .available()
            .get_mut(..2)
            .expect("padded 2 digit integer exceeds available buffer space");
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(1) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(0) = MaybeUninit::new(b'0' + (n as u8));
        }
        self.filled += 2;
    }

    /// Writes the given integer as a 4-digit zero padded integer to this
    /// buffer.
    ///
    /// # Panics
    ///
    /// When the available space is shorter than 4 or if `n > 9999`.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_int_pad4(&mut self, mut n: u64) {
        // This is required for correctness. When `n > 9999`, then the
        // last `n as u8` below could result in writing an invalid UTF-8
        // byte. We don't mind incorrect results, but writing invalid
        // UTF-8 can lead to undefined behavior, and we want this API
        // to be sound.
        //
        // We omit the final `% 10` because it makes micro-benchmark results
        // worse. This panicking check has a more modest impact.
        assert!(n <= 9999);

        let dst = self
            .available()
            .get_mut(..4)
            .expect("padded 4 digit integer exceeds available buffer space");
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(3) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(2) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(1) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(0) = MaybeUninit::new(b'0' + (n as u8));
        }
        self.filled += 4;
    }

    /// Writes the given integer as a 6-digit zero padded integer to this
    /// buffer.
    ///
    /// # Panics
    ///
    /// When the available space is shorter than 6 or if `n > 999999`.
    #[allow(dead_code)]
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_int_pad6(&mut self, mut n: u64) {
        // This is required for correctness. When `n > 999999`, then the
        // last `n as u8` below could result in writing an invalid UTF-8
        // byte. We don't mind incorrect results, but writing invalid
        // UTF-8 can lead to undefined behavior, and we want this API
        // to be sound.
        //
        // We omit the final `% 10` because it makes micro-benchmark results
        // worse. This panicking check has a more modest impact.
        assert!(n <= 999999);

        let dst = self
            .available()
            .get_mut(..6)
            .expect("padded 6 digit integer exceeds available buffer space");
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(5) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(4) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(3) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(2) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(1) =
                MaybeUninit::new(b'0' + ((n % 10) as u8));
        }
        n /= 10;
        // SAFETY: Valid because of the assertion above.
        unsafe {
            *dst.get_unchecked_mut(0) = MaybeUninit::new(b'0' + (n as u8));
        }
        self.filled += 6;
    }

    /// Writes `n` as a fractional component to the given `precision`.
    ///
    /// When `precision` is absent, then it is automatically detected based
    /// on the value of `n`.
    ///
    /// When `precision` is bigger than `9`, then it is clamped to `9`.
    ///
    /// # Panics
    ///
    /// When the available space is shorter than the number of digits required
    /// to write `n` as a fractional value.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn write_fraction(
        &mut self,
        precision: Option<u8>,
        mut n: u32,
    ) {
        assert!(n <= 999_999_999);
        let mut buf = ArrayBuffer::<MAX_PRECISION>::default();
        for i in (0..MAX_PRECISION).rev() {
            unsafe {
                *buf.data.get_unchecked_mut(i) =
                    MaybeUninit::new(b'0' + ((n % 10) as u8));
            }
            n /= 10;
        }

        let end = precision
            .map(|p| p.min(MAX_PRECISION as u8))
            .unwrap_or_else(|| {
                // SAFETY: The loop above is guaranteed to initialize `buf` in
                // its entirety.
                let buf = unsafe { buf.assume_init() };
                let mut end = MAX_PRECISION as u8;
                while end > 0 && buf[usize::from(end) - 1] == b'0' {
                    end -= 1;
                }
                end
            });

        let buf = &buf.data[..usize::from(end)];
        self.available()
            .get_mut(..buf.len())
            .expect("fraction exceeds available buffer space")
            .copy_from_slice(buf);
        self.filled += u16::from(end);
    }

    /// Clears this buffer so that there are no filled bytes.
    ///
    /// Note that no actual clearing of data is done, but this does lose
    /// track of data that has been initialized and data that hasn't been
    /// initialized.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    #[allow(dead_code)]
    pub(crate) fn clear(&mut self) {
        self.filled = 0;
    }

    /// Returns the filled portion of this buffer.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn filled(&self) -> &str {
        // SAFETY: It is guaranteed that `..self.len()` is always a valid
        // range into `self.data` since `self.filled` is only increased upon
        // a valid write.
        let filled = unsafe { self.data.get_unchecked(..self.len()) };
        // SAFETY: Everything up to `self.filled` is guaranteed to be
        // initialized. Also, since `MaybeUninit<u8>` and `u8` have the same
        // representation, we can cast from `&[MaybeUninit<u8>]` to `&[u8]`.
        // Finally, the `BorrowedBuffer` API specifically guarantees that
        // all writes to `self.data` are valid UTF-8.
        unsafe {
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(
                filled.as_ptr().cast::<u8>(),
                self.len(),
            ))
        }
    }

    /// Returns the filled portion of this buffer with a lifetime equivalent
    /// to the original borrow.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    #[allow(dead_code)]
    pub(crate) fn into_filled(&self) -> &'data str {
        // SAFETY: It is guaranteed that `..self.len()` is always a valid
        // range into `self.data` since `self.filled` is only increased upon
        // a valid write.
        let filled = unsafe { self.data.get_unchecked(..self.len()) };
        // SAFETY: Everything up to `self.filled` is guaranteed to be
        // initialized. Also, since `MaybeUninit<u8>` and `u8` have the same
        // representation, we can cast from `&[MaybeUninit<u8>]` to `&[u8]`.
        // Finally, the `BorrowedBuffer` API specifically guarantees that
        // all writes to `self.data` are valid UTF-8.
        unsafe {
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(
                filled.as_ptr().cast::<u8>(),
                self.len(),
            ))
        }
    }

    /// Returns the available space in this buffer.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    fn available(&mut self) -> &mut [MaybeUninit<u8>] {
        // SAFETY: `self.len()` is guaranteed to be a valid offset for the
        // start of a slice into `self.data`.
        unsafe { self.data.get_unchecked_mut(self.len()..) }
    }

    /// Return the length of the "filled" in bytes.
    ///
    /// This is always equivalent to the length of the slice returned by
    /// `BorrowedBuffer::filled`.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    fn len(&self) -> usize {
        usize::from(self.filled)
    }

    /// Return the total unused capacity available to this buffer.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    #[allow(dead_code)]
    fn available_capacity(&self) -> usize {
        self.capacity() - self.len()
    }

    /// Return the total capacity available to this buffer.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    #[allow(dead_code)]
    fn capacity(&self) -> usize {
        self.data.len()
    }
}

/// Construct a borrowed buffer for writing into a `&mut [u8]`.
///
/// This typically isn't useful on its own since `&mut [u8]` is already
/// guaranteed to be initialized and doesn't require handling with
/// care. However, this is useful when using with APIs that expect a
/// `BorrowedBuffer`.
///
/// # Panics
///
/// When the slice exceeds the maximum capacity supported by `BorrowedBuffer`.
impl<'data> From<&'data mut [u8]> for BorrowedBuffer<'data> {
    #[cfg_attr(feature = "perf-inline", inline(always))]
    fn from(data: &'data mut [u8]) -> BorrowedBuffer<'data> {
        assert!(
            data.len() <= MAX_CAPACITY,
            "borrowed buffer only supports {MAX_CAPACITY} bytes"
        );
        let len = data.len();
        let data: *mut MaybeUninit<u8> = data.as_mut_ptr().cast();
        // SAFETY: The length hasn't changed and `MaybeUninit<u8>` and `u8`
        // are guaranteed to have the same representation in memory.
        let data = unsafe { core::slice::from_raw_parts_mut(data, len) };
        BorrowedBuffer { data, filled: 0 }
    }
}

/// Construct a borrowed buffer directly from a slice of uninitialized data.
///
/// # Panics
///
/// When the slice exceeds the maximum capacity supported by `BorrowedBuffer`.
impl<'data> From<&'data mut [MaybeUninit<u8>]> for BorrowedBuffer<'data> {
    #[cfg_attr(feature = "perf-inline", inline(always))]
    fn from(data: &'data mut [MaybeUninit<u8>]) -> BorrowedBuffer<'data> {
        assert!(
            data.len() <= MAX_CAPACITY,
            "borrowed buffer only supports {MAX_CAPACITY} bytes"
        );
        BorrowedBuffer { data, filled: 0 }
    }
}

/// Construct a borrowed buffer directly from an array of uninitialized data.
///
/// # Panics
///
/// When the array exceeds the maximum capacity supported by `BorrowedBuffer`.
impl<'data, const N: usize> From<&'data mut [MaybeUninit<u8>; N]>
    for BorrowedBuffer<'data>
{
    #[cfg_attr(feature = "perf-inline", inline(always))]
    fn from(data: &'data mut [MaybeUninit<u8>; N]) -> BorrowedBuffer<'data> {
        BorrowedBuffer::from(&mut data[..])
    }
}

/// Returns the number of digits in the decimal representation of `n`.
///
/// This calculation to figure out the number of digits to write in `n` is
/// the expense we incur by having our printers write forwards. If we instead
/// wrote backwards, then we could omit this calculation. I ended up choosing
/// this design because 1) most integer writes in datetime (not span) printing
/// are fixed 2 or 4 digits, and don't require this extra computation and 2)
/// writing backwards just overall seems like a pain.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn digits(n: u64) -> u8 {
    // It's faster by about 1-5% (on microbenchmarks) to make this more
    // branch-y and specialize the smaller and more common integers in lieu
    // of calling `ilog10`.
    match n {
        0..=9 => 1,
        10..=99 => 2,
        100..=999 => 3,
        1000..=9999 => 4,
        _ => n.ilog10() as u8 + 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_str_array() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();
        bbuf.write_str("Hello, world!");
        assert_eq!(bbuf.filled(), "Hello, world!");
        let buf = bbuf.into_filled();
        assert_eq!(buf, "Hello, world!");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn write_str_string() {
        let mut buf = alloc::string::String::with_capacity(100);
        BorrowedBuffer::with_string_spare_capacity(&mut buf, |bbuf| {
            bbuf.write_str("Hello, world!");
        });
        assert_eq!(buf, "Hello, world!");
    }

    #[test]
    fn write_int_array() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_int(0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0");
        }

        bbuf.clear();
        bbuf.write_int(1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "1");
        }

        bbuf.clear();
        bbuf.write_int(10);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "10");
        }

        bbuf.clear();
        bbuf.write_int(100);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "100");
        }

        bbuf.clear();
        bbuf.write_int(u64::MAX);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "18446744073709551615");
        }
    }

    #[test]
    fn write_int_pad2() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_int_pad2(0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "00");
        }

        bbuf.clear();
        bbuf.write_int_pad2(1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "01");
        }

        bbuf.clear();
        bbuf.write_int_pad2(10);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "10");
        }

        bbuf.clear();
        bbuf.write_int_pad2(99);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "99");
        }
    }

    #[test]
    #[should_panic]
    fn write_int_pad2_panic() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();
        // technically unspecified behavior,
        // but should not result in undefined behavior.
        bbuf.write_int_pad4(u64::MAX);
    }

    #[test]
    fn write_int_pad4() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_int_pad4(0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0000");
        }

        bbuf.clear();
        bbuf.write_int_pad4(1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0001");
        }

        bbuf.clear();
        bbuf.write_int_pad4(10);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0010");
        }

        bbuf.clear();
        bbuf.write_int_pad4(99);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0099");
        }

        bbuf.clear();
        bbuf.write_int_pad4(999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0999");
        }

        bbuf.clear();
        bbuf.write_int_pad4(9999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "9999");
        }
    }

    #[test]
    #[should_panic]
    fn write_int_pad4_panic() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();
        // technically unspecified behavior,
        // but should not result in undefined behavior.
        bbuf.write_int_pad4(u64::MAX);
    }

    #[test]
    fn write_int_pad6() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_int_pad6(0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000000");
        }

        bbuf.clear();
        bbuf.write_int_pad6(1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000001");
        }

        bbuf.clear();
        bbuf.write_int_pad6(10);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000010");
        }

        bbuf.clear();
        bbuf.write_int_pad6(99);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000099");
        }

        bbuf.clear();
        bbuf.write_int_pad6(999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000999");
        }

        bbuf.clear();
        bbuf.write_int_pad6(9999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "009999");
        }

        bbuf.clear();
        bbuf.write_int_pad6(999999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "999999");
        }
    }

    #[test]
    #[should_panic]
    fn write_int_pad6_panic() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();
        // technically unspecified behavior,
        // but should not result in undefined behavior.
        bbuf.write_int_pad6(u64::MAX);
    }

    #[test]
    fn write_int_pad_zero() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_int_pad(0, b'0', 0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0");
        }

        bbuf.clear();
        bbuf.write_int_pad(0, b'0', 1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0");
        }

        bbuf.clear();
        bbuf.write_int_pad(0, b'0', 2);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "00");
        }

        bbuf.clear();
        bbuf.write_int_pad(0, b'0', 20);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "00000000000000000000");
        }

        bbuf.clear();
        // clamped to 20
        bbuf.write_int_pad(0, b'0', 21);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "00000000000000000000");
        }

        bbuf.clear();
        bbuf.write_int_pad(0, b' ', 2);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, " 0");
        }
    }

    #[test]
    fn write_int_pad_one() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_int_pad(1, b'0', 0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "1");
        }

        bbuf.clear();
        bbuf.write_int_pad(1, b'0', 1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "1");
        }

        bbuf.clear();
        bbuf.write_int_pad(1, b'0', 2);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "01");
        }

        bbuf.clear();
        bbuf.write_int_pad(1, b'0', 20);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "00000000000000000001");
        }

        bbuf.clear();
        // clamped to 20
        bbuf.write_int_pad(1, b'0', 21);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "00000000000000000001");
        }

        bbuf.clear();
        bbuf.write_int_pad(1, b' ', 2);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, " 1");
        }
    }

    #[test]
    fn write_int_pad_max() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_int_pad(u64::MAX, b'0', 0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "18446744073709551615");
        }

        bbuf.clear();
        bbuf.write_int_pad(u64::MAX, b'0', 1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "18446744073709551615");
        }

        bbuf.clear();
        bbuf.write_int_pad(u64::MAX, b'0', 2);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "18446744073709551615");
        }

        bbuf.clear();
        bbuf.write_int_pad(u64::MAX, b'0', 20);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "18446744073709551615");
        }

        bbuf.clear();
        // clamped to 20
        bbuf.write_int_pad(u64::MAX, b'0', 21);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "18446744073709551615");
        }

        bbuf.clear();
        bbuf.write_int_pad(u64::MAX, b' ', 2);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "18446744073709551615");
        }
    }

    #[test]
    #[should_panic]
    fn write_int_pad_non_ascii_panic() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();
        bbuf.write_int_pad(0, 0xFF, 0);
    }

    #[test]
    #[should_panic]
    fn write_int_pad_insufficient_capacity_panic() {
        let mut buf = ArrayBuffer::<19>::default();
        let mut bbuf = buf.as_borrowed();
        bbuf.write_int_pad(0, b'0', 20);
    }

    #[test]
    fn write_fraction_no_precision() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_fraction(None, 0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "");
        }

        bbuf.clear();
        bbuf.write_fraction(None, 1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000000001");
        }

        bbuf.clear();
        bbuf.write_fraction(None, 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "123");
        }

        bbuf.clear();
        bbuf.write_fraction(None, 999_999_999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "999999999");
        }
    }

    #[test]
    fn write_fraction_precision() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();

        bbuf.write_fraction(Some(0), 0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(1), 0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "0");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(9), 0);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000000000");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(0), 1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(9), 1);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "000000001");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(0), 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(1), 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "1");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(2), 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "12");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(3), 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "123");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(6), 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "123000");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(9), 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "123000000");
        }

        bbuf.clear();
        // clamps to 9
        bbuf.write_fraction(Some(10), 123_000_000);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "123000000");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(0), 999_999_999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(1), 999_999_999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "9");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(3), 999_999_999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "999");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(6), 999_999_999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "999999");
        }

        bbuf.clear();
        bbuf.write_fraction(Some(9), 999_999_999);
        {
            let buf = bbuf.into_filled();
            assert_eq!(buf, "999999999");
        }
    }

    #[test]
    #[should_panic]
    fn write_fraction_too_big_panic() {
        let mut buf = ArrayBuffer::<100>::default();
        let mut bbuf = buf.as_borrowed();
        bbuf.write_fraction(None, 1_000_000_000);
    }
}
