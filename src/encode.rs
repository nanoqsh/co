use {
    crate::writer::Writer,
    core::{mem::MaybeUninit, slice},
};

/// A trait for encoding values into a buffer.
///
/// # Note
///
/// This trait is intended for low-level implementation, which is also unsafe to
/// call. Instead, use the [`EncodeExt`] trait, which allows safely constructing
/// encodable sequences.
///
/// # Safety
///
/// This trait is unsafe because unsafe code relies on the safety invariants upheld
/// by implementations. To implement this trait correctly, the following invariants
/// must be maintained:
///
/// * `size` must always return the exact number of bytes required to encode
///   the value. In particular, `size` must consistently return the same value if
///   `self` has not changed.
///
/// * `encode_unchecked` must initialize exactly `size` bytes in the passed buffer.
pub unsafe trait Encode {
    /// Returns byte size of encodable value.
    ///
    /// # Note
    ///
    /// Although the [`Size`] type contains a `usize` and checks for overflow in
    /// its [expand](Size::expand) method, the [`Encode`] trait cannot encode a
    /// value larger than `isize::MAX` bytes sequentially. However, it is
    /// impossible to create a [`Writer`] with a buffer that exceeds this limit, so
    /// calling [`encode_unchecked`](Encode::encode_unchecked) with such a size is
    /// also impossible.
    fn size(&self) -> Size;

    /// Encodes the value to the buffer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `w.remaining() >= self.size()`.
    unsafe fn encode_unchecked(&self, w: &mut Writer);
}

/// A wrapper around `usize` representing a size value.
///
/// This type works closely with the [`Encode`] trait, as the [`size`](Encode::size)
/// method returns a value representing the byte size required for encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Size(pub usize);

impl Size {
    /// Expands the current size by adding another [`Size`] value.
    ///
    /// # Panics
    ///
    /// This method will panic if the addition results in an overflow of the
    /// `usize` type.
    #[inline]
    pub fn expand(self, Self(more): Self) -> Self {
        Self(usize::checked_add(self.0, more).expect("size cannot overflow"))
    }
}

// SAFETY: delegate to inner impl
unsafe impl<E> Encode for &E
where
    E: Encode + ?Sized,
{
    #[inline]
    fn size(&self) -> Size {
        (**self).size()
    }

    #[inline]
    unsafe fn encode_unchecked(&self, w: &mut Writer) {
        // SAFETY: delegate to inner impl
        unsafe { (**self).encode_unchecked(w) }
    }
}

// SAFETY: encode empty buffer with zero size
unsafe impl Encode for () {
    #[inline]
    fn size(&self) -> Size {
        Size(0)
    }

    #[inline]
    unsafe fn encode_unchecked(&self, _: &mut Writer) {}
}

// SAFETY: copy a slice into the buffer
unsafe impl Encode for [u8] {
    #[inline]
    fn size(&self) -> Size {
        Size(self.len())
    }

    #[inline]
    unsafe fn encode_unchecked(&self, w: &mut Writer) {
        // SAFETY: `w.remaining() >= self.len()`
        unsafe { w.write_slice(self) }
    }
}

// SAFETY: delegate to slice impl
unsafe impl<const N: usize> Encode for [u8; N] {
    #[inline]
    fn size(&self) -> Size {
        self[..].size()
    }

    #[inline]
    unsafe fn encode_unchecked(&self, w: &mut Writer) {
        // SAFETY: delegate to slice impl
        unsafe { self[..].encode_unchecked(w) }
    }
}

// SAFETY: encode a byte, `size` is 1
unsafe impl Encode for u8 {
    #[inline]
    fn size(&self) -> Size {
        Size(size_of::<Self>())
    }

    #[inline]
    unsafe fn encode_unchecked(&self, w: &mut Writer) {
        // SAFETY: `w.remaining() >= 1`
        unsafe { w.write_byte(*self) }
    }
}

struct Then<A, B>(A, B);

// SAFETY:
// * delegate impls to parts
// * write to the buffer
//   `a.size()` bytes and `b.size()` bytes
unsafe impl<A, B> Encode for Then<A, B>
where
    A: Encode,
    B: Encode,
{
    #[inline]
    fn size(&self) -> Size {
        let Self(a, b) = self;
        a.size().expand(b.size())
    }

    #[inline]
    unsafe fn encode_unchecked(&self, w: &mut Writer) {
        let Self(a, b) = self;

        // SAFETY: `w.remaining() >= a.size()`
        unsafe { a.encode_unchecked(w) }

        // SAFETY: `w.remaining() >= b.size()`
        unsafe { b.encode_unchecked(w) }
    }
}

/// An extension trait for [encodable](Encode) types.
///
/// This trait allows for appending an encoding sequence
/// by encodable values.
///
/// Integers are encoded in big-endian byte order by default.
/// To encode integers in little-endian order use [`LittleEndianEncodeExt`].
///
/// # Examples
///
/// ```rust
/// use co::EncodeExt;
///
/// let mut code = [0; 5];
///
/// // Encode a sequence of bytes to the `code` buffer
/// b'h'
///     .then(b"el") // `then` accepts any encodable
///     .u8(b'l')    // `u8` is a special method for u8 type
///     .u8(b'o')
///     .encode(&mut code);
///
/// assert_eq!(&code, b"hello");
/// ```
pub trait EncodeExt: Encode + Sized {
    /// ​​Sequentially encodes two values.
    ///
    /// This method allows chaining two encodable items, producing
    /// a composite value that implements the [`Encode`] trait.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 3];
    ///
    /// b'u'
    ///     .then(b'w')
    ///     .then(b'u')
    ///     .encode(&mut code);
    ///
    /// assert_eq!(&code, b"uwu");
    /// ```
    #[inline]
    fn then<E>(self, e: E) -> impl Encode
    where
        E: Encode,
    {
        Then(self, e)
    }

    /// Appends a `u8` value to the encodable sequence.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0];
    /// ().u8(37).encode(&mut code);
    ///
    /// assert_eq!(code, [37]);
    /// ```
    #[inline]
    fn u8(self, u: u8) -> impl Encode {
        Then(self, u)
    }

    /// Appends a `u16` value to the encodable
    /// sequence with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 2];
    /// ().u16(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0, 0xFF]);
    /// ```
    #[inline]
    fn u16(self, u: u16) -> impl Encode {
        Then(self, u16::to_be_bytes(u))
    }

    /// Appends a `u32` value to the encodable
    /// sequence with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 4];
    /// ().u32(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0, 0, 0, 0xFF]);
    /// ```
    #[inline]
    fn u32(self, u: u32) -> impl Encode {
        Then(self, u32::to_be_bytes(u))
    }

    /// Appends a `u64` value to the encodable
    /// sequence with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 8];
    /// ().u64(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0, 0, 0, 0, 0, 0, 0, 0xFF]);
    /// ```
    #[inline]
    fn u64(self, u: u64) -> impl Encode {
        Then(self, u64::to_be_bytes(u))
    }

    /// Appends a `u128` value to the encodable
    /// sequence with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 16];
    /// ().u128(255).encode(&mut code);
    ///
    /// assert_eq!(code, [
    ///     0, 0, 0, 0, 0, 0, 0, 0,
    ///     0, 0, 0, 0, 0, 0, 0, 0xFF,
    /// ]);
    /// ```
    #[inline]
    fn u128(self, u: u128) -> impl Encode {
        Then(self, u128::to_be_bytes(u))
    }

    /// Appends a `usize` value to the encodable
    /// sequence with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; size_of::<usize>()];
    /// ().usize(255).encode(&mut code);
    ///
    /// assert_eq!(code.last(), Some(&0xFF));
    /// ```
    #[inline]
    fn usize(self, u: usize) -> impl Encode {
        Then(self, usize::to_be_bytes(u))
    }

    /// Encodes the sequence and writes the result into the buffer.
    ///
    /// Returns [`Ok`] with a slice of the written data if the buffer size matches the
    /// size of the encoded sequence. Otherwise, it returns [`Err`] with the required
    /// size. In case of an error, expand the buffer to the required size and call this
    /// method again.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use {core::mem::MaybeUninit, co::EncodeExt};
    ///
    /// let mut buf = [MaybeUninit::uninit(); 3];
    /// let code = b"uwu".encode(&mut buf);
    ///
    /// // The buffer length matches the size of the encoded sequence
    /// assert!(code.is_ok_and(|code| code == b"uwu"));
    ///
    /// let code = b"uwu".encode(&mut buf[..2]);
    ///
    /// // Error: buffer length must be equal to 3
    /// assert_eq!(code, Err(3));
    /// ```
    ///
    /// # Note
    ///
    /// For more optimal buffer allocation, you can preallocate more than
    /// necessary for the sequence, but this method must be called with *exactly* the
    /// required length. The implementation does not truncate the buffer if needed;
    /// this is the caller responsibility.
    #[inline]
    fn encode<B>(self, buf: &mut B) -> Result<&mut [u8], usize>
    where
        B: Buffer + ?Sized,
    {
        let buf = buf.buffer();
        let Size(size) = self.size();
        if size == buf.len() {
            let mut w = Writer::new(buf);

            debug_assert_eq!(
                w.remaining(),
                size,
                "the buffer must not be filled at the beginning",
            );

            // SAFETY: `w.remaining() == self.size()`
            unsafe { self.encode_unchecked(&mut w) }

            debug_assert_eq!(
                w.remaining(),
                0,
                "afterward the buffer must be completely filled",
            );

            // SAFETY:
            // * since the `Encode` implementation writes
            //   exactly `size` bytes to the buffer, and
            //   the buffer size is exactly `size` bytes
            //   (checked by the condition)
            //   the entire buffer has been initialized
            let init = unsafe { w.init() };

            Ok(init)
        } else {
            Err(size)
        }
    }
}

impl<E> EncodeExt for E where E: Encode {}

/// Extension trait for encoding sequences with little-endian byte ordering.
pub trait LittleEndianEncodeExt: Encode + Sized {
    /// Appends a `u16` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::{EncodeExt, LittleEndianEncodeExt};
    ///
    /// let mut code = [0; 2];
    /// ().u16_le(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0xFF, 0]);
    /// ```
    #[inline]
    fn u16_le(self, u: u16) -> impl Encode {
        Then(self, u16::to_le_bytes(u))
    }

    /// Appends a `u32` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::{EncodeExt, LittleEndianEncodeExt};
    ///
    /// let mut code = [0; 4];
    /// ().u32_le(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0xFF, 0, 0, 0]);
    /// ```
    #[inline]
    fn u32_le(self, u: u32) -> impl Encode {
        Then(self, u32::to_le_bytes(u))
    }

    /// Appends a `u64` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::{EncodeExt, LittleEndianEncodeExt};
    ///
    /// let mut code = [0; 8];
    /// ().u64_le(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0xFF, 0, 0, 0, 0, 0, 0, 0]);
    /// ```
    #[inline]
    fn u64_le(self, u: u64) -> impl Encode {
        Then(self, u64::to_le_bytes(u))
    }

    /// Appends a `u128` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::{EncodeExt, LittleEndianEncodeExt};
    ///
    /// let mut code = [0; 16];
    /// ().u128_le(255).encode(&mut code);
    ///
    /// assert_eq!(code, [
    ///     0xFF, 0, 0, 0, 0, 0, 0, 0,
    ///     0, 0, 0, 0, 0, 0, 0, 0,
    /// ]);
    /// ```
    #[inline]
    fn u128_le(self, u: u128) -> impl Encode {
        Then(self, u128::to_le_bytes(u))
    }

    /// Appends a `usize` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::{EncodeExt, LittleEndianEncodeExt};
    ///
    /// let mut code = [0; size_of::<usize>()];
    /// ().usize_le(255).encode(&mut code);
    ///
    /// assert_eq!(code.first(), Some(&0xFF));
    /// ```
    #[inline]
    fn usize_le(self, u: usize) -> impl Encode {
        Then(self, usize::to_le_bytes(u))
    }
}

impl<E> LittleEndianEncodeExt for E where E: Encode {}

/// A trait for accessing a maybe uninitialized mutable buffer.
pub trait Buffer {
    /// Accesses the buffer's memory.
    fn buffer(&mut self) -> &mut [MaybeUninit<u8>];
}

impl Buffer for [MaybeUninit<u8>] {
    #[inline]
    fn buffer(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }
}

impl<const N: usize> Buffer for [MaybeUninit<u8>; N] {
    #[inline]
    fn buffer(&mut self) -> &mut [MaybeUninit<u8>] {
        self
    }
}

impl Buffer for [u8] {
    #[inline]
    fn buffer(&mut self) -> &mut [MaybeUninit<u8>] {
        // This operation is basically safe
        fn slice_mut_as_init(s: &mut [u8]) -> &mut [MaybeUninit<u8>] {
            // SAFETY:
            // * rebuild the slice by erasing information about initialization,
            //   here the `[MaybeUninit<u8>]` is fully initializated, but
            //   it is ok for `MaybeUninit<u8>` to be initializated
            unsafe { slice::from_raw_parts_mut(s.as_mut_ptr().cast(), s.len()) }
        }

        slice_mut_as_init(self)
    }
}

impl<const N: usize> Buffer for [u8; N] {
    #[inline]
    fn buffer(&mut self) -> &mut [MaybeUninit<u8>] {
        self[..].buffer()
    }
}
