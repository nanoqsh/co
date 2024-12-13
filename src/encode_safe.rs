/// A trait for encoding values into a buffer.
pub trait Encode {
    /// Returns byte size of encodable value.
    fn size(&self) -> usize;

    /// Encodes the value to the buffer.
    fn encode_checked(&self, buf: &mut [u8]);
}

impl<E> Encode for &E
where
    E: Encode + ?Sized,
{
    #[inline]
    fn size(&self) -> usize {
        (**self).size()
    }

    #[inline]
    fn encode_checked(&self, buf: &mut [u8]) {
        (**self).encode_checked(buf)
    }
}

impl Encode for () {
    #[inline]
    fn size(&self) -> usize {
        0
    }

    #[inline]
    fn encode_checked(&self, buf: &mut [u8]) {
        debug_assert!(buf.is_empty(), "trait invariant violation");
    }
}

impl Encode for [u8] {
    #[inline]
    fn size(&self) -> usize {
        self.len()
    }

    #[inline]
    fn encode_checked(&self, buf: &mut [u8]) {
        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        buf.copy_from_slice(self);
    }
}

impl<const N: usize> Encode for [u8; N] {
    #[inline]
    fn size(&self) -> usize {
        self[..].size()
    }

    #[inline]
    fn encode_checked(&self, buf: &mut [u8]) {
        self[..].encode_checked(buf)
    }
}

impl Encode for u8 {
    #[inline]
    fn size(&self) -> usize {
        size_of::<Self>()
    }

    #[inline]
    fn encode_checked(&self, buf: &mut [u8]) {
        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        buf[0] = *self;
    }
}

struct Then<A, B>(A, B);

impl<A, B> Encode for Then<A, B>
where
    A: Encode,
    B: Encode,
{
    #[inline]
    fn size(&self) -> usize {
        let Self(a, b) = self;
        a.size() + b.size()
    }

    #[inline]
    fn encode_checked(&self, buf: &mut [u8]) {
        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        let Self(a, b) = self;

        let (head, tail) = buf.split_at_mut(a.size());

        a.encode_checked(head);
        b.encode_checked(tail);
    }
}

#[derive(Clone, Copy)]
struct Be<T>(T);

#[derive(Clone, Copy)]
struct Le<T>(T);

trait Bytes<const N: usize>: Copy {
    fn bytes(self) -> [u8; N];
}

impl Bytes<{ size_of::<u16>() }> for Be<u16> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u16>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u16>() }> for Le<u16> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u16>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<u32>() }> for Be<u32> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u32>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u32>() }> for Le<u32> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u32>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<u64>() }> for Be<u64> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u64>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u64>() }> for Le<u64> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u64>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<u128>() }> for Be<u128> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u128>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u128>() }> for Le<u128> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<u128>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<usize>() }> for Be<usize> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<usize>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<usize>() }> for Le<usize> {
    #[inline]
    fn bytes(self) -> [u8; size_of::<usize>()] {
        self.0.to_le_bytes()
    }
}

struct Plain<B, const N: usize>(B);

impl<B, const N: usize> Encode for Plain<B, N>
where
    B: Bytes<N>,
{
    #[inline]
    fn size(&self) -> usize {
        N
    }

    #[inline]
    fn encode_checked(&self, buf: &mut [u8]) {
        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        buf.copy_from_slice(&self.0.bytes());
    }
}

/// An extension trait for [encodable](Encode) types.
///
/// This trait allows for appending an encoding sequence
/// by encodable values.
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
///     .u8(b'l')    // a special method for u8 type
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
    /// ().u16_be(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0, 0xFF]);
    /// ```
    #[inline]
    fn u16_be(self, u: u16) -> impl Encode {
        Then(self, Plain(Be(u)))
    }

    /// Appends a `u16` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 2];
    /// ().u16_le(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0xFF, 0]);
    /// ```
    #[inline]
    fn u16_le(self, u: u16) -> impl Encode {
        Then(self, Plain(Le(u)))
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
    /// ().u32_be(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0, 0, 0, 0xFF]);
    /// ```
    #[inline]
    fn u32_be(self, u: u32) -> impl Encode {
        Then(self, Plain(Be(u)))
    }

    /// Appends a `u32` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 4];
    /// ().u32_le(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0xFF, 0, 0, 0]);
    /// ```
    #[inline]
    fn u32_le(self, u: u32) -> impl Encode {
        Then(self, Plain(Le(u)))
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
    /// ().u64_be(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0, 0, 0, 0, 0, 0, 0, 0xFF]);
    /// ```
    #[inline]
    fn u64_be(self, u: u64) -> impl Encode {
        Then(self, Plain(Be(u)))
    }

    /// Appends a `u64` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; 8];
    /// ().u64_le(255).encode(&mut code);
    ///
    /// assert_eq!(code, [0xFF, 0, 0, 0, 0, 0, 0, 0]);
    /// ```
    #[inline]
    fn u64_le(self, u: u64) -> impl Encode {
        Then(self, Plain(Le(u)))
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
    /// ().u128_be(255).encode(&mut code);
    ///
    /// assert_eq!(code, [
    ///     0, 0, 0, 0, 0, 0, 0, 0,
    ///     0, 0, 0, 0, 0, 0, 0, 0xFF,
    /// ]);
    /// ```
    #[inline]
    fn u128_be(self, u: u128) -> impl Encode {
        Then(self, Plain(Be(u)))
    }

    /// Appends a `u128` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
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
        Then(self, Plain(Le(u)))
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
    /// ().usize_be(255).encode(&mut code);
    ///
    /// assert_eq!(code.last(), Some(&0xFF));
    /// ```
    #[inline]
    fn usize_be(self, u: usize) -> impl Encode {
        Then(self, Plain(Be(u)))
    }

    /// Appends a `usize` value to the encodable
    /// sequence with little-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use co::EncodeExt;
    ///
    /// let mut code = [0; size_of::<usize>()];
    /// ().usize_le(255).encode(&mut code);
    ///
    /// assert_eq!(code.first(), Some(&0xFF));
    /// ```
    #[inline]
    fn usize_le(self, u: usize) -> impl Encode {
        Then(self, Plain(Le(u)))
    }

    /// Encodes the sequence and writes the result into the buffer.
    ///
    /// Returns [`Ok`] with a slice of the written data if the buffer size matches the
    /// size of the encoded sequence. Otherwise, it returns [`Err`] with the required
    /// size. In case of an error, expand the buffer to the required size and call this
    /// method again.
    ///
    /// Note, for more optimal buffer allocation, you can preallocate more than
    /// necessary for the sequence, but this method must be called with *exactly* the
    /// required length. The implementation does not truncate the buffer if needed;
    /// this is the caller responsibility.
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
    #[inline]
    fn encode(self, buf: &mut [u8]) -> Result<(), usize> {
        let size = self.size();
        if size == buf.len() {
            self.encode_checked(buf);
            Ok(())
        } else {
            Err(size)
        }
    }
}

impl<E> EncodeExt for E where E: Encode {}
