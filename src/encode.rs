use core::{mem::MaybeUninit, slice};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Size(pub usize);

impl Size {
    #[inline]
    pub fn expand(self, more: usize) -> Self {
        Self(usize::checked_add(self.0, more).expect("size cannot overflow"))
    }
}

impl PartialEq<usize> for Size {
    #[inline]
    fn eq(&self, &rhs: &usize) -> bool {
        self.0 == rhs
    }
}

/// A trait for encoding values into a buffer.
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
/// * `encode_unchecked` must initialize *all* bytes in the passed buffer.
pub unsafe trait Encode {
    /// Returns byte size of encodable value.
    fn size(&self) -> Size;

    /// Encodes the value to the buffer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `self.size() == buf.len()`.
    ///
    /// Note that even if the buffer length exceeds the required size for encoding
    /// the value, the implementation still relies on strict equality. Passing
    /// a longer buffer may also lead to undefined behavior.
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]);
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
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]) {
        // SAFETY: delegate to inner impl
        unsafe { (**self).encode_unchecked(buf) }
    }
}

// SAFETY: encode empty buffer with zero size
unsafe impl Encode for () {
    #[inline]
    fn size(&self) -> Size {
        Size(0)
    }

    #[inline]
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]) {
        debug_assert!(buf.is_empty(), "trait invariant violation");
    }
}

// SAFETY: copy a slice into the buffer
unsafe impl Encode for [u8] {
    #[inline]
    fn size(&self) -> Size {
        Size(self.len())
    }

    #[inline]
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]) {
        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        let bufptr: *mut u8 = buf.as_mut_ptr().cast();

        // SAFETY:
        // * copy all bytes from the slice
        // * slice and `buf` are nonoverlapping since `buf` passed by `&mut [_]`
        unsafe { bufptr.copy_from_nonoverlapping(self.as_ptr(), self.len()) }
    }
}

// SAFETY: delegate to slice impl
unsafe impl<const N: usize> Encode for [u8; N] {
    #[inline]
    fn size(&self) -> Size {
        self[..].size()
    }

    #[inline]
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]) {
        // SAFETY: delegate to slice impl
        unsafe { self[..].encode_unchecked(buf) }
    }
}

// SAFETY: encode a byte, `size` is 1
unsafe impl Encode for u8 {
    #[inline]
    fn size(&self) -> Size {
        Size(size_of::<Self>())
    }

    #[inline]
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]) {
        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        // SAFETY: `buf.len()` == 1
        unsafe {
            *buf.get_unchecked_mut(0) = MaybeUninit::new(*self);
        }
    }
}

struct Then<A, B>(A, B);

// SAFETY:
// * split `buf` into two parts at `a.size()`
// * delegate impls to parts
unsafe impl<A, B> Encode for Then<A, B>
where
    A: Encode,
    B: Encode,
{
    #[inline]
    fn size(&self) -> Size {
        let Self(a, b) = self;
        let Size(b_size) = b.size();
        a.size().expand(b_size)
    }

    #[inline]
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]) {
        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        let Self(a, b) = self;

        let Size(a_size) = a.size();

        // SAFETY: `buf` length == `a.size() + b.size()`, so it can be splitted at `a.size()`
        let (head, tail) = unsafe { buf.split_at_mut_unchecked(a_size) };

        // SAFETY: head length == `a.size()`
        unsafe { a.encode_unchecked(head) }

        // SAFETY: tail length == `b.size()`
        unsafe { b.encode_unchecked(tail) }
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
    fn bytes(self) -> [u8; size_of::<u16>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u16>() }> for Le<u16> {
    fn bytes(self) -> [u8; size_of::<u16>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<u32>() }> for Be<u32> {
    fn bytes(self) -> [u8; size_of::<u32>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u32>() }> for Le<u32> {
    fn bytes(self) -> [u8; size_of::<u32>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<u64>() }> for Be<u64> {
    fn bytes(self) -> [u8; size_of::<u64>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u64>() }> for Le<u64> {
    fn bytes(self) -> [u8; size_of::<u64>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<u128>() }> for Be<u128> {
    fn bytes(self) -> [u8; size_of::<u128>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<u128>() }> for Le<u128> {
    fn bytes(self) -> [u8; size_of::<u128>()] {
        self.0.to_le_bytes()
    }
}

impl Bytes<{ size_of::<usize>() }> for Be<usize> {
    fn bytes(self) -> [u8; size_of::<usize>()] {
        self.0.to_be_bytes()
    }
}

impl Bytes<{ size_of::<usize>() }> for Le<usize> {
    fn bytes(self) -> [u8; size_of::<usize>()] {
        self.0.to_le_bytes()
    }
}

struct Plain<B, const N: usize>(B);

// SAFETY:
// * initialze `N` bytes, so `size` returns exatly `N`
// * copy bytes from `Bytes` trait impls, even when `Bytes`
//   is a safe trait, it returns fully initialized bytes,
//   since the array type guarantees initialization.
//   (actually `Bytes` can also be public since custom impl
//   doesn't break the safety)
unsafe impl<B, const N: usize> Encode for Plain<B, N>
where
    B: Bytes<N>,
{
    #[inline]
    fn size(&self) -> Size {
        Size(N)
    }

    #[inline]
    unsafe fn encode_unchecked(&self, buf: &mut [MaybeUninit<u8>]) {
        // SAFETY: the caller must ensure `s.len() == N`
        unsafe fn as_array_mut<T, const N: usize>(s: &mut [T]) -> &mut [T; N] {
            debug_assert_eq!(s.len(), N, "lengths don't match");

            let sptr: *mut [T; N] = s.as_mut_ptr().cast();

            // SAFETY:
            // * cast the slice with `N` length
            //   to an array with `N` length
            unsafe { &mut *sptr }
        }

        debug_assert_eq!(self.size(), buf.len(), "trait invariant violation");

        // SAFETY: `s.len() == N` by outer caller invariant
        let array = unsafe { as_array_mut(buf) };

        *array = self.0.bytes().map(MaybeUninit::new);
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
    fn encode<B>(self, buf: &mut B) -> Result<&mut [u8], usize>
    where
        B: Buffer + ?Sized,
    {
        let buf = buf.buffer();
        let Size(size) = self.size();
        if size == buf.len() {
            // SAFETY: `buf` length is checked above
            unsafe { self.encode_unchecked(buf) }

            // SAFETY:
            // * by `Encode` trait invariant all bytes of `buf` was initialized,
            //   so cast `&mut [MaybeUninit<u8>]` to `&mut [u8]`
            let init = unsafe { slice::from_raw_parts_mut(buf.as_mut_ptr().cast(), buf.len()) };

            Ok(init)
        } else {
            Err(size)
        }
    }
}

impl<E> EncodeExt for E where E: Encode {}

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
