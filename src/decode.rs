use crate::reader::Reader;

/// A trait for decoding values from a buffer.
///
/// # Note
///
/// This trait is intended for low-level implementations. Use the
/// [decoder](Decoder) for convenient decoding of byte sequences.
pub trait Decode<'buf>: Sized {
    fn decode(r: &mut Reader<'buf>) -> Option<Self>;
}

impl Decode<'_> for () {
    #[inline]
    fn decode(_: &mut Reader<'_>) -> Option<Self> {
        Some(())
    }
}

impl Decode<'_> for u8 {
    #[inline]
    fn decode(r: &mut Reader<'_>) -> Option<Self> {
        r.read_byte()
    }
}

impl<'buf, const N: usize> Decode<'buf> for &'buf [u8; N] {
    #[inline]
    fn decode(r: &mut Reader<'buf>) -> Option<Self> {
        r.read_array()
    }
}

impl<'buf, const N: usize> Decode<'buf> for [u8; N] {
    #[inline]
    fn decode(r: &mut Reader<'buf>) -> Option<Self> {
        r.read_array().copied()
    }
}

/// The [`Decode`] trait extension to decode a value with some [state](DecodeWith::State).
pub trait DecodeWith<'buf>: Sized {
    type State;

    fn decode_with(r: &mut Reader<'buf>, state: Self::State) -> Option<Self>;
}

impl<'buf, D> DecodeWith<'buf> for D
where
    D: Decode<'buf>,
{
    type State = ();

    #[inline]
    fn decode_with(r: &mut Reader<'buf>, _: Self::State) -> Option<Self> {
        Self::decode(r)
    }
}

impl<'buf> DecodeWith<'buf> for &'buf [u8] {
    type State = usize;

    #[inline]
    fn decode_with(r: &mut Reader<'buf>, len: Self::State) -> Option<Self> {
        r.read_slice(len)
    }
}

/// The type to [decode](Decode) data from a buffer.
///
/// # Examples
///
/// ```
/// # fn d() -> Option<()> {
/// use co::AsDecoder;
///
/// let mut dec = [0, 1, 2, 1, 0].as_decoder();
///
/// let a = dec.u16()?;
/// assert_eq!(a, 1);
///
/// let b = dec.u8()?;
/// assert_eq!(b, 2);
///
/// let c = dec.u16()?;
/// assert_eq!(c, 256);
/// #
/// # Some(())
/// # }
/// #
/// # d().expect("failed to decode");
/// ```
pub struct Decoder<'buf>(Reader<'buf>);

impl<'buf> Decoder<'buf> {
    /// Decodes a value from the buffer.
    #[inline]
    pub fn decode<D>(&mut self) -> Option<D>
    where
        D: Decode<'buf>,
    {
        D::decode(&mut self.0)
    }

    /// Decodes a value from the buffer with passed state.
    #[inline]
    pub fn decode_with<D>(&mut self, state: D::State) -> Option<D>
    where
        D: DecodeWith<'buf>,
    {
        D::decode_with(&mut self.0, state)
    }

    /// Decodes an `u8` value.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn d() -> Option<()> {
    /// use co::AsDecoder;
    ///
    /// let mut dec = [3].as_decoder();
    ///
    /// let n = dec.u8()?;
    /// assert_eq!(n, 3);
    /// #
    /// # Some(())
    /// # }
    /// #
    /// # d().expect("failed to decode");
    /// ```
    #[inline]
    pub fn u8(&mut self) -> Option<u8> {
        self.decode()
    }

    /// Decodes an `u16` value with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn d() -> Option<()> {
    /// use co::AsDecoder;
    ///
    /// let mut dec = [0, 3].as_decoder();
    ///
    /// let n = dec.u16()?;
    /// assert_eq!(n, 3);
    /// #
    /// # Some(())
    /// # }
    /// #
    /// # d().expect("failed to decode");
    /// ```
    #[inline]
    pub fn u16(&mut self) -> Option<u16> {
        self.decode_from_bytes(u16::from_be_bytes)
    }

    /// Decodes an `u32` value with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn d() -> Option<()> {
    /// use co::AsDecoder;
    ///
    /// let mut dec = [0, 0, 0, 3].as_decoder();
    ///
    /// let n = dec.u32()?;
    /// assert_eq!(n, 3);
    /// #
    /// # Some(())
    /// # }
    /// #
    /// # d().expect("failed to decode");
    /// ```
    #[inline]
    pub fn u32(&mut self) -> Option<u32> {
        self.decode_from_bytes(u32::from_be_bytes)
    }

    /// Decodes an `u64` value with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn d() -> Option<()> {
    /// use co::AsDecoder;
    ///
    /// let mut dec = [0, 0, 0, 0, 0, 0, 0, 3].as_decoder();
    ///
    /// let n = dec.u64()?;
    /// assert_eq!(n, 3);
    /// #
    /// # Some(())
    /// # }
    /// #
    /// # d().expect("failed to decode");
    /// ```
    #[inline]
    pub fn u64(&mut self) -> Option<u64> {
        self.decode_from_bytes(u64::from_be_bytes)
    }

    /// Decodes an `u128` value with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn d() -> Option<()> {
    /// use co::AsDecoder;
    ///
    /// let mut dec = [
    ///     0, 0, 0, 0, 0, 0, 0, 0,
    ///     0, 0, 0, 0, 0, 0, 0, 3,
    /// ].as_decoder();
    ///
    /// let n = dec.u128()?;
    /// assert_eq!(n, 3);
    /// #
    /// # Some(())
    /// # }
    /// #
    /// # d().expect("failed to decode");
    /// ```
    #[inline]
    pub fn u128(&mut self) -> Option<u128> {
        self.decode_from_bytes(u128::from_be_bytes)
    }

    /// Decodes an `usize` value with big-endian byte ordering.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn d() -> Option<()> {
    /// use co::AsDecoder;
    ///
    /// let mut buf = [0; size_of::<usize>()];
    /// let [.., m] = &mut buf;
    /// *m = 3;
    ///
    /// let mut dec = buf.as_decoder();
    ///
    /// let n = dec.usize()?;
    /// assert_eq!(n, 3);
    /// #
    /// # Some(())
    /// # }
    /// #
    /// # d().expect("failed to decode");
    /// ```
    #[inline]
    pub fn usize(&mut self) -> Option<usize> {
        self.decode_from_bytes(usize::from_be_bytes)
    }

    /// Checks if the buffer has ended.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn d() -> Option<()> {
    /// use co::AsDecoder;
    ///
    /// let mut dec = [0, 1, 2].as_decoder();
    ///
    /// // The buffer has not ended yet
    /// assert!(dec.end().is_none());
    ///
    /// dec.u8()?;
    /// dec.u8()?;
    /// dec.u8()?;
    ///
    /// // The buffer has already ended
    /// dec.end()?;
    /// #
    /// # Some(())
    /// # }
    /// #
    /// # d().expect("failed to decode");
    /// ```
    #[inline]
    pub fn end(&mut self) -> Option<()> {
        if self.0.remaining() == 0 {
            Some(())
        } else {
            None
        }
    }

    #[inline]
    fn decode_from_bytes<D, F, const N: usize>(&mut self, f: F) -> Option<D>
    where
        F: FnOnce([u8; N]) -> D,
    {
        Some(f(self.decode()?))
    }
}

/// Creates a [decoder](Decoder) from a buffer.
pub trait AsDecoder {
    fn as_decoder(&self) -> Decoder<'_>;
}

impl<A> AsDecoder for A
where
    A: AsRef<[u8]> + ?Sized,
{
    #[inline]
    fn as_decoder(&self) -> Decoder<'_> {
        Decoder(Reader::new(self.as_ref()))
    }
}
