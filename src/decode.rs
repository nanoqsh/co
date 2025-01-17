use crate::reader::Reader;

/// A trait for decoding values from a buffer.
///
/// # Note
///
/// This trait is intended for low-level implementations. Use the
/// [decoder](Decoder) for convenient decoding of byte sequences.
pub trait Decode<'buf, S = ()>: Sized {
    fn decode(r: &mut Reader<'buf>, state: S) -> Option<Self>;
}

impl Decode<'_> for () {
    #[inline]
    fn decode(_: &mut Reader<'_>, _: ()) -> Option<Self> {
        Some(())
    }
}

impl Decode<'_> for u8 {
    #[inline]
    fn decode(r: &mut Reader<'_>, _: ()) -> Option<Self> {
        r.read_byte()
    }
}

impl<'buf> Decode<'buf, usize> for &'buf [u8] {
    #[inline]
    fn decode(r: &mut Reader<'buf>, len: usize) -> Option<Self> {
        r.read_slice(len)
    }
}

impl<'buf, const N: usize> Decode<'buf> for &'buf [u8; N] {
    #[inline]
    fn decode(r: &mut Reader<'buf>, _: ()) -> Option<Self> {
        r.read_array()
    }
}

impl<'buf, const N: usize> Decode<'buf> for [u8; N] {
    #[inline]
    fn decode(r: &mut Reader<'buf>, _: ()) -> Option<Self> {
        r.read_array().copied()
    }
}

pub struct Decoder<'buf>(Reader<'buf>);

impl<'buf> Decoder<'buf> {
    #[inline]
    pub fn decode<D>(&mut self) -> Option<D>
    where
        D: Decode<'buf>,
    {
        self.decode_with(())
    }

    #[inline]
    pub fn decode_with<D, S>(&mut self, state: S) -> Option<D>
    where
        D: Decode<'buf, S>,
    {
        D::decode(&mut self.0, state)
    }

    #[inline]
    pub fn u8(&mut self) -> Option<u8> {
        self.decode_with(())
    }

    #[inline]
    pub fn u16(&mut self) -> Option<u16> {
        self.decode_from_bytes(u16::from_be_bytes)
    }

    #[inline]
    pub fn u32(&mut self) -> Option<u32> {
        self.decode_from_bytes(u32::from_be_bytes)
    }

    #[inline]
    pub fn u64(&mut self) -> Option<u64> {
        self.decode_from_bytes(u64::from_be_bytes)
    }

    #[inline]
    pub fn u128(&mut self) -> Option<u128> {
        self.decode_from_bytes(u128::from_be_bytes)
    }

    #[inline]
    pub fn usize(&mut self) -> Option<usize> {
        self.decode_from_bytes(usize::from_be_bytes)
    }

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
