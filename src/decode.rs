use crate::reader::Reader;

pub trait Decode<'buf, S = ()>: Sized {
    fn decode(r: &mut Reader<'buf>, state: S) -> Option<Self>;
}

impl Decode<'_> for () {
    fn decode(_: &mut Reader<'_>, _: ()) -> Option<Self> {
        Some(())
    }
}

impl Decode<'_> for u8 {
    fn decode(r: &mut Reader<'_>, _: ()) -> Option<Self> {
        r.read_byte()
    }
}

impl Decode<'_> for u32 {
    fn decode(r: &mut Reader<'_>, _: ()) -> Option<Self> {
        let &bytes = r.read_array()?;
        Some(Self::from_be_bytes(bytes))
    }
}

impl<'buf> Decode<'buf, usize> for &'buf [u8] {
    fn decode(r: &mut Reader<'buf>, len: usize) -> Option<Self> {
        r.read_slice(len)
    }
}

impl<'buf, const N: usize> Decode<'buf> for &'buf [u8; N] {
    fn decode(r: &mut Reader<'buf>, _: ()) -> Option<Self> {
        r.read_array()
    }
}

impl<'buf, const N: usize> Decode<'buf> for [u8; N] {
    fn decode(r: &mut Reader<'buf>, _: ()) -> Option<Self> {
        r.read_array().copied()
    }
}

pub struct Decoder<'buf>(Reader<'buf>);

impl<'buf> Decoder<'buf> {
    pub fn decode<D>(&mut self) -> Option<D>
    where
        D: Decode<'buf>,
    {
        self.decode_with(())
    }

    pub fn decode_with<D, S>(&mut self, state: S) -> Option<D>
    where
        D: Decode<'buf, S>,
    {
        D::decode(&mut self.0, state)
    }
}

pub trait AsDecoder {
    fn as_decoder(&self) -> Decoder<'_>;
}

impl<A> AsDecoder for A
where
    A: AsRef<[u8]> + ?Sized,
{
    fn as_decoder(&self) -> Decoder<'_> {
        Decoder(Reader::new(self.as_ref()))
    }
}
