pub unsafe trait Encode {
    fn size(&self) -> u32;
    unsafe fn encode(&self, buf: &mut [u8]);
}
