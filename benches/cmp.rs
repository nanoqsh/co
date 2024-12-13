fn main() {
    divan::main();
}

struct Pack {
    code: u8,
    key: &'static str,
    val: u32,
    slice: &'static [u8],
}

const PACK: Pack = Pack {
    code: 0,
    key: "hello",
    val: 37,
    slice: &[1, 2, 3],
};

#[divan::bench]
fn co_unsafe() {
    let mut out = [0; 14];
    let (p, out) = divan::black_box((PACK, &mut out));

    let res = co_unsafe_encode(&p, out);
    assert!(res.is_ok());
}

#[divan::bench]
fn co_safe() {
    let mut out = [0; 14];
    let (p, out) = divan::black_box((PACK, &mut out));

    let res = co_safe_encode(&p, out);
    assert!(res.is_ok());
}

#[divan::bench]
fn safe() {
    let mut out = [0; 14];
    let (p, out) = divan::black_box((PACK, &mut out));

    let res = safe_encode(&p, out);
    assert!(res.is_ok());
}

fn co_unsafe_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    use co::encode_unsafe::EncodeExt;

    p.code
        .then(p.key.as_bytes())
        .u8(0)
        .u32_be(p.val)
        .then(p.slice)
        .encode(out)?;

    Ok(())
}

fn co_safe_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    use co::EncodeExt;

    p.code
        .then(p.key.as_bytes())
        .u8(0)
        .u32_be(p.val)
        .then(p.slice)
        .encode(out)
}

fn safe_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    let pack_len =
          1             // code
        + p.key.len()   // key
        + 1             // nul byte
        + 4             // val
        + p.slice.len() // slice
    ;

    if out.len() != pack_len {
        return Err(pack_len);
    }

    let mut i = 0;

    out[i] = p.code;
    i += 1;

    out[i..i + p.key.len()].copy_from_slice(p.key.as_bytes());
    i += p.key.len();

    out[i] = 0;
    i += 1;

    out[i..i + 4].copy_from_slice(&p.val.to_be_bytes());
    i += 4;

    out[i..i + p.slice.len()].copy_from_slice(p.slice);
    i += p.slice.len();

    // used in test mod
    debug_assert_eq!(i, out.len());

    Ok(())
}
