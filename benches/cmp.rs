use {divan::Bencher, std::fmt};

fn main() {
    divan::main();
}

#[derive(Copy, Clone)]
struct Case(fn(), &'static str);

impl fmt::Display for Case {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.1.fmt(f)
    }
}

#[divan::bench(
    sample_count = 100000,
    args = [
        Case(co, "co"),
        Case(co_unsafe, "co_unsafe"),
        Case(safe, "safe"),
    ],
)]
fn bench(ben: Bencher, Case(f, _): Case) {
    // warmup
    for _ in 0..100000000 {
        f();
    }

    ben.bench(f);
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

fn co_unsafe() {
    let mut out = [0; 14];
    let (p, out) = divan::black_box((PACK, &mut out));

    let res = co_unsafe_encode(&p, out);
    assert!(res.is_ok());
}

fn co() {
    let mut out = [0; 14];
    let (p, out) = divan::black_box((PACK, &mut out));

    let res = co_encode(&p, out);
    assert!(res.is_ok());
}

fn safe() {
    let mut out = [0; 14];
    let (p, out) = divan::black_box((PACK, &mut out));

    let res = safe_encode(&p, out);
    assert!(res.is_ok());
}

fn co_unsafe_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    use co::EncodeExt;

    p.code
        .then(p.key.as_bytes())
        .u8(0)
        .u32_be(p.val)
        .then(p.slice)
        .encode_(out)?;

    Ok(())
}

fn co_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    use co::EncodeExt;

    p.code
        .then(p.key.as_bytes())
        .u8(0)
        .u32_be(p.val)
        .then(p.slice)
        .encode(out)?;

    Ok(())
}

fn safe_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    let pack_len =
          size_of::<u8>()  // code
        + p.key.len()      // key
        + size_of::<u8>()  // nul byte
        + size_of::<u32>() // val
        + p.slice.len()    // slice
    ;

    if out.len() != pack_len {
        return Err(pack_len);
    }

    let mut i = 0;

    out[i] = p.code;
    i += size_of::<u8>();

    out[i..i + p.key.len()].copy_from_slice(p.key.as_bytes());
    i += p.key.len();

    out[i] = 0;
    i += size_of::<u8>();

    out[i..i + size_of::<u32>()].copy_from_slice(&p.val.to_be_bytes());
    i += size_of::<u32>();

    out[i..i + p.slice.len()].copy_from_slice(p.slice);
    i += p.slice.len();

    // used in test mod
    debug_assert_eq!(i, out.len());

    Ok(())
}
