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
    a: u8,
    b: &'static [u8],
    c: u32,
    d: u8,
    e: &'static [u8],
    f: u8,
    g: u64,
    h: &'static [u8],
}

const PACK: Pack = Pack {
    a: 0,
    b: &[1, 2, 3, 4, 5, 6],
    c: 1,
    d: 2,
    e: &[1, 2, 3, 4, 5, 6],
    f: 3,
    g: 4,
    h: &[1, 2, 3, 4, 5, 6],
};

fn co() {
    let mut out = [0; 33];
    let (p, out) = divan::black_box((PACK, &mut out));

    co_encode(&p, out).expect("encoding must be successful");
}

fn safe() {
    let mut out = [0; 33];
    let (p, out) = divan::black_box((PACK, &mut out));

    safe_encode(&p, out).expect("encoding must be successful");
}

fn co_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    use co::EncodeExt;

    p.a.then(p.b)
        .u32(p.c)
        .u8(p.d)
        .then(p.e)
        .u8(p.f)
        .u64(p.g)
        .then(p.h)
        .encode(out)?;

    Ok(())
}

fn safe_encode(p: &Pack, out: &mut [u8]) -> Result<(), usize> {
    let pack_len =
          size_of::<u8>()  // a
        + p.b.len()        // b
        + size_of::<u32>() // c
        + size_of::<u8>()  // d
        + p.e.len()        // e
        + size_of::<u8>()  // f
        + size_of::<u64>() // g
        + p.h.len()        // h
    ;

    if out.len() != pack_len {
        return Err(pack_len);
    }

    let mut i = 0;

    out[i] = p.a;
    i += size_of::<u8>();

    out[i..i + p.b.len()].copy_from_slice(p.b);
    i += p.b.len();

    out[i..i + size_of::<u32>()].copy_from_slice(&p.c.to_be_bytes());
    i += size_of::<u32>();

    out[i..i + size_of::<u8>()].copy_from_slice(&p.d.to_be_bytes());
    i += size_of::<u8>();

    out[i..i + p.e.len()].copy_from_slice(p.e);
    i += p.e.len();

    out[i..i + size_of::<u8>()].copy_from_slice(&p.f.to_be_bytes());
    i += size_of::<u8>();

    out[i..i + size_of::<u64>()].copy_from_slice(&p.g.to_be_bytes());
    i += size_of::<u64>();

    out[i..i + p.h.len()].copy_from_slice(p.h);
    i += p.h.len();

    // used in test mod
    debug_assert_eq!(i, out.len(), "fill the whole buffer");

    Ok(())
}
