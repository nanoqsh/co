use co::prelude::*;

fn main() {
    divan::main();
}

struct Pack {
    code: u8,
    key: &'static str,
    val: u32,
    slice: &'static [u8],
}

#[divan::bench]
fn co() {
    let p = Pack {
        code: 0,
        key: "hello",
        val: 37,
        slice: &[1, 2, 3],
    };

    let mut out = [0; 14];

    let (p, out) = divan::black_box((p, &mut out));
    let ok = co_encode(&p, out);
    assert!(ok);
}

#[divan::bench]
fn safe() {
    let p = Pack {
        code: 0,
        key: "hello",
        val: 37,
        slice: &[1, 2, 3],
    };

    let mut out = [0; 14];

    let (p, out) = divan::black_box((p, &mut out));
    let ok = safe_encode(&p, out);
    assert!(ok);
}

fn co_encode(p: &Pack, out: &mut [u8]) -> bool {
    p.code
        .then(p.key.as_bytes())
        .u8(0)
        .u32_be(p.val)
        .then(p.slice)
        .encode(out)
        .is_ok()
}

fn safe_encode(p: &Pack, out: &mut [u8]) -> bool {
    let pack_len =
          1           // code
        + p.key.len() // key
        + 1           // nul byte
        + 4           // val
        + 3           // slice
    ;

    if out.len() != pack_len {
        return false;
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

    true
}
