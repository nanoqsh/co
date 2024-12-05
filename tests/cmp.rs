include!("../benches/cmp.rs");

const PACK: Pack = Pack {
    code: 0,
    key: "hello",
    val: 37,
    slice: &[1, 2, 3],
};

const CODE: [u8; 14] = [
    0x0, //                          0
    0x68, 0x65, 0x6C, 0x6C, 0x6F, // hello
    0x0,  //                         0
    0x0, 0x0, 0x0, 0x25, //          37
    0x1, 0x2, 0x3, //                1 2 3
];

#[test]
fn co_pack() {
    let mut out = [0; CODE.len()];
    let ok = co_encode(&PACK, &mut out);

    assert!(ok);
    assert_eq!(out, CODE);
}

#[test]
fn safe_pack() {
    let mut out = [0; CODE.len()];
    let ok = safe_encode(&PACK, &mut out);

    assert!(ok);
    assert_eq!(out, CODE);
}
