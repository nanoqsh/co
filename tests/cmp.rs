include!("../benches/cmp.rs");

const CODE: [u8; 14] = [
    0x0, //                          0
    0x68, 0x65, 0x6C, 0x6C, 0x6F, // hello
    0x0,  //                         0
    0x0, 0x0, 0x0, 0x25, //          37
    0x1, 0x2, 0x3, //                1 2 3
];

#[test]
fn co_unsafe_pack() {
    let mut out = [0; CODE.len()];
    let res = co_unsafe_encode(&PACK, &mut out);

    assert!(res.is_ok());
    assert_eq!(out, CODE);
}

#[test]
fn co_safe_pack() {
    let mut out = [0; CODE.len()];
    let res = co_safe_encode(&PACK, &mut out);

    assert!(res.is_ok());
    assert_eq!(out, CODE);
}

#[test]
fn safe_pack() {
    let mut out = [0; CODE.len()];
    let res = safe_encode(&PACK, &mut out);

    assert!(res.is_ok());
    assert_eq!(out, CODE);
}
