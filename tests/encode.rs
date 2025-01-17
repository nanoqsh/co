include!("../benches/encode.rs");

const CODE: [u8; 33] = [
    0, //                      a
    1, 2, 3, 4, 5, 6, //       b
    0, 0, 0, 1, //             c
    2, //                      d
    1, 2, 3, 4, 5, 6, //       e
    3, 0, 0, 0, 0, 0, 0, 0, // f
    4, //                      g
    1, 2, 3, 4, 5, 6, //       h
];

#[test]
fn co_pack() {
    let mut out = [0; CODE.len()];
    let res = co_encode(&PACK, &mut out);

    assert_eq!(res, Ok(()));
    assert_eq!(out, CODE);
}

#[test]
fn safe_pack() {
    let mut out = [0; CODE.len()];
    let res = safe_encode(&PACK, &mut out);

    assert_eq!(res, Ok(()));
    assert_eq!(out, CODE);
}
