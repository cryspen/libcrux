#[test]
fn sha3_kat_oneshot() {
    let d256 = libcrux_sha3::sha256(b"Hello, World!");
    let expected256 = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
    assert_eq!(hex::encode(&d256), expected256);

    let dshake = libcrux_sha3::shake128::<42>(b"Hello, World!");
    let expectedshake =
        "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbaf";
    assert_eq!(hex::encode(&dshake), expectedshake);
}

#[test]
fn sha3_simd_kat_oneshot() {
    let d256 = libcrux_sha3::sha256(b"Hello, World!");
    let expected256 = "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef";
    assert_eq!(hex::encode(&d256), expected256);

    let dshake = libcrux_sha3::shake128::<42>(b"Hello, World!");
    let expectedshake =
        "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbaf";
    assert_eq!(hex::encode(&dshake), expectedshake);
}
