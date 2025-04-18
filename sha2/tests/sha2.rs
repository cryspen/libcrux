use libcrux_traits::Digest as _;

// XXX: The tests in here are failing in wasm for some reason.

// #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn sha256_kat_streaming() {
    let mut digest = libcrux_sha2::Sha256::new();
    let mut d = [0u8; 32];
    digest.update(b"libcrux sha2 256 tests");
    digest.finish(&mut d);

    let expected = "8683520e19e5b33db33c8fb90918c0c96fcdfd9a17c695ce0f0ea2eaa0c95956";
    assert_eq!(hex::encode(d), expected);
}

// #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn sha256_kat_oneshot() {
    let d = libcrux_sha2::sha256(b"libcrux sha2 256 tests");

    let expected = "8683520e19e5b33db33c8fb90918c0c96fcdfd9a17c695ce0f0ea2eaa0c95956";
    assert_eq!(hex::encode(d), expected);
}

#[test]
fn shaclone() {
    let mut hasher_224 = libcrux_sha2::Sha224::new();
    hasher_224.update(b"test 224");
    let mut hasher224_2 = hasher_224.clone();
    hasher_224.update(b"more 224");
    hasher224_2.update(b"more 224");
    let mut digest = [0u8; 28];
    let mut digest_2 = [0u8; 28];
    hasher_224.finish(&mut digest);
    hasher224_2.finish(&mut digest_2);

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux_sha2::sha224(b"test 224more 224"));

    let mut hasher_256 = libcrux_sha2::Sha256::new();
    hasher_256.update(b"test 256");
    let mut hasher256_2 = hasher_256.clone();
    hasher_256.update(b"more 256");
    hasher256_2.update(b"more 256");
    let mut digest = [0u8; 32];
    let mut digest_2 = [0u8; 32];
    hasher_256.finish(&mut digest);
    hasher256_2.finish(&mut digest_2);

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux_sha2::sha256(b"test 256more 256"));

    let mut hasher_384 = libcrux_sha2::Sha384::new();
    hasher_384.update(b"test 384");
    let mut hasher384_2 = hasher_384.clone();
    hasher_384.update(b"more 384");
    hasher384_2.update(b"more 384");
    let mut digest = [0u8; 48];
    let mut digest_2 = [0u8; 48];
    hasher_384.finish(&mut digest);
    hasher384_2.finish(&mut digest_2);

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux_sha2::sha384(b"test 384more 384"));

    let mut hasher_512 = libcrux_sha2::Sha512::new();
    hasher_512.update(b"test 512");
    let mut hasher512_2 = hasher_512.clone();
    hasher_512.update(b"more 512");
    hasher512_2.update(b"more 512");
    let mut digest = [0u8; 64];
    let mut digest_2 = [0u8; 64];
    hasher_512.finish(&mut digest);
    hasher512_2.finish(&mut digest_2);

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux_sha2::sha512(b"test 512more 512"));
}
