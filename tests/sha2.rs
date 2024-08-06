// XXX: The tests in here are failing in wasm for some reason.

// #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn sha256_kat_streaming() {
    let mut digest = libcrux::digest::Sha2_256::new();
    digest.update(b"libcrux sha2 256 tests");
    let d = digest.finish();

    let expected = "8683520e19e5b33db33c8fb90918c0c96fcdfd9a17c695ce0f0ea2eaa0c95956";
    assert_eq!(hex::encode(&d), expected);
}

// #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn sha256_kat_oneshot() {
    let d = libcrux::digest::sha2_256(b"libcrux sha2 256 tests");

    let expected = "8683520e19e5b33db33c8fb90918c0c96fcdfd9a17c695ce0f0ea2eaa0c95956";
    assert_eq!(hex::encode(&d), expected);
}

#[test]
fn sha2_clone() {
    let mut hasher_224 = libcrux::digest::Sha2_224::new();
    hasher_224.update(b"test 224");
    let mut hasher224_2 = hasher_224.clone();
    hasher_224.update(b"more 224");
    hasher224_2.update(b"more 224");
    let digest = hasher_224.finish();
    let digest_2 = hasher224_2.finish();

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux::digest::sha2_224(b"test 224more 224"));

    let mut hasher_256 = libcrux::digest::Sha2_256::new();
    hasher_256.update(b"test 256");
    let mut hasher256_2 = hasher_256.clone();
    hasher_256.update(b"more 256");
    hasher256_2.update(b"more 256");
    let digest = hasher_256.finish();
    let digest_2 = hasher256_2.finish();

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux::digest::sha2_256(b"test 256more 256"));

    let mut hasher_384 = libcrux::digest::Sha2_384::new();
    hasher_384.update(b"test 384");
    let mut hasher384_2 = hasher_384.clone();
    hasher_384.update(b"more 384");
    hasher384_2.update(b"more 384");
    let digest = hasher_384.finish();
    let digest_2 = hasher384_2.finish();

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux::digest::sha2_384(b"test 384more 384"));

    let mut hasher_512 = libcrux::digest::Sha2_512::new();
    hasher_512.update(b"test 512");
    let mut hasher512_2 = hasher_512.clone();
    hasher_512.update(b"more 512");
    hasher512_2.update(b"more 512");
    let digest = hasher_512.finish();
    let digest_2 = hasher512_2.finish();

    assert_eq!(digest, digest_2);
    assert_eq!(digest, libcrux::digest::sha2_512(b"test 512more 512"));
}
