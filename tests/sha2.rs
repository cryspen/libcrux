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
