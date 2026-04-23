#[test]
fn blake2b256() {
    let vectors = libcrux_kats::blake2::load_blake2b256();
    assert!(!vectors.is_empty());

    for (i, tv) in vectors.iter().enumerate() {
        let mut got = [0u8; 32];
        if let Some(ref key) = tv.key {
            let mut hasher = libcrux_blake2::Blake2bBuilder::new_keyed_dynamic(key)
                .unwrap()
                .build_var_digest_len(32)
                .unwrap();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got).unwrap();
        } else {
            let mut hasher = libcrux_blake2::Blake2bBuilder::new_unkeyed().build_const_digest_len();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got);
        }
        assert_eq!(&got[..], &tv.hash[..], "blake2b256 vector {i} mismatch");
    }
    println!("Ran {} BLAKE2b-256 test vectors", vectors.len());
}

#[test]
fn blake2s256() {
    let vectors = libcrux_kats::blake2::load_blake2s256();
    assert!(!vectors.is_empty());

    for (i, tv) in vectors.iter().enumerate() {
        let mut got = [0u8; 32];
        if let Some(ref key) = tv.key {
            let mut hasher = libcrux_blake2::Blake2sBuilder::new_keyed_dynamic(key)
                .unwrap()
                .build_var_digest_len(32)
                .unwrap();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got).unwrap();
        } else {
            let mut hasher = libcrux_blake2::Blake2sBuilder::new_unkeyed().build_const_digest_len();
            hasher.update(&tv.input).unwrap();
            hasher.finalize(&mut got);
        }
        assert_eq!(&got[..], &tv.hash[..], "blake2s256 vector {i} mismatch");
    }
    println!("Ran {} BLAKE2s-256 test vectors", vectors.len());
}
