use libcrux_kats::wycheproof::{aead, TestResult};
use rand_core::UnwrapErr;

fn randbuf<const N: usize>(rng: &mut impl rand_core::Rng) -> [u8; N] {
    let mut buf = [0; N];
    rng.fill_bytes(&mut buf);
    buf
}

#[test]
fn wycheproof() {
    let test_set = aead::TestSet::load_chacha20_poly1305();
    let mut tests_run = 0;
    let mut skipped = 0;

    for test_group in test_set.test_groups {
        if test_group.iv_size != 96 {
            skipped += test_group.tests.len();
            continue;
        }

        for test in &test_group.tests {
            let valid = test.result == TestResult::Valid;
            let nonce = <&[u8; 12]>::try_from(test.nonce.as_slice()).unwrap();
            let key = <&[u8; 32]>::try_from(test.key.as_slice()).unwrap();

            let mut ctxt = test.pt.to_vec();
            let tag =
                match libcrux_chacha20poly1305::encrypt(key, &test.pt, &mut ctxt, &test.aad, nonce)
                {
                    Ok((_v, t)) => t,
                    Err(_) => {
                        tests_run += 1;
                        continue;
                    }
                };

            if valid {
                assert_eq!(
                    tag,
                    test.tag.as_slice(),
                    "tc_id {}: tag mismatch",
                    test.tc_id
                );
            } else {
                assert_ne!(
                    tag,
                    test.tag.as_slice(),
                    "tc_id {}: expected tag mismatch for invalid test",
                    test.tc_id,
                );
            }
            assert_eq!(
                ctxt,
                test.ct.as_slice(),
                "tc_id {}: ciphertext mismatch",
                test.tc_id,
            );

            let mut decrypted = vec![0; test.pt.len()];
            match libcrux_chacha20poly1305::decrypt(key, &mut decrypted, &ctxt, &test.aad, nonce) {
                Ok(m) => {
                    assert_eq!(m, test.pt.as_slice());
                    assert_eq!(&decrypted, test.pt.as_slice());
                }
                Err(_) => {
                    assert!(!valid);
                }
            };

            tests_run += 1;
        }
    }

    assert!(tests_run > 0, "No tests were run");
    println!(
        "Ran {tests_run} ChaCha20-Poly1305 tests, skipped {skipped} ({} total)",
        test_set.number_of_tests
    );
}

#[test]
fn wycheproof_xchacha() {
    let test_set = aead::TestSet::load_xchacha20_poly1305();
    let mut tests_run = 0;
    let mut skipped = 0;

    for test_group in test_set.test_groups {
        if test_group.iv_size != 192 {
            skipped += test_group.tests.len();
            continue;
        }

        for test in &test_group.tests {
            let valid = test.result == TestResult::Valid;
            let nonce = <&[u8; 24]>::try_from(test.nonce.as_slice()).unwrap();
            let key = <&[u8; 32]>::try_from(test.key.as_slice()).unwrap();

            let mut ctxt = test.pt.to_vec();
            let tag = match libcrux_chacha20poly1305::xchacha20_poly1305::encrypt(
                key, &test.pt, &mut ctxt, &test.aad, nonce,
            ) {
                Ok((_v, t)) => t,
                Err(_) => {
                    tests_run += 1;
                    continue;
                }
            };

            if valid {
                assert_eq!(
                    tag,
                    test.tag.as_slice(),
                    "tc_id {}: tag mismatch",
                    test.tc_id
                );
            } else {
                assert_ne!(
                    tag,
                    test.tag.as_slice(),
                    "tc_id {}: expected tag mismatch for invalid test",
                    test.tc_id,
                );
            }
            assert_eq!(
                ctxt,
                test.ct.as_slice(),
                "tc_id {}: ciphertext mismatch",
                test.tc_id,
            );

            let mut decrypted = vec![0; test.pt.len()];
            match libcrux_chacha20poly1305::xchacha20_poly1305::decrypt(
                key,
                &mut decrypted,
                &ctxt,
                &test.aad,
                nonce,
            ) {
                Ok(m) => {
                    assert_eq!(m, test.pt.as_slice());
                    assert_eq!(&decrypted, test.pt.as_slice());
                }
                Err(_) => {
                    assert!(!valid);
                }
            };

            tests_run += 1;
        }
    }

    assert!(tests_run > 0, "No tests were run");
    println!(
        "Ran {tests_run} XChaCha20-Poly1305 tests, skipped {skipped} ({} total)",
        test_set.number_of_tests
    );
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn chachapoly_self_test() {
    let ptxt = b"hacspec rulez";
    let aad = b"associated data" as &[u8];
    let key = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32,
    ];
    let nonce = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

    let mut ctxt = [0; 29];

    libcrux_chacha20poly1305::encrypt(&key, ptxt, &mut ctxt, aad, &nonce).unwrap();

    let mut ptxt_rx = [0; 13];

    assert!(libcrux_chacha20poly1305::decrypt(&key, &mut ptxt_rx, &ctxt, aad, &nonce).is_ok());
    assert_eq!(ptxt, &ptxt_rx);
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn chachapoly_self_test_rand() {
    let msg = b"hacspec rulez";
    let aad = b"associated data" as &[u8];

    let mut rng = UnwrapErr(rand::rngs::SysRng);

    let key: [u8; 32] = randbuf(&mut rng);
    let nonce: [u8; 12] = randbuf(&mut rng);

    let mut ctxt = [0; 29];
    let mut ptxt = [0; 13];

    libcrux_chacha20poly1305::encrypt(&key, msg, &mut ctxt, aad, &nonce).unwrap();
    assert!(libcrux_chacha20poly1305::decrypt(&key, &mut ptxt, &ctxt, aad, &nonce).is_ok());

    assert_eq!(msg, &ptxt);
}

#[test]
fn chachapoly_test_invalid_buffer_lengths() {
    let msg = b"hacspec rulez";
    let aad = b"associated data" as &[u8];

    let mut rng = UnwrapErr(rand::rngs::SysRng);

    let key: [u8; 32] = randbuf(&mut rng);
    let nonce: [u8; 12] = randbuf(&mut rng);

    // test that calling with incorrect-length buffers returns error: non-detached
    let err = libcrux_chacha20poly1305::encrypt(&key, msg, &mut [], aad, &nonce).unwrap_err();
    assert!(matches!(
        err,
        libcrux_chacha20poly1305::AeadError::CiphertextTooShort
    ));

    // test that calling with incorrect-length buffers returns error: detached
    let err =
        libcrux_chacha20poly1305::encrypt_detached(&key, msg, &mut [], &mut [0; 16], aad, &nonce)
            .unwrap_err();
    assert!(matches!(
        err,
        libcrux_chacha20poly1305::AeadError::CiphertextTooShort
    ));

    // encrypt correctly
    let mut ctxt = [0; 29];
    libcrux_chacha20poly1305::encrypt(&key, msg, &mut ctxt, aad, &nonce).unwrap();

    // encrypt correctly on ciphertext buffer longer than `ptxt.len() + TAG_LEN`
    let mut long_ctxt = [0; 30];
    libcrux_chacha20poly1305::encrypt(&key, msg, &mut long_ctxt, aad, &nonce).unwrap();

    let mut decrypted = [0u8; 13];
    assert!(
        libcrux_chacha20poly1305::decrypt(&key, &mut decrypted, &long_ctxt[..29], aad, &nonce)
            .is_ok()
    );
    assert_eq!(decrypted, *msg);

    // test that calling with incorrect-length buffers returns error: non-detached
    let err = libcrux_chacha20poly1305::decrypt(&key, &mut [], &ctxt, aad, &nonce).unwrap_err();
    assert!(matches!(
        err,
        libcrux_chacha20poly1305::AeadError::PlaintextTooShort
    ));

    // test that calling with incorrect-length buffers returns error: detached
    let err =
        libcrux_chacha20poly1305::decrypt_detached(&key, &mut [], &ctxt, &mut [0; 16], aad, &nonce)
            .unwrap_err();
    assert!(matches!(
        err,
        libcrux_chacha20poly1305::AeadError::PlaintextTooShort
    ));
}
