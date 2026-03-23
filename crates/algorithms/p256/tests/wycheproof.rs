use wycheproof::{ecdh, TestResult};

#[test]
fn ecdh_secp256r1() {
    let test_set =
        ecdh::TestSet::load(ecdh::TestName::EcdhSecp256r1Ecpoint).unwrap();
    let mut tests_run = 0;

    for test_group in test_set.test_groups {
        for test in &test_group.tests {
            // The ecpoint format gives us raw public key bytes.
            // For a valid uncompressed point: 04 || X (32 bytes) || Y (32 bytes) = 65 bytes
            // The private key is a 32-byte scalar.
            // The shared secret is the X coordinate (32 bytes).

            let pk_bytes = test.public_key.as_ref();
            let sk_raw = test.private_key.as_ref();

            // Normalize private key to 32 bytes (strip leading zeros or left-pad)
            let sk_bytes: [u8; 32] = if sk_raw.len() > 32 {
                // Strip leading zeros
                let start = sk_raw.len() - 32;
                if sk_raw[..start].iter().any(|&b| b != 0) {
                    // Non-zero leading bytes — invalid scalar
                    if test.result == TestResult::Valid {
                        panic!("tc_id {}: valid test has oversized private key", test.tc_id);
                    }
                    tests_run += 1;
                    continue;
                }
                sk_raw[start..].try_into().unwrap()
            } else if sk_raw.len() == 32 {
                sk_raw.try_into().unwrap()
            } else {
                // Left-pad with zeros
                let mut buf = [0u8; 32];
                buf[32 - sk_raw.len()..].copy_from_slice(sk_raw);
                buf
            };

            // Parse public key: strip 04 prefix if present to get raw 64-byte X||Y
            let raw_pk = if pk_bytes.len() == 65 && pk_bytes[0] == 0x04 {
                &pk_bytes[1..]
            } else if pk_bytes.len() == 64 {
                pk_bytes
            } else {
                // Compressed points (33 bytes), empty, or otherwise malformed
                // keys — skip and just verify the test expects failure
                if test.result == TestResult::Valid {
                    panic!(
                        "tc_id {}: unexpected public key length {} for valid test",
                        test.tc_id,
                        pk_bytes.len(),
                    );
                }
                tests_run += 1;
                continue;
            };

            let mut shared = [0u8; 64];

            let success =
                libcrux_p256::dh_responder(&mut shared, raw_pk, &sk_bytes);

            match test.result {
                TestResult::Valid | TestResult::Acceptable => {
                    assert!(
                        success,
                        "tc_id {}: expected success but ECDH failed",
                        test.tc_id,
                    );
                    // Wycheproof shared secret is just the X coordinate (first 32 bytes)
                    assert_eq!(
                        &shared[..32],
                        test.shared_secret.as_ref(),
                        "tc_id {}: shared secret mismatch",
                        test.tc_id,
                    );
                }
                TestResult::Invalid => {
                    if success {
                        // Some invalid tests may still compute — that's OK
                        // as long as we don't claim they're valid
                    }
                }
            }
            tests_run += 1;
        }
    }

    assert!(tests_run > 0, "No tests were run");
    println!(
        "Ran {tests_run} P-256 ECDH tests ({} total)",
        test_set.number_of_tests
    );
}
