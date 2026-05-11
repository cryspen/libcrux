use libcrux_kats::wycheproof::{ecdh, TestResult};
use libcrux_p256::{compressed_to_raw, ecdh_api::EcdhSlice, uncompressed_to_raw};

#[test]
fn ecdh_secp256r1() {
    let test_set = ecdh::TestSet::load_secp256r1_ecpoint();
    let mut tests_run = 0;

    for test_group in test_set.test_groups {
        for test in &test_group.tests {
            // The ecpoint format gives us sec 1 encoded public keys as hex strings and private keys
            // encoded as hex formatted big integers

            // strip leading 0 bytes
            let sk = test
                .private_key
                .iter()
                .position(|b| *b != 0)
                .map_or(test.private_key.as_slice(), |pos| &test.private_key[pos..]);

            assert!(
                sk.len() <= 32,
                "0 prefix stripped sk is larger than 32 bytes, tc_id: {}",
                test.tc_id
            );
            let mut sk_bytes = [0; 32];
            // sk is a 32-byte big endian big integer, so we pad the lower bytes with 0
            sk_bytes[32 - sk.len()..].copy_from_slice(sk);

            let mut pk_bytes = [0; 64];
            if test.public_key.len() == 65 {
                assert!(
                    uncompressed_to_raw(&test.public_key, &mut pk_bytes),
                    "tc_id: {}, invalid uncompressed public key",
                    test.tc_id
                );
            } else if test.public_key.len() == 33 {
                let valid = compressed_to_raw(&test.public_key, &mut pk_bytes);
                if !valid {
                    assert_eq!(
                        TestResult::Invalid,
                        test.result,
                        "tc_id: {}, test has invalid compressed point but test result is {:?}",
                        test.tc_id,
                        test.result
                    );
                    tests_run += 1;
                    continue;
                }
            } else {
                assert_eq!(
                    TestResult::Invalid,
                    test.result,
                    "tc_id: {}, public key has invalid size {}, but test result is {:?}",
                    test.tc_id,
                    test.public_key.len(),
                    test.result
                );
                assert!(
                    test.flags.contains(&"InvalidEncoding".to_string()),
                    "tc_id: {}, public key is invalid but test does not contain InvalidEncoding flag ",
                    test.tc_id
                );
                tests_run += 1;
                continue;
            }

            let mut derived = [0u8; 64];
            let result = libcrux_p256::P256::derive_ecdh(&mut derived, &pk_bytes, &sk_bytes);

            match test.result {
                // XXX: In the future, wycheproof might add acceptable test cases which we (want to) reject.
                // This needs to be split then.
                TestResult::Valid | TestResult::Acceptable => {
                    assert!(
                        result.is_ok(),
                        "tc_id {}: expected success or acceptable but ECDH failed",
                        test.tc_id,
                    );
                    // Wycheproof shared secret is just the X coordinate (first 32 bytes)
                    assert_eq!(
                        test.shared_secret,
                        derived[..32],
                        "tc_id {}: shared secret mismatch",
                        test.tc_id,
                    );
                }
                TestResult::Invalid => {
                    assert!(
                        result.is_err(),
                        "tc_id: {}, expected invalid test but ECDH derive succeeded",
                        test.tc_id
                    );
                }
            }
            tests_run += 1;
        }
    }

    assert_eq!(
        test_set.number_of_tests, tests_run,
        "invalid number of tests run"
    );
    println!("Ran {tests_run} ecdh_secp256r1_ecpoint tests",);
}
