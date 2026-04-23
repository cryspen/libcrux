use libcrux_hkdf::Algorithm;
use libcrux_kats::wycheproof::{hkdf, TestResult};
use libcrux_secrets::{Classify, DeclassifyRef};

fn test_hkdf(test_set: hkdf::TestSet, name: &str, algo: Algorithm) {
    let mut tests_run = 0;

    for test_group in test_set.test_groups {
        for test in &test_group.tests {
            let salt = test.salt.to_vec().classify();
            let ikm = test.ikm.to_vec().classify();
            let mut okm = vec![0u8; test.size].classify();

            let result = libcrux_hkdf::hkdf(algo, &mut okm, &salt, &ikm, &test.info);

            match test.result {
                TestResult::Valid | TestResult::Acceptable => {
                    result.unwrap_or_else(|e| {
                        panic!(
                            "tc_id {}: expected valid but got error: {:?}",
                            test.tc_id, e
                        )
                    });
                    assert_eq!(
                        okm.declassify_ref(),
                        test.okm.as_slice(),
                        "tc_id {}: output mismatch",
                        test.tc_id,
                    );
                }
                TestResult::Invalid => {
                    assert!(
                        result.is_err(),
                        "tc_id {}: expected error for invalid test",
                        test.tc_id,
                    );
                }
            }
            tests_run += 1;
        }
    }

    assert!(tests_run > 0, "No tests were run for {name}");
    println!(
        "Ran {tests_run} tests for {name} ({} total in set)",
        test_set.number_of_tests
    );
}

#[test]
fn hkdf_sha256() {
    test_hkdf(
        hkdf::TestSet::load_sha256(),
        "hkdf_sha256",
        Algorithm::Sha256,
    );
}

#[test]
fn hkdf_sha384() {
    test_hkdf(
        hkdf::TestSet::load_sha384(),
        "hkdf_sha384",
        Algorithm::Sha384,
    );
}

#[test]
fn hkdf_sha512() {
    test_hkdf(
        hkdf::TestSet::load_sha512(),
        "hkdf_sha512",
        Algorithm::Sha512,
    );
}
