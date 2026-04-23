use libcrux_hmac::Algorithm;
use libcrux_kats::wycheproof::{mac, TestResult};

fn test_hmac(test_set: mac::TestSet, name: &str, algo: Algorithm) {
    let mut tests_run = 0;

    for test_group in test_set.test_groups {
        let tag_bytes = test_group.tag_size / 8;

        for test in &test_group.tests {
            let computed = libcrux_hmac::hmac(algo, &test.key, &test.msg, Some(tag_bytes));

            match test.result {
                TestResult::Valid | TestResult::Acceptable => {
                    assert_eq!(
                        computed.as_slice(),
                        test.tag.as_slice(),
                        "tc_id {}: tag mismatch",
                        test.tc_id,
                    );
                }
                TestResult::Invalid => {
                    assert_ne!(
                        computed.as_slice(),
                        test.tag.as_slice(),
                        "tc_id {}: expected tag mismatch for invalid test",
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
fn hmac_sha1() {
    test_hmac(mac::TestSet::load_hmac_sha1(), "hmac_sha1", Algorithm::Sha1);
}

#[test]
fn hmac_sha256() {
    test_hmac(
        mac::TestSet::load_hmac_sha256(),
        "hmac_sha256",
        Algorithm::Sha256,
    );
}

#[test]
fn hmac_sha384() {
    test_hmac(
        mac::TestSet::load_hmac_sha384(),
        "hmac_sha384",
        Algorithm::Sha384,
    );
}

#[test]
fn hmac_sha512() {
    test_hmac(
        mac::TestSet::load_hmac_sha512(),
        "hmac_sha512",
        Algorithm::Sha512,
    );
}
