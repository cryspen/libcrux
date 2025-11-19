use libcrux_hkdf::Algorithm;
use wycheproof::TestResult;

#[test]
fn run_wycheproof() {
    for test_name in wycheproof::hkdf::TestName::all() {
        let alg = match test_name {
            wycheproof::hkdf::TestName::HkdfSha1 => continue,
            wycheproof::hkdf::TestName::HkdfSha256 => Algorithm::Sha256,
            wycheproof::hkdf::TestName::HkdfSha384 => Algorithm::Sha384,
            wycheproof::hkdf::TestName::HkdfSha512 => Algorithm::Sha512,
        };
        let test_set = wycheproof::hkdf::TestSet::load(test_name)
            .expect("error loading wycheproof test for name {test_name}");

        println!("Test Set {test_name:?}");
        for test_group in test_set.test_groups {
            for (i, test) in test_group.tests.into_iter().enumerate() {
                let comment = &test.comment;
                println!("Test {i}: {comment}");

                let result = libcrux_hkdf::hkdf(alg, &test.salt, &test.ikm, &test.info, test.size);
                match (result, test.result) {
                    (Ok(okm), TestResult::Valid) => {
                        assert_eq!(okm.as_slice(), test.okm.as_ref())
                    }
                    (Err(_), TestResult::Invalid) => {}
                    other => {
                        panic!("found failing test case: {test:?}, got {other:?}")
                    }
                }
            }
        }
    }
}
