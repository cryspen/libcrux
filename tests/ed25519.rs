use libcrux::signature::{Algorithm, Ed25519Signature, Signature};

#[test]
fn run_wycheproof() {
    for test_name in wycheproof::eddsa::TestName::all() {
        let _ = match test_name {
            wycheproof::eddsa::TestName::Ed25519 => Algorithm::Ed25519,
            _ => continue,
        };
        let test_set = wycheproof::eddsa::TestSet::load(test_name)
            .expect("error loading wycheproof test for name {test_name}");

        println!("Test Set {test_name:?}");
        for test_group in test_set.test_groups {
            let pk = &test_group.key.pk;

            for (i, test) in test_group.tests.into_iter().enumerate() {
                let comment = &test.comment;
                println!("Test {i}: {comment}");

                match test.result {
                    wycheproof::TestResult::Valid => {
                        let sig =
                            Signature::Ed25519(Ed25519Signature::from_slice(&test.sig).unwrap());
                        libcrux::signature::verify(&test.msg, &sig, pk).unwrap();
                    }
                    wycheproof::TestResult::Invalid => {
                        Ed25519Signature::from_slice(&test.sig)
                            .map(Signature::Ed25519)
                            .and_then(|sig| libcrux::signature::verify(&test.msg, &sig, pk))
                            .expect_err("expected error");
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
