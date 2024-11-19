use libcrux_hmac::Algorithm;

#[test]
fn run_wycheproof() {
    for test_name in wycheproof::mac::TestName::all() {
        let alg = match test_name {
            wycheproof::mac::TestName::HmacSha1 => Algorithm::Sha1,
            wycheproof::mac::TestName::HmacSha256 => Algorithm::Sha256,
            wycheproof::mac::TestName::HmacSha384 => Algorithm::Sha384,
            wycheproof::mac::TestName::HmacSha512 => Algorithm::Sha512,
            _ => continue,
        };
        let test_set = wycheproof::mac::TestSet::load(test_name)
            .expect("error loading wycheproof test for name {test_name}");

        println!("Test Set {test_name:?}");
        for test_group in test_set.test_groups {
            for (i, test) in test_group.tests.into_iter().enumerate() {
                let comment = &test.comment;
                println!("Test {i}: {comment}");

                let tag = libcrux_hmac::hmac(alg, &test.key, &test.msg, Some(test.tag.len()));

                match test.result {
                    wycheproof::TestResult::Valid => assert_eq!(tag.as_slice(), test.tag.as_ref()),
                    wycheproof::TestResult::Invalid => {
                        assert_ne!(tag.as_slice(), test.tag.as_ref())
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
