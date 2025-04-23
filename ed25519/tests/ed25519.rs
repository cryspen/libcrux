#[test]
fn run_wycheproof() {
    for test_name in wycheproof::eddsa::TestName::all() {
        if !matches!(test_name, wycheproof::eddsa::TestName::Ed25519) {
            continue;
        }

        let test_set = wycheproof::eddsa::TestSet::load(test_name)
            .expect("error loading wycheproof test for name {test_name}");

        println!("Test Set {test_name:?}");
        for (k, test_group) in test_set.test_groups.into_iter().enumerate() {
            let pk = &test_group.key.pk;
            if pk.len() != 32 {
                println!(
                    "Skipping test group {k}: public key length {} != 32",
                    pk.len()
                );
                for test in test_group.tests.into_iter() {
                    assert_eq!(test.result, wycheproof::TestResult::Invalid);
                }
                continue;
            }
            let pk_buf: [u8; 32] = pk.as_slice().try_into().unwrap();

            for (i, test) in test_group.tests.into_iter().enumerate() {
                let comment = &test.comment;
                println!("Test {i}: {comment}");

                let sig_len = test.sig.len();
                if sig_len != 64 {
                    println!("Skipping test {i}: signature length {} != 64", sig_len);
                    assert_eq!(test.result, wycheproof::TestResult::Invalid);
                    continue;
                }
                let sig_buf: [u8; 64] = test.sig.as_slice().try_into().unwrap();

                match test.result {
                    wycheproof::TestResult::Valid => {
                        libcrux_ed25519::verify(&test.msg, &pk_buf, &sig_buf).unwrap();
                    }
                    wycheproof::TestResult::Invalid => {
                        libcrux_ed25519::verify(&test.msg, &pk_buf, &sig_buf)
                            .expect_err("expected error");
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
