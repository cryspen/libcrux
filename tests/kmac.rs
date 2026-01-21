#[test]
fn run_wycheproof() {
    for test_name in wycheproof::mac::TestName::all() {
        let kmac = match test_name {
            wycheproof::mac::TestName::Kmac128 => libcrux_kmac::kmac_128,
            wycheproof::mac::TestName::Kmac256 => libcrux_kmac::kmac_256,
            _ => continue,
        };
        let test_set = wycheproof::mac::TestSet::load(test_name)
            .expect("error loading wycheproof test for name {test_name}");

        println!("Test Set {test_name:?}");
        for test_group in test_set.test_groups {
            let tag_size = test_group.tag_size;
            for (i, test) in test_group.tests.into_iter().enumerate() {
                let comment = &test.comment;
                println!("Test {i}: {comment}");
                let mut tag = vec![0; tag_size >> 3];
                let tag = kmac(tag.as_mut_slice(), &test.key, &test.msg, &[]);

                match test.result {
                    wycheproof::TestResult::Valid => assert_eq!(tag, test.tag.as_ref()),
                    wycheproof::TestResult::Invalid => {
                        assert_ne!(tag, test.tag.as_ref())
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
