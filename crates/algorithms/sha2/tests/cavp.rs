use cavp::*;

macro_rules! sha2_test {
    ($file:ident, $digest_len:expr, $hash_fn:path) => {
        #[test]
        #[allow(non_snake_case)]
        fn $file() {
            let file = "tests/tv/".to_string();
            let file = file + stringify!($file) + ".rsp";
            let tv: TestVector<cavp::Sha3> = read_file(&file).unwrap();

            let mut c = 0;
            for test in &tv.tests {
                c += 1;
                let digest = $hash_fn(&test.msg[0..test.msg_length / 8]);
                assert_eq!(
                    &digest[..],
                    &test.digest[..],
                    "test {c}: digest mismatch"
                );
            }
            assert!(c > 0, "No tests were run");
            eprintln!("Ran {c} tests for {}", stringify!($file));
        }
    };
}

sha2_test!(SHA224ShortMsg, 28, libcrux_sha2::sha224);
sha2_test!(SHA224LongMsg, 28, libcrux_sha2::sha224);

sha2_test!(SHA256ShortMsg, 32, libcrux_sha2::sha256);
sha2_test!(SHA256LongMsg, 32, libcrux_sha2::sha256);

sha2_test!(SHA384ShortMsg, 48, libcrux_sha2::sha384);
sha2_test!(SHA384LongMsg, 48, libcrux_sha2::sha384);

sha2_test!(SHA512ShortMsg, 64, libcrux_sha2::sha512);
sha2_test!(SHA512LongMsg, 64, libcrux_sha2::sha512);
