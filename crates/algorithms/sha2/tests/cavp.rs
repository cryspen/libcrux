macro_rules! sha2_test {
    ($test_name:ident, $kats_fn:path, $hash_fn:path) => {
        #[test]
        #[allow(non_snake_case)]
        fn $test_name() {
            let tv = $kats_fn();
            let mut c = 0;
            for test in &tv.tests {
                c += 1;
                let digest = $hash_fn(&test.msg[0..test.msg_length / 8]);
                assert_eq!(&digest[..], &test.digest[..], "test {c}: digest mismatch");
            }
            assert!(c > 0, "No tests were run");
            eprintln!("Ran {c} tests for {}", stringify!($test_name));
        }
    };
}

sha2_test!(SHA224ShortMsg, libcrux_kats::sha2::sha224_short, libcrux_sha2::sha224);
sha2_test!(SHA224LongMsg, libcrux_kats::sha2::sha224_long, libcrux_sha2::sha224);

sha2_test!(SHA256ShortMsg, libcrux_kats::sha2::sha256_short, libcrux_sha2::sha256);
sha2_test!(SHA256LongMsg, libcrux_kats::sha2::sha256_long, libcrux_sha2::sha256);

sha2_test!(SHA384ShortMsg, libcrux_kats::sha2::sha384_short, libcrux_sha2::sha384);
sha2_test!(SHA384LongMsg, libcrux_kats::sha2::sha384_long, libcrux_sha2::sha384);

sha2_test!(SHA512ShortMsg, libcrux_kats::sha2::sha512_short, libcrux_sha2::sha512);
sha2_test!(SHA512LongMsg, libcrux_kats::sha2::sha512_long, libcrux_sha2::sha512);
