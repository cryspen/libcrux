use cavp::*;
use libcrux_sha3::*;

macro_rules! sha3_test {
    ($file:ident, $digest:ty, $algorithm:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $file() {
            let file = "tests/tv/".to_string();
            let file = file + stringify!($file) + ".rsp";
            let tv: TestVector<cavp::Sha3> = read_file(&file).unwrap();

            let mut c = 0;
            for test in &tv.tests {
                eprintln!("test {c}");
                c += 1;
                let my_digest: $digest = sha3($algorithm, &test.msg[0..test.msg_length / 8]);
                assert_eq!(&my_digest, &test.digest[..]);
            }
        }
    };
}

sha3_test!(SHA3_224LongMsg, Sha3_224Digest, Algorithm::Sha224);
sha3_test!(SHA3_256LongMsg, Sha3_256Digest, Algorithm::Sha256);
sha3_test!(SHA3_384LongMsg, Sha3_384Digest, Algorithm::Sha384);
sha3_test!(SHA3_512LongMsg, Sha3_512Digest, Algorithm::Sha512);

sha3_test!(SHA3_224ShortMsg, Sha3_224Digest, Algorithm::Sha224);
sha3_test!(SHA3_256ShortMsg, Sha3_256Digest, Algorithm::Sha256);
sha3_test!(SHA3_384ShortMsg, Sha3_384Digest, Algorithm::Sha384);
sha3_test!(SHA3_512ShortMsg, Sha3_512Digest, Algorithm::Sha512);

macro_rules! shake_test {
    ($file:ident, $shake:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $file() {
            let _ = pretty_env_logger::try_init();
            let file = "tests/tv/".to_string();
            let file = file + stringify!($file) + ".rsp";
            let tv: TestVector<cavp::ShakeMsg> = read_file(&file).unwrap();

            let mut c = 0;
            for test in &tv.tests {
                eprintln!("test {c}");
                c += 1;
                let mut my_digest = vec![0u8; test.digest.len()];
                $shake(&mut my_digest, &test.msg[0..test.msg_length / 8]);
                assert_eq!(&my_digest, &test.digest[..]);
            }
        }
    };
}

shake_test!(SHAKE128LongMsg, shake128_ema);
shake_test!(SHAKE128ShortMsg, shake128_ema);

shake_test!(SHAKE256LongMsg, shake256_ema);
shake_test!(SHAKE256ShortMsg, shake256_ema);

macro_rules! shake_vo_test {
    ($file:ident, $shake:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $file() {
            let _ = pretty_env_logger::try_init();
            let file = "tests/tv/".to_string();
            let file = file + stringify!($file) + ".rsp";
            let tv: TestVector<cavp::ShakeVariableOut> = read_file(&file).unwrap();

            let mut c = 0;
            for test in &tv.tests {
                eprintln!("test {c}");
                c += 1;
                let mut my_digest = vec![0u8; test.digest.len()];
                $shake(&mut my_digest, &test.msg[0..tv.header.input_length / 8]);
                assert_eq!(&my_digest, &test.digest[..]);
            }
        }
    };
}
shake_vo_test!(SHAKE128VariableOut, shake128_ema);
shake_vo_test!(SHAKE256VariableOut, shake256_ema);
