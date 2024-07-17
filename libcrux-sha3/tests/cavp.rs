use cavp::*;
use libcrux_sha3::*;

macro_rules! test {
    ($file:ident, $digest:ty, $algorithm:expr) => {
        #[test]
        #[allow(non_snake_case)]
        fn $file() {
            let file = "tests/tv/".to_string();
            let file = file + stringify!($file) + ".rsp";
            let tv = read_file(&file).unwrap();

            let mut c = 0;
            for test in tv.tests() {
                eprintln!("test {c}");
                c += 1;
                let my_digest: $digest = sha3($algorithm, &test.msg);
                assert_eq!(&my_digest, &test.digest[..]);
            }
        }
    };
}

test!(SHA3_224LongMsg, Sha3_224Digest, Algorithm::Sha224);
test!(SHA3_256LongMsg, Sha3_256Digest, Algorithm::Sha256);
test!(SHA3_384LongMsg, Sha3_384Digest, Algorithm::Sha384);
test!(SHA3_512LongMsg, Sha3_512Digest, Algorithm::Sha512);

test!(SHA3_224ShortMsg, Sha3_224Digest, Algorithm::Sha224);
test!(SHA3_256ShortMsg, Sha3_256Digest, Algorithm::Sha256);
test!(SHA3_384ShortMsg, Sha3_384Digest, Algorithm::Sha384);
test!(SHA3_512ShortMsg, Sha3_512Digest, Algorithm::Sha512);
