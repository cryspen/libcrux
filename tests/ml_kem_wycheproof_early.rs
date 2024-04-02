use libcrux::kem;
use libcrux::kem::MlKem768PublicKey;
use serde::Deserialize;
use serde_json;

use std::path::Path;

use libcrux::digest;

use std::{fs::File, io::BufRead, io::BufReader, panic};

struct EncapsTestCase<const PK_LEN: usize> {
    comment: String,
    entropy: [u8; 32],
    public_key: [u8; PK_LEN],
    expected_result: String,
    expected_ciphertext: String,
    expected_shared_secret: String,
}

fn parse_bytes<const N: usize>(s: &str, val: &str) -> [u8; N] {
    let value_start = match s.find(val) {
        Some(val) => val,
        None => {
            panic!("Didn't find '{val}' on '{s}'");
        }
    };
    let value_start = value_start + val.len() + 3;
    let value = hex::decode(&s[value_start..]).unwrap();
    println!("{} != {}", N, value.len());
    value.try_into().unwrap()
}

macro_rules! impl_known_answer_test {
    ($name:ident, $parameter_set: literal, $key_gen_derand:expr, $encapsulate_derand:expr, $decapsulate_derand: expr, $validate_pk: expr) => {
        #[test]
        fn $name() {
            let katfile_path = Path::new("tests")
                .join("kyber_kats")
                .join("wycheproof_early")
                .join(format!("encaps{}draft", $parameter_set));
            let katfile = File::open(katfile_path).expect("Could not open KAT file.");
            let reader = BufReader::new(katfile);
            let mut lines = reader.lines();

            while let (
                Some(comment),
                Some(entropy),
                Some(public_key),
                Some(expected_result),
                Some(expected_ciphertext),
                Some(expected_shared_secret),
                _, // Always read the empty line after the test.
            ) = (
                lines.next(),
                lines.next(),
                lines.next(),
                lines.next(),
                lines.next(),
                lines.next(),
                lines.next(),
            ) {
                let comment = &comment.unwrap()["comment".len() + 3..];
                println!("{}", comment);
                let pass = expected_result.unwrap() == "pass";

                let entropy: [u8; 32] = parse_bytes(entropy.as_ref().unwrap(), "entropy");

                let pk = public_key.as_ref().unwrap();
                if !pass
                    && (comment == "Public key is too short" || comment == "Public key is too long")
                {
                    // The parsing fails already and we require the sized array.
                    let value_start = pk.find("public_key").unwrap();
                    let value_start = value_start + "public_key".len() + 3;
                    let pk = hex::decode(&pk[value_start..]).unwrap();
                    assert_ne!(pk.len(), 1184);
                    continue;
                }

                let pk: [u8; 1184] = parse_bytes(&public_key.unwrap(), "public_key");
                let (my_ciphertext, my_shared_secret) =
                    $encapsulate_derand(&MlKem768PublicKey::from(pk), entropy);

                if pass {
                    let expected_ciphertext: [u8; 1088] =
                        parse_bytes(&expected_ciphertext.unwrap(), "expected_ciphertext");
                    let expected_shared_secret: [u8; 32] =
                        parse_bytes(&expected_shared_secret.unwrap(), "expected_shared_secret");

                    assert_eq!(my_ciphertext.as_ref(), expected_ciphertext);
                    assert_eq!(my_shared_secret.as_ref(), expected_shared_secret);
                } else {
                    if comment == "Public key not reduced" {
                        assert!($validate_pk(MlKem768PublicKey::from(pk)).is_none());
                    }
                }
            }

        }
    };
}

// impl_known_answer_test!(
//     kyber512_nist_known_answer_tests,
//     512,
//     kem::deterministic::kyber512_generate_keypair_derand,
//     kem::deterministic::kyber512_encapsulate_derand,
//     kem::deterministic::kyber512_decapsulate_derand
// );
impl_known_answer_test!(
    ml_kem768_wycheproof_early_kat,
    768,
    kem::deterministic::kyber768_generate_keypair_derand,
    kem::deterministic::kyber768_encapsulate_derand,
    kem::deterministic::kyber768_decapsulate_derand,
    kem::ml_kem768_validate_public_key
);
// impl_known_answer_test!(
//     kyber1024_nist_known_answer_tests,
//     1024,
//     kem::deterministic::kyber1024_generate_keypair_derand,
//     kem::deterministic::kyber1024_encapsulate_derand,
//     kem::deterministic::kyber1024_decapsulate_derand
// );
