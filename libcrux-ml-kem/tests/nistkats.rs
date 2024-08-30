use serde::Deserialize;
use serde_json;
use std::{fs::File, io::BufReader, path::Path};

use libcrux_sha3::*;

#[derive(Deserialize)]
struct MlKemNISTKAT {
    #[serde(with = "hex::serde")]
    key_generation_seed: [u8; 64],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_public_key: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_secret_key: [u8; 32],

    #[serde(with = "hex::serde")]
    encapsulation_seed: [u8; 32],

    #[serde(with = "hex::serde")]
    sha3_256_hash_of_ciphertext: [u8; 32],

    #[serde(with = "hex::serde")]
    shared_secret: [u8; 32],
}

macro_rules! impl_nist_known_answer_tests {
    ($name:ident, $variant:literal, $parameter_set:literal, $module:path) => {
        #[test]
        fn $name() {
            use $module::*;

            let katfile_path = Path::new("tests")
                .join("kats")
            .join(format!("nistkats_{}_{}.json", $variant, $parameter_set));
            let katfile = File::open(katfile_path).expect("Could not open KAT file.");
            let reader = BufReader::new(katfile);

            let nist_kats: Vec<MlKemNISTKAT> =
                serde_json::from_reader(reader).expect("Could not deserialize KAT file.");

            for kat in nist_kats {
                let key_pair = generate_key_pair(kat.key_generation_seed);

                #[cfg(feature = "pre-verification")]
                assert!(validate_public_key(key_pair.public_key()));

                let public_key_hash = sha256(key_pair.pk());
                eprintln!("pk hash: {}", hex::encode(public_key_hash));
                let secret_key_hash = sha256(key_pair.sk());

                assert_eq!(public_key_hash, kat.sha3_256_hash_of_public_key, "lhs: computed public key hash, rhs: hash from kat");
                assert_eq!(secret_key_hash, kat.sha3_256_hash_of_secret_key, "lhs: computed secret key hash, rhs: hash from kat");

                let (ciphertext, shared_secret) =
                encapsulate(key_pair.public_key(), kat.encapsulation_seed);
                let ciphertext_hash = sha256(ciphertext.as_ref());

                assert_eq!(ciphertext_hash, kat.sha3_256_hash_of_ciphertext, "lhs: computed ciphertext hash, rhs: hash from akt");
                assert_eq!(shared_secret.as_ref(), kat.shared_secret, "lhs: computed shared secret from encapsulate, rhs: shared secret from kat");

                #[cfg(feature = "pre-verification")]
                assert!(validate_private_key(key_pair.private_key(), &ciphertext));

                let shared_secret_from_decapsulate =
                decapsulate(key_pair.private_key(), &ciphertext);
                assert_eq!(shared_secret_from_decapsulate, shared_secret.as_ref(), "lhs: shared secret computed via decapsulation, rhs: shared secret computed via encapsulation");
            }
        }
    };
}
#[cfg(all(not(feature = "pre-verification"), feature = "mlkem512"))]
impl_nist_known_answer_tests!(
    mlkem512_nist_known_answer_tests,
    "mlkem_ipd",
    512,
    libcrux_ml_kem::mlkem512
);

#[cfg(all(not(feature = "pre-verification"), feature = "mlkem768"))]
impl_nist_known_answer_tests!(
    mlkem768_nist_known_answer_tests,
    "mlkem_ipd",
    768,
    libcrux_ml_kem::mlkem768
);

#[cfg(all(not(feature = "pre-verification"), feature = "mlkem1024"))]
impl_nist_known_answer_tests!(
    mlkem1024_nist_known_answer_tests,
    "mlkem_ipd",
    1024,
    libcrux_ml_kem::mlkem1024
);

#[cfg(all(feature = "mlkem512", feature = "pre-verification"))]
impl_nist_known_answer_tests!(
    mlkem512_nist_kats_portable,
    "mlkem",
    512,
    libcrux_ml_kem::mlkem512::portable
);

#[cfg(all(feature = "mlkem768", feature = "pre-verification"))]
impl_nist_known_answer_tests!(
    mlkem768_nist_kats_portable,
    "mlkem",
    768,
    libcrux_ml_kem::mlkem768::portable
);

#[cfg(all(feature = "mlkem1024", feature = "pre-verification"))]
impl_nist_known_answer_tests!(
    mlkem1024_nist_kats_portable,
    "mlkem",
    1024,
    libcrux_ml_kem::mlkem1024::portable
);

#[cfg(all(feature = "mlkem512", feature = "kyber", feature = "pre-verification"))]
impl_nist_known_answer_tests!(
    kyber512_nist_kats_portable,
    "kyber",
    512,
    libcrux_ml_kem::kyber512
);

#[cfg(all(feature = "mlkem768", feature = "kyber", feature = "pre-verification"))]
impl_nist_known_answer_tests!(
    kyber768_nist_kats_portable,
    "kyber",
    768,
    libcrux_ml_kem::kyber768
);

#[cfg(all(feature = "mlkem1024", feature = "kyber", feature = "pre-verification"))]
impl_nist_known_answer_tests!(
    kyber1024_nist_kats_portable,
    "kyber",
    1024,
    libcrux_ml_kem::kyber1024
);
