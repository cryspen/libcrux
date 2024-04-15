//! Tests for ML-KEM

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use libcrux::kem::{self, PublicKey};

/// These tests are from https://github.com/C2SP/CCTV/
fn test_invalid_modulus(p: &str, alg: kem::Algorithm) {
    let kat_file_path = file_name(p);
    let kat_file = File::open(kat_file_path).unwrap();
    let reader = BufReader::new(kat_file);
    for line in reader.lines() {
        let line = line.unwrap();
        let pk_err = PublicKey::decode(alg, &hex::decode(line).unwrap());
        match pk_err {
            Ok(_) => panic!("This should have errored out"),
            Err(e) => eprintln!("Error {e:?}"),
        }
    }
}

#[test]
fn invalid_modulus_512() {
    test_invalid_modulus("512", kem::Algorithm::MlKem512);
}

#[test]
fn invalid_modulus_768() {
    test_invalid_modulus("768", kem::Algorithm::MlKem768);
}

#[test]
fn invalid_modulus_1024() {
    test_invalid_modulus("1024", kem::Algorithm::MlKem1024);
}

fn file_name(p: &str) -> std::path::PathBuf {
    Path::new("tests")
        .join("kyber_kats")
        .join("invalid_modulus")
        .join(format!("ML-KEM-{}.txt", p))
}
