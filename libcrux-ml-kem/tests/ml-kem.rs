// SPDX-FileCopyrightText: 2024 Cryspen Sarl <info@cryspen.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Tests for ML-KEM

/// These tests are from https://github.com/C2SP/CCTV/
fn test_invalid_modulus(p: &str) {
    use std::{
        fs::File,
        io::{BufRead, BufReader},
    };

    let kat_file_path = file_name(p);
    let kat_file = File::open(kat_file_path).unwrap();
    let reader = BufReader::new(kat_file);
    for line in reader.lines() {
        let line = line.unwrap();
        let pk = hex::decode(line).unwrap();
        let pk = pk.as_slice();
        match p {
            #[cfg(feature = "mlkem512")]
            "512" => assert!(
                libcrux_ml_kem::mlkem512::validate_public_key(pk.try_into().unwrap()).is_none()
            ),
            #[cfg(feature = "mlkem768")]
            "768" => assert!(
                libcrux_ml_kem::mlkem768::validate_public_key(pk.try_into().unwrap()).is_none()
            ),
            #[cfg(feature = "mlkem1024")]
            "1024" => assert!(libcrux_ml_kem::mlkem1024::validate_public_key(
                pk.try_into().unwrap()
            )
            .is_none()),
            _ => unreachable!(),
        };
    }
}

#[test]
#[cfg(feature = "mlkem512")]
fn invalid_modulus_512() {
    test_invalid_modulus("512");
}

#[test]
#[cfg(feature = "mlkem768")]
fn invalid_modulus_768() {
    test_invalid_modulus("768");
}

#[test]
#[cfg(feature = "mlkem1024")]
fn invalid_modulus_1024() {
    test_invalid_modulus("1024");
}

fn file_name(p: &str) -> std::path::PathBuf {
    std::path::Path::new("tests")
        .join("kats")
        .join("invalid_modulus")
        .join(format!("ML-KEM-{}.txt", p))
}
