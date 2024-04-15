#![no_main]

use libcrux::hpke::{kem::GenerateKeyPair, HPKEConfig, SetupAuthPSKR};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() != 96 {
        return;
    }

    let kem_mode = libcrux::hpke::kem::KEM::DHKEM_P256_HKDF_SHA256;
    let config = HPKEConfig(
        libcrux::hpke::Mode::mode_auth_psk,
        kem_mode,
        libcrux::hpke::kdf::KDF::HKDF_SHA256,
        libcrux::hpke::aead::AEAD::ChaCha20Poly1305,
    );
    let info = vec![
        0x4f, 0x64, 0x65, 0x20, 0x6f, 0x6e, 0x20, 0x61, 0x20, 0x47, 0x72, 0x65, 0x63, 0x69, 0x61,
        0x6e, 0x20, 0x55, 0x72, 0x6e,
    ];
    let psk = vec![
        0x02, 0x47, 0xfd, 0x33, 0xb9, 0x13, 0x76, 0x0f, 0xa1, 0xfa, 0x51, 0xe1, 0x89, 0x2d, 0x9f,
        0x30,
    ];
    let psk_id = vec![
        0x02, 0x47, 0xfd, 0x33, 0xb9, 0x13, 0x76, 0x0f, 0xa1, 0xfa, 0x51, 0xe1, 0x89, 0x2d, 0x9f,
        0x30,
    ];

    let (_sk_sm, pk_sm) = GenerateKeyPair(kem_mode, data[0..32].to_vec()).unwrap();
    let (_sk, enc) = GenerateKeyPair(kem_mode, data[32..64].to_vec()).unwrap();
    let (sk_rm, _pk_rm) = GenerateKeyPair(kem_mode, data[64..96].to_vec()).unwrap();

    let _ = SetupAuthPSKR(config, &enc, &sk_rm, &info, &psk, &psk_id, &pk_sm).unwrap();
});
