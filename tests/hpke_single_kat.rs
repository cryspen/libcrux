mod test_util;
use test_util::*;

use libcrux::hpke::aead::AEAD::*;
use libcrux::hpke::kdf::KDF::*;
use libcrux::hpke::kem::KEM::*;
use libcrux::hpke::{Mode::*, *};

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn single_kat_base() {
    let _ = pretty_env_logger::try_init();

    // A.2.1.1.
    let config = HPKEConfig(
        mode_base,
        DHKEM_X25519_HKDF_SHA256,
        HKDF_SHA256,
        ChaCha20Poly1305,
    );
    let pk_r = hex_str_to_bytes("4310ee97d88cc1f088a5576c77ab0cf5c3ac797f3d95139c6c84b5429c59662a");
    let info = hex_str_to_bytes("4f6465206f6e2061204772656369616e2055726e");
    let aad = hex_str_to_bytes("436f756e742d30");
    let ptxt = hex_str_to_bytes("4265617574792069732074727574682c20747275746820626561757479");
    let randomness =
        hex_str_to_bytes("909a9b35d3dc4713a5e72a4da274b55d3d3821a37e5d099e74a647db583a904b");

    let HPKECiphertext(enc, ct) = HpkeSeal(
        config, &pk_r, &info, &aad, &ptxt, None, None, None, randomness,
    )
    .expect("Error in hpke seal");
    assert_eq!(
        hex_str_to_bytes(
            "1c5250d8034ec2b784ba2cfd69dbdb8af406cfe3ff938e131f0def8c8b60b4db21993c62ce81883d2dd1b51a28"
        ),
        ct,
    );

    let sk_r = hex_str_to_bytes("8057991eef8f1f1af18f4a9491d16a1ce333f695d4db8e38da75975c4478e0fb");
    let decrypted_ptxt = HpkeOpen(
        config,
        &HPKECiphertext(enc, ct),
        &sk_r,
        &info,
        &aad,
        None,
        None,
        None,
    )
    .expect("Error opening hpke ciphertext");
    assert_eq!(ptxt, decrypted_ptxt);
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn single_kat_psk() {
    // A.2.2
    let config = HPKEConfig(
        mode_psk,
        DHKEM_X25519_HKDF_SHA256,
        HKDF_SHA256,
        ChaCha20Poly1305,
    );
    let info = hex_str_to_bytes("4f6465206f6e2061204772656369616e2055726e");
    let randomness =
        hex_str_to_bytes("35706a0b09fb26fb45c39c2f5079c709c7cf98e43afa973f14d88ece7e29c2e3");
    let pk_r = hex_str_to_bytes("13640af826b722fc04feaa4de2f28fbd5ecc03623b317834e7ff4120dbe73062");
    let psk = &hex_str_to_bytes("0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82");
    let psk_id = &hex_str_to_bytes("456e6e796e20447572696e206172616e204d6f726961");

    // A.2.2.1
    let aad = hex_str_to_bytes("436f756e742d30");
    let ptxt = hex_str_to_bytes("4265617574792069732074727574682c20747275746820626561757479");

    let HPKECiphertext(enc, ct) = HpkeSeal(
        config,
        &pk_r,
        &info,
        &aad,
        &ptxt,
        Some(psk),
        Some(psk_id),
        None,
        randomness,
    )
    .expect("Error in hpke seal");
    assert_eq!(
        hex_str_to_bytes(
            "4a177f9c0d6f15cfdf533fb65bf84aecdc6ab16b8b85b4cf65a370e07fc1d78d28fb073214525276f4a89608ff"
        ),
        ct,
    );

    let sk_r = hex_str_to_bytes("77d114e0212be51cb1d76fa99dd41cfd4d0166b08caa09074430a6c59ef17879");
    let decrypted_ptxt = HpkeOpen(
        config,
        &HPKECiphertext(enc, ct),
        &sk_r,
        &info,
        &aad,
        Some(psk),
        Some(psk_id),
        None,
    )
    .expect("Error opening hpke ciphertext");
    assert_eq!(ptxt, decrypted_ptxt);
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn single_kat_auth() {
    // A.2.3
    let config = HPKEConfig(
        mode_auth,
        DHKEM_X25519_HKDF_SHA256,
        HKDF_SHA256,
        ChaCha20Poly1305,
    );
    let info = hex_str_to_bytes("4f6465206f6e2061204772656369616e2055726e");
    let randomness =
        hex_str_to_bytes("938d3daa5a8904540bc24f48ae90eed3f4f7f11839560597b55e7c9598c996c0");
    let pk_r = hex_str_to_bytes("1a478716d63cb2e16786ee93004486dc151e988b34b475043d3e0175bdb01c44");
    let sk_s = hex_str_to_bytes("2def0cb58ffcf83d1062dd085c8aceca7f4c0c3fd05912d847b61f3e54121f05");

    // A.2.3.1
    let aad = hex_str_to_bytes("436f756e742d30");
    let ptxt = hex_str_to_bytes("4265617574792069732074727574682c20747275746820626561757479");

    let HPKECiphertext(enc, ct) = HpkeSeal(
        config,
        &pk_r,
        &info,
        &aad,
        &ptxt,
        None,
        None,
        Some(&sk_s),
        randomness,
    )
    .expect("Error in hpke seal");
    assert_eq!(
        hex_str_to_bytes(
            "ab1a13c9d4f01a87ec3440dbd756e2677bd2ecf9df0ce7ed73869b98e00c09be111cb9fdf077347aeb88e61bdf"
        ),
        ct,
    );

    let sk_r = hex_str_to_bytes("3ca22a6d1cda1bb9480949ec5329d3bf0b080ca4c45879c95eddb55c70b80b82");
    let pk_s = hex_str_to_bytes("f0f4f9e96c54aeed3f323de8534fffd7e0577e4ce269896716bcb95643c8712b");
    let decrypted_ptxt = HpkeOpen(
        config,
        &HPKECiphertext(enc, ct),
        &sk_r,
        &info,
        &aad,
        None,
        None,
        Some(&pk_s),
    )
    .expect("Error opening hpke ciphertext");
    assert_eq!(ptxt, decrypted_ptxt);
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn single_kat_auth_psk() {
    // A.2.4
    let config = HPKEConfig(
        mode_auth_psk,
        DHKEM_X25519_HKDF_SHA256,
        HKDF_SHA256,
        ChaCha20Poly1305,
    );
    let info = hex_str_to_bytes("4f6465206f6e2061204772656369616e2055726e");
    let randomness =
        hex_str_to_bytes("49d6eac8c6c558c953a0a252929a818745bb08cd3d29e15f9f5db5eb2e7d4b84");
    let pk_r = hex_str_to_bytes("a5099431c35c491ec62ca91df1525d6349cb8aa170c51f9581f8627be6334851");
    let sk_s = hex_str_to_bytes("90761c5b0a7ef0985ed66687ad708b921d9803d51637c8d1cb72d03ed0f64418");
    let psk = &hex_str_to_bytes("0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82");
    let psk_id = &hex_str_to_bytes("456e6e796e20447572696e206172616e204d6f726961");

    // A.2.4.1
    let aad = hex_str_to_bytes("436f756e742d30");
    let ptxt = hex_str_to_bytes("4265617574792069732074727574682c20747275746820626561757479");

    let HPKECiphertext(enc, ct) = HpkeSeal(
        config,
        &pk_r,
        &info,
        &aad,
        &ptxt,
        Some(psk),
        Some(psk_id),
        Some(&sk_s),
        randomness,
    )
    .expect("Error in hpke seal");
    assert_eq!(
        hex_str_to_bytes(
            "9aa52e29274fc6172e38a4461361d2342585d3aeec67fb3b721ecd63f059577c7fe886be0ede01456ebc67d597"
        ),
        ct,
    );

    let sk_r = hex_str_to_bytes("7b36a42822e75bf3362dfabbe474b3016236408becb83b859a6909e22803cb0c");
    let pk_s = hex_str_to_bytes("3ac5bd4dd66ff9f2740bef0d6ccb66daa77bff7849d7895182b07fb74d087c45");
    let decrypted_ptxt = HpkeOpen(
        config,
        &HPKECiphertext(enc, ct),
        &sk_r,
        &info,
        &aad,
        Some(psk),
        Some(psk_id),
        Some(&pk_s),
    )
    .expect("Error opening hpke ciphertext");
    assert_eq!(ptxt, decrypted_ptxt);
}
