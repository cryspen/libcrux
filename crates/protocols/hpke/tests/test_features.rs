extern crate hpke_rs as hpke;

#[cfg(feature = "serialization")]
use evercrypt::prelude::*;

#[cfg(feature = "serialization")]
use hpke::prelude::*;

use hpke::{HPKEKeyPair, HPKEPrivateKey, HPKEPublicKey};

#[test]
#[cfg(feature = "serialization")]
fn test_serialization() {
    let hpke = Hpke::new(
        HpkeMode::Base,
        HpkeKemMode::DhKem25519,
        HpkeKdfMode::HkdfSha256,
        HpkeAeadMode::AesGcm256,
    );
    let hpke_serialized = serde_json::to_string(&hpke).unwrap();
    let hpke_out: Hpke = serde_json::from_str(&hpke_serialized).unwrap();
    assert_eq!(format!("{}", hpke), format!("{}", hpke_out));

    let aead_mode = AeadMode::Aes256Gcm;
    let serialized_mode = serde_json::to_string(&aead_mode).unwrap();
    let aead_mode_out: AeadMode = serde_json::from_str(&serialized_mode).unwrap();
    assert_eq!(aead_mode, aead_mode_out);
}

#[test]
fn deprecation() {
    let _pk = HPKEPublicKey::new(vec![1, 2, 3, 4]);
    let _sk = HPKEPrivateKey::new(vec![1, 2, 3, 4]);
    let _key_pair = HPKEKeyPair::new(vec![1, 2, 3, 4], vec![1, 2, 3, 4]);
}
