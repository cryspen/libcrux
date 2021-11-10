#![no_main]
use libfuzzer_sys::fuzz_target;

use hpke_rs::prelude::*;
use hpke_rs_crypto::types::*;

fuzz_target!(|data: &[u8]| {
    let hpke = Hpke::<hpke_rs_rust_crypto::HpkeRustCrypto>::new(
        HpkeMode::Base,
        KemAlgorithm::DhKemP256,
        KdfAlgorithm::HkdfSha256,
        AeadAlgorithm::Aes128Gcm,
    );

    let pk_r = HpkePublicKey::new(data.to_vec());
    let sk_r = HpkePrivateKey::new(data.to_vec());
    let info = b"HPKE self test info";
    let aad = b"HPKE self test aad";
    let plain_txt = b"HPKE self test plain text";
    let _ = hpke.seal(&pk_r, info, aad, plain_txt, None, None, None);
    let _ = hpke.open(data, &sk_r, info, aad, data, None, None, None);
});
