#![no_main]
use libfuzzer_sys::fuzz_target;

use hpke_rs::prelude::*;

fuzz_target!(|data: &[u8]| {
    let hpke = Hpke::new(
        HpkeMode::Base,
        HpkeKemMode::DhKemP256,
        HpkeKdfMode::HkdfSha256,
        HpkeAeadMode::AesGcm128,
    );

    let pk_r = HPKEPublicKey::new(data.to_vec());
    let sk_r = HPKEPrivateKey::new(data.to_vec());
    let info = b"HPKE self test info";
    let aad = b"HPKE self test aad";
    let plain_txt = b"HPKE self test plain text";
    let _ = hpke.seal(&pk_r, info, aad, plain_txt, None, None, None);
    let _ = hpke.open(data, &sk_r, info, aad, data, None, None, None);
});
