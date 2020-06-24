use std::convert::TryInto;

use x25519_dalek;

use crate::kdf;
use crate::kem::*;
use crate::util::*;

type PK = Vec<u8>;
type SK = Vec<u8>;

pub trait Curve {
    const SK_LEN: usize;
    const ENC_PK_LEN: usize;
}

pub(crate) struct X25519Kem {
    kdf: kdf::Kdf,
}

impl X25519Kem {
    fn dh(&self, sk: &[u8], pk: &[u8]) -> [u8; 32] {
        x25519_dalek::x25519(
            sk.try_into().expect("secret key has incorrect length"),
            pk.try_into().expect("public key has incorrect length"),
        )
    }

    fn dh_base(&self, sk: &[u8]) -> [u8; 32] {
        x25519_dalek::x25519(
            sk.try_into().expect("secret key has incorrect length"),
            x25519_dalek::X25519_BASEPOINT_BYTES,
        )
    }

    fn extract_and_expand(&self, pk: PK, kem_context: &[u8]) -> Vec<u8> {
        let prk = self.kdf.labeled_extract(&[], "dh", &pk);
        self.kdf
            .labeled_expand(&prk, "prk", kem_context, self.get_secret_len())
    }

    fn derive_key_pair(&self, ikm: &[u8]) -> (PK, SK) {
        (self.dh_base(ikm).to_vec(), ikm.to_vec())
    }

    fn marshal(&self, pk: &[u8]) -> Vec<u8> {
        pk.to_vec()
    }

    fn unmarshal(&self, enc: &[u8]) -> Vec<u8> {
        enc.to_vec()
    }
}

impl KemTrait for X25519Kem {
    fn get_secret_len(&self) -> usize {
        32 // K::HASH_LEN
    }
    fn get_seed_len(&self) -> usize {
        32 // C::SK_LEN
    }
    fn get_encoded_pk_len(&self) -> usize {
        32 // C::ENCODED_PK_LEN
    }

    fn new() -> Self {
        Self {
            kdf: kdf::Kdf::new(kdf::Mode::HkdfSha256),
        }
    }

    fn encaps(&self, pk_r: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let (pk_e, sk_e) = self.derive_key_pair(&random(self.get_secret_len()));
        let dh_pk = self.dh(&sk_e, pk_r);
        let enc = self.marshal(&pk_e);

        let pk_rm = self.marshal(pk_r);
        let kem_context = concat(&[&enc, &pk_rm]);

        let zz = self.extract_and_expand(dh_pk.to_vec(), &kem_context);
        (zz, enc)
    }

    fn decaps(&self, enc: &[u8], sk_r: &[u8]) -> Vec<u8> {
        let pk_e = self.unmarshal(enc);
        let dh_pk = self.dh(sk_r, &pk_e);

        let pk_rm = self.marshal(&self.dh_base(sk_r));
        let kem_context = concat(&[&enc, &pk_rm]);

        self.extract_and_expand(dh_pk.to_vec(), &kem_context)
    }
    fn auth_encaps(&self, _pk_r: &[u8], _sk_s: &[u8]) -> (Vec<u8>, Vec<u8>) {
        unimplemented!();
    }
    fn auth_decaps(&self, _enc: &[u8], _sk_r: &[u8], _pk_s: &[u8]) -> Vec<u8> {
        unimplemented!();
    }
}
