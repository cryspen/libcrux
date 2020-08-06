use evercrypt::prelude::*;

use crate::kdf;
use crate::kem::*;
use crate::util::*;

type PK = Vec<u8>;
type SK = Vec<u8>;

pub(crate) struct DhKem {
    encoded_pk_len: usize,
    sk_len: usize,
    kdf: kdf::Kdf,
    dh_id: ecdh::Mode,
}

impl DhKem {
    pub fn init(kdf_id: kdf::Mode, dh_id: ecdh::Mode) -> Self {
        Self {
            sk_len: 32,
            encoded_pk_len: match dh_id {
                ecdh::Mode::X25519 => 32,
                ecdh::Mode::P256 => 64,
            },
            kdf: kdf::Kdf::new(kdf_id),
            dh_id: dh_id,
        }
    }
    fn dh(&self, sk: &[u8], pk: &[u8]) -> Vec<u8> {
        // TODO: error handling
        let out = ecdh_derive(self.dh_id, pk, sk).unwrap();
        let out = match self.dh_id {
            ecdh::Mode::X25519 => {
                out
            },
            ecdh::Mode::P256 => {
                // This isn't great :(
                let mut tmp = vec![0x04];
                tmp.extend(out);
                tmp
            },
        };
        out
    }

    fn dh_base(&self, sk: &[u8]) -> Vec<u8> {
        let out = ecdh_derive_base(self.dh_id, sk).unwrap();
        match self.dh_id {
            ecdh::Mode::X25519 => {
                out
            },
            ecdh::Mode::P256 => {
                let mut tmp = vec![0x04];
                tmp.extend(out);
                tmp
            },
        }
    }

    fn extract_and_expand(&self, pk: PK, kem_context: &[u8], suite_id: &[u8]) -> Vec<u8> {
        let prk = self.kdf.labeled_extract(&[], suite_id, "eae_prk", &pk);
        self.kdf
            .labeled_expand(&prk, suite_id, "zz", kem_context, self.get_secret_len())
    }

    fn derive_key_pair(&self, ikm: &[u8], suite_id: &[u8]) -> (PK, SK) {
        let dpk_prk = self.kdf.labeled_extract(&[], suite_id, "dpk_prk", ikm);

        let sk = match self.dh_id {
            ecdh::Mode::X25519 => {
                self.kdf
                    .labeled_expand(&dpk_prk, suite_id, "sk", &[], self.sk_len)
            }
            ecdh::Mode::P256 => {
                let ctr = 0u8;
                // FIXME: this currently produces invalid keys sometimes.
                // loop {
                self.kdf.labeled_expand(
                    &dpk_prk,
                    suite_id,
                    "candidate",
                    &ctr.to_be_bytes(),
                    self.sk_len - 1,
                )
                // }
            }
        };
        (self.dh_base(&sk).to_vec(), sk)
    }

    fn marshal(&self, pk: &[u8]) -> Vec<u8> {
        pk.to_vec()
    }

    fn unmarshal(&self, enc: &[u8]) -> Vec<u8> {
        enc.to_vec()
    }
}

impl KemTrait for DhKem {
    fn get_secret_len(&self) -> usize {
        self.sk_len
    }
    fn get_encoded_pk_len(&self) -> usize {
        self.encoded_pk_len
    }

    fn new(_kdf_id: kdf::Mode) -> Self {
        panic!("Don't use this please");
    }

    fn encaps(&self, pk_r: &[u8], suite_id: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let (pk_e, sk_e) = self.derive_key_pair(&get_random_vec(self.get_secret_len()), suite_id);
        let dh_pk = self.dh(&sk_e, pk_r);
        let enc = self.marshal(&pk_e);

        let pk_rm = self.marshal(pk_r);
        let kem_context = concat(&[&enc, &pk_rm]);

        let zz = self.extract_and_expand(dh_pk.to_vec(), &kem_context, suite_id);
        (zz, enc)
    }

    fn decaps(&self, enc: &[u8], sk_r: &[u8], suite_id: &[u8]) -> Vec<u8> {
        let pk_e = self.unmarshal(enc);
        let dh_pk = self.dh(sk_r, &pk_e);

        let pk_rm = self.marshal(&self.dh_base(sk_r));
        let kem_context = concat(&[&enc, &pk_rm]);

        self.extract_and_expand(dh_pk.to_vec(), &kem_context, suite_id)
    }
    fn auth_encaps(&self, pk_r: &[u8], sk_s: &[u8], suite_id: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let (pk_e, sk_e) = self.derive_key_pair(&get_random_vec(self.get_secret_len()), suite_id);
        let dh_pk = concat(&[&self.dh(&sk_e, pk_r), &self.dh(&sk_s, pk_r)]);

        let enc = self.marshal(&pk_e);
        let pk_rm = self.marshal(&pk_r);
        let pk_sm = self.marshal(&self.dh_base(&sk_s));

        let kem_context = concat(&[&enc, &pk_rm, &pk_sm]);

        let zz = self.extract_and_expand(dh_pk.to_vec(), &kem_context, suite_id);
        (zz, enc)
    }
    fn auth_decaps(&self, enc: &[u8], sk_r: &[u8], pk_s: &[u8], suite_id: &[u8]) -> Vec<u8> {
        let pk_e = self.unmarshal(enc);
        let dh_pk = concat(&[&self.dh(sk_r, &pk_e), &self.dh(sk_r, &pk_s)]);

        let pk_rm = self.marshal(&self.dh_base(sk_r));
        let pk_sm = self.marshal(&pk_s);
        let kem_context = concat(&[&enc, &pk_rm, &pk_sm]);

        self.extract_and_expand(dh_pk.to_vec(), &kem_context, suite_id)
    }
}
