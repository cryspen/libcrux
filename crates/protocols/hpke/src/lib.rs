pub mod aead;
mod aead_impl;
pub mod dh_kem;
mod hkdf;
pub mod kdf;
pub mod kem;

mod util;

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum Mode {
    Base = 0x00,
    Psk = 0x01,
    Auth = 0x02,
    AuthPsk = 0x03,
}

impl From<u16> for Mode {
    fn from(x: u16) -> Mode {
        match x {
            0x00 => Mode::Base,
            0x01 => Mode::Psk,
            0x02 => Mode::Auth,
            0x03 => Mode::AuthPsk,
            _ => panic!("Unknown HPKE Mode {}", x),
        }
    }
}

// TODO: Do we need this?
#[allow(dead_code)]
fn get_kdf_for_kem(mode: kem::Mode) -> kdf::Mode {
    match mode {
        kem::Mode::DhKemP256 => kdf::Mode::HkdfSha256,
        kem::Mode::DhKemP384 => kdf::Mode::HkdfSha384,
        kem::Mode::DhKemP521 => kdf::Mode::HkdfSha512,
        kem::Mode::DhKem25519 => kdf::Mode::HkdfSha256,
        kem::Mode::DhKem448 => kdf::Mode::HkdfSha512,
    }
}

// TODO: add types

pub struct Context<'a> {
    key: Vec<u8>,
    nonce: Vec<u8>,
    exporter_secret: Vec<u8>,
    sequence_number: u32,
    hpke: &'a Hpke,
}

impl<'a> Context<'a> {
    pub fn seal(&mut self, aad: &[u8], plain_txt: &[u8]) -> Vec<u8> {
        let ctxt = self
            .hpke
            .aead
            .seal(&self.key, &self.compute_nonce(), aad, plain_txt);
        self.increment_seq();
        ctxt
    }

    pub fn open(&mut self, aad: &[u8], cipher_txt: &[u8]) -> Vec<u8> {
        match self
            .hpke
            .aead
            .open(&self.key, &self.compute_nonce(), aad, cipher_txt)
        {
            Ok(plain_txt) => {
                self.increment_seq();
                plain_txt
            }
            Err(e) => panic!("Error in open {:?}", e),
        }
    }

    // TODO: not cool
    fn compute_nonce(&self) -> Vec<u8> {
        let seq = self.sequence_number.to_be_bytes();
        let mut enc_seq = vec![0u8; self.nonce.len() - seq.len()];
        enc_seq.append(&mut seq.to_vec());
        util::xor_bytes(&enc_seq, &self.nonce)
    }

    fn increment_seq(&mut self) {
        self.sequence_number += 1;
    }
}

pub struct Hpke {
    mode: Mode,
    kem_id: kem::Mode,
    kdf_id: kdf::Mode,
    aead_id: aead::Mode,
    kem: kem::Kem,
    kdf: kdf::Kdf,
    aead: aead::Aead,
    nk: usize,
    nn: usize,
    nh: usize,
}

impl Hpke {
    pub fn new(mode: Mode, kem_id: kem::Mode, kdf_id: kdf::Mode, aead_id: aead::Mode) -> Self {
        let kem = kem::Kem::new(kem_id);
        let kdf = kdf::Kdf::new(kdf_id);
        let aead = aead::Aead::new(aead_id);
        Self {
            mode: mode,
            kem_id: kem_id,
            kdf_id: kdf_id,
            aead_id: aead_id,
            nk: aead.get_nk(),
            nn: aead.get_nn(),
            nh: kdf.get_nh(),
            kem: kem,
            kdf: kdf,
            aead: aead,
        }
    }

    pub fn seal_base(
        mode: Mode,
        pk_r: &[u8],
        info: &[u8],
        aad: &[u8],
        ptxt: &[u8],
    ) -> (Vec<u8>, Vec<u8>) {
        let hpke = Self::new(
            mode,
            kem::Mode::DhKem25519,
            kdf::Mode::HkdfSha256,
            aead::Mode::AesGcm128,
        );
        let (enc, mut context) = hpke.setup_base_sender(pk_r, info);
        (enc, context.seal(aad, ptxt))
    }

    pub fn open_base(
        mode: Mode,
        enc: &[u8],
        sk_r: &[u8],
        info: &[u8],
        aad: &[u8],
        ct: &[u8],
    ) -> Vec<u8> {
        let hpke = Self::new(
            mode,
            kem::Mode::DhKem25519,
            kdf::Mode::HkdfSha256,
            aead::Mode::AesGcm128,
        );
        let mut context = hpke.setup_base_receiver(enc, sk_r, info);
        context.open(aad, ct)
    }

    #[inline]
    fn verify_psk_inputs(&self, psk: &[u8], psk_id: &[u8]) {
        let got_psk = !psk.is_empty();
        let got_psk_id = !psk_id.is_empty();
        if (got_psk && !got_psk_id) || (!got_psk && got_psk_id) {
            panic!("Inconsistent PSK inputs");
        }

        if got_psk && (self.mode == Mode::Base || self.mode == Mode::Auth) {
            panic!("PSK input provided when not needed");
        }
        if !got_psk && (self.mode == Mode::Psk || self.mode == Mode::AuthPsk) {
            panic!("Missing required PSK input");
        }
    }

    #[inline]
    fn get_ciphersuite(&self) -> Vec<u8> {
        util::concat(&[
            &(self.kem_id as u16).to_be_bytes(),
            &(self.kdf_id as u16).to_be_bytes(),
            &(self.aead_id as u16).to_be_bytes(),
        ])
    }

    #[inline]
    fn get_key_schedule_context(&self, info: &[u8], psk_id: &[u8]) -> Vec<u8> {
        let ciphersuite = self.get_ciphersuite();

        let psk_id_hash = self.kdf.labeled_extract(&[0], "pskID_hash", psk_id);
        let info_hash = self.kdf.labeled_extract(&[0], "info_hash", info);
        util::concat(&[&ciphersuite, &[self.mode as u8], &psk_id_hash, &info_hash])
    }

    #[inline]
    fn get_secret(&self, psk: &[u8], zz: &[u8]) -> Vec<u8> {
        let psk = if psk.is_empty() {
            vec![0; self.kdf.get_nh()]
        } else {
            psk.to_vec()
        };
        let psk_hash = self
            .kdf
            .labeled_extract(&vec![0; self.kdf.get_nh()], "psk_hash", &psk);
        self.kdf.labeled_extract(&psk_hash, "secret", zz)
    }

    fn key_schedule(&self, zz: &[u8], info: &[u8], psk: &[u8], psk_id: &[u8]) -> Context {
        self.verify_psk_inputs(psk, psk_id);
        let key_schedule_context = self.get_key_schedule_context(info, psk_id);
        let secret = self.get_secret(psk, zz);

        let key = self
            .kdf
            .labeled_expand(&secret, "key", &key_schedule_context, self.nk);
        let nonce = self
            .kdf
            .labeled_expand(&secret, "nonce", &key_schedule_context, self.nn);
        let exporter_secret =
            self.kdf
                .labeled_expand(&secret, "exp", &key_schedule_context, self.nh);

        Context {
            key: key,
            nonce: nonce,
            exporter_secret: exporter_secret,
            sequence_number: 0,
            hpke: self,
        }
    }

    pub fn setup_sender(&self, pk_r: &[u8], info: &[u8]) -> (Vec<u8>, Context) {
        match self.mode {
            Mode::Base => self.setup_base_sender(pk_r, info),
            _ => unimplemented!(),
        }
    }

    pub fn setup_receiver(&self, enc: &[u8], sk_r: &[u8], info: &[u8]) -> Context {
        match self.mode {
            Mode::Base => self.setup_base_receiver(enc, sk_r, info),
            _ => unimplemented!(),
        }
    }

    fn setup_base_sender(&self, pk_r: &[u8], info: &[u8]) -> (Vec<u8>, Context) {
        assert_eq!(self.mode, Mode::Base);
        let (zz, enc) = self.kem.encaps(pk_r);
        (enc, self.key_schedule(&zz, info, &[], &[]))
    }

    fn setup_base_receiver(&self, enc: &[u8], sk_r: &[u8], info: &[u8]) -> Context {
        assert_eq!(self.mode, Mode::Base);
        let zz = self.kem.decaps(enc, sk_r);
        self.key_schedule(&zz, info, &[], &[])
    }
}

// ==== Unit and KAT test for internal functions ====

mod test {
    #![allow(unused_imports)]
    use super::*;
    use util::*;

    #[test]
    fn test_kat_a11_unit() {
        // mode: 0
        // kemID: 32
        // kdfID: 1
        // aeadID: 1
        // info: 4f6465206f6e2061204772656369616e2055726e
        // skRm: 919f0e1b7c361d1e5a3d0086ba94edeb6d2df9f756654741731f4e84cb813bdb
        // skEm: 232ce0da9fd45b8d500781a5ee1b0a2cf64411dd08d6442400ab05a4d29733a8
        // pkRm: ac511615dee12b2e11170f1272c3972e6e2268d8fb05fc93c6b008065f61f22f
        // pkEm: ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258
        // enc: ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258
        // zz: 44807c99177b0f3761d66f422945a21317a1532ca038e976594487a6a7e58fbf
        // key_schedule_context: 002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aa
        // c7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0
        // c49f16cd56fc524af4ce
        // secret: c104521df56de97b517165011f09e0ea2a36b9af339a9de402c8b88547c8b67e
        // key: e34afc8f8f4c2906b310d8e4e4d526f0
        // nonce: 2764228860619e140920c7d7
        // exporterSecret:
        // 93c6a28ec7af55f669612d5d64fe680ae38ca88d14fb6ecba647606eee668124
        let mode = Mode::Base;
        let kem_id = kem::Mode::DhKem25519;
        let kdf_id = kdf::Mode::HkdfSha256;
        let aead_id = aead::Mode::AesGcm128;
        let info = hex_to_bytes("4f6465206f6e2061204772656369616e2055726e");

        let sk_rm =
            hex_to_bytes("919f0e1b7c361d1e5a3d0086ba94edeb6d2df9f756654741731f4e84cb813bdb");
        let pk_rm =
            hex_to_bytes("ac511615dee12b2e11170f1272c3972e6e2268d8fb05fc93c6b008065f61f22f");

        let _sk_em =
            hex_to_bytes("232ce0da9fd45b8d500781a5ee1b0a2cf64411dd08d6442400ab05a4d29733a8");
        let _pk_em =
            hex_to_bytes("ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258");
        let _enc = hex_to_bytes("ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258");

        let zz = hex_to_bytes("44807c99177b0f3761d66f422945a21317a1532ca038e976594487a6a7e58fbf");
        let key_schedule_context = hex_to_bytes("002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc524af4ce");
        let secret =
            hex_to_bytes("c104521df56de97b517165011f09e0ea2a36b9af339a9de402c8b88547c8b67e");
        let key = hex_to_bytes("e34afc8f8f4c2906b310d8e4e4d526f0");
        let nonce = hex_to_bytes("2764228860619e140920c7d7");
        let exporter_secret =
            hex_to_bytes("93c6a28ec7af55f669612d5d64fe680ae38ca88d14fb6ecba647606eee668124");

        let hpke = Hpke::new(mode, kem_id, kdf_id, aead_id);
        let mut context = hpke.key_schedule(&zz, &info, &[], &[]);

        // Check setup info
        assert_eq!(
            key_schedule_context,
            hpke.get_key_schedule_context(&info, &[])
        );
        assert_eq!(secret, hpke.get_secret(&[], &zz));
        assert_eq!(context.key, key);
        assert_eq!(context.nonce, nonce);
        assert_eq!(context.exporter_secret, exporter_secret);
        assert_eq!(context.sequence_number, 0);

        // Encryptions
        // sequence number: 0
        // plaintext: 4265617574792069732074727574682c20747275746820626561757479
        // aad: 436f756e742d30
        // nonce: 2764228860619e140920c7d7
        // ciphertext: 1811cf5d39f857f80175f96ca4d3600bfb0585e4ce119bc46396da4b3719
        // 66a358924e5a97a7b53ea255971f6b
        let ptxt = hex_to_bytes("4265617574792069732074727574682c20747275746820626561757479");
        let aad = hex_to_bytes("436f756e742d30");
        let nonce = hex_to_bytes("2764228860619e140920c7d7");
        let ctxt_expected = hex_to_bytes("1811cf5d39f857f80175f96ca4d3600bfb0585e4ce119bc46396da4b371966a358924e5a97a7b53ea255971f6b");
        assert_eq!(context.nonce, nonce);

        let ctxt = context.seal(&aad, &ptxt);
        assert_eq!(ctxt_expected, ctxt);

        // Encryptiont to public key pk_rm
        let (enc, mut sender_context) = hpke.setup_base_sender(&pk_rm, &info);
        let ctxt = sender_context.seal(&aad, &ptxt);
        let mut receiver_context = hpke.setup_base_receiver(&enc, &sk_rm, &info);
        let ptxt_out = receiver_context.open(&aad, &ctxt);
        assert_eq!(ptxt_out, ptxt);

        // Singe-shot API
        let (enc, ct) = Hpke::seal_base(mode, &pk_rm, &info, &aad, &ptxt);
        let ptxt_out = Hpke::open_base(mode, &enc, &sk_rm, &info, &aad, &ct);
        assert_eq!(ptxt_out, ptxt);

        // seqno 1, same ptxt
        let aad = hex_to_bytes("436f756e742d31");
        let ctxt_expected = hex_to_bytes("2ed9ff66c33bad2f7c0326881f05aa9616ccba13bdb126a0d2a5a3dfa6b95bd4de78a98ff64c1fb64b366074d4");
        let ctxt = context.seal(&aad, &ptxt);
        assert_eq!(ctxt_expected, ctxt);
        let ctxt = sender_context.seal(&aad, &ptxt);
        let ptxt_out = receiver_context.open(&aad, &ctxt);
        assert_eq!(ptxt_out, ptxt);

        // seqno 2, same ptxt
        let aad = hex_to_bytes("436f756e742d32");
        let ctxt_expected = hex_to_bytes("4bfc8da6f1da808be2c1c141e864fe536bd1e9c4e01376cd383370b8095438a06f372e663739b30af9355da8a3");
        let ctxt = context.seal(&aad, &ptxt);
        assert_eq!(ctxt_expected, ctxt);
        let ctxt = sender_context.seal(&aad, &ptxt);
        let ptxt_out = receiver_context.open(&aad, &ctxt);
        assert_eq!(ptxt_out, ptxt);

        // Skip one seqno
        context.sequence_number += 1;

        // seqno 4, same ptxt
        let aad = hex_to_bytes("436f756e742d34");
        let ctxt_expected = hex_to_bytes("6314e60548cfdc30552303be4cb19875e335554bce186e1b41f9d15b4b4a4af77d68c09ebf883a9cbb51f3be9d");
        let ctxt = context.seal(&aad, &ptxt);
        assert_eq!(ctxt_expected, ctxt);
        let ctxt = sender_context.seal(&aad, &ptxt);
        let ptxt_out = receiver_context.open(&aad, &ctxt);
        assert_eq!(ptxt_out, ptxt);
    }
}
