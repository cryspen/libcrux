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

// TODO: add types and don't make it all pub

pub struct Context<'a> {
    pub key: Vec<u8>,
    pub nonce: Vec<u8>,
    pub exporter_secret: Vec<u8>,
    pub sequence_number: u32,
    pub hpke: &'a Hpke,
}

impl<'a> std::fmt::Debug for Context<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Context {{\n  key: {:?}\n  nonce: {:?}\n exporter_secret: {:?}\n seq no: {:?}\n}}",
            self.key, self.nonce, self.exporter_secret, self.sequence_number
        )
    }
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

    pub fn export(&self, exporter_context: &[u8], length: usize) -> Vec<u8> {
        self.hpke.kdf.labeled_expand(
            &self.exporter_secret,
            &self.hpke.get_ciphersuite(),
            "sec",
            exporter_context,
            length,
        )
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

    pub fn setup_sender(
        &self,
        pk_r: &[u8],
        info: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        sk_s: Option<&[u8]>,
    ) -> (Vec<u8>, Context) {
        let (zz, enc) = match self.mode {
            Mode::Base | Mode::Psk => self.kem.encaps(pk_r),
            Mode::Auth | Mode::AuthPsk => {
                let sk_s = match sk_s {
                    Some(s) => s,
                    None => panic!("Called setup_sender on Mode::Auth without sk_s"),
                };
                self.kem.auth_encaps(pk_r, sk_s)
            }
        };
        (
            enc,
            self.key_schedule(
                &zz,
                info,
                psk.unwrap_or_default(),
                psk_id.unwrap_or_default(),
            ),
        )
    }

    pub fn setup_receiver(
        &self,
        enc: &[u8],
        sk_r: &[u8],
        info: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        pk_s: Option<&[u8]>,
    ) -> Context {
        let zz = match self.mode {
            Mode::Base | Mode::Psk => self.kem.decaps(enc, sk_r),
            Mode::Auth | Mode::AuthPsk => {
                let pk_s = match pk_s {
                    Some(s) => s,
                    None => panic!("Called setup_sender on Mode::Auth without sk_s"),
                };
                self.kem.auth_decaps(enc, sk_r, pk_s)
            }
        };
        self.key_schedule(
            &zz,
            info,
            psk.unwrap_or_default(),
            psk_id.unwrap_or_default(),
        )
    }

    pub fn seal(
        &self,
        pk_r: &[u8],
        info: &[u8],
        aad: &[u8],
        ptxt: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        sk_s: Option<&[u8]>,
    ) -> (Vec<u8>, Vec<u8>) {
        let (enc, mut context) = self.setup_sender(pk_r, info, psk, psk_id, sk_s);
        (enc, context.seal(aad, ptxt))
    }

    pub fn open(
        &self,
        enc: &[u8],
        sk_r: &[u8],
        info: &[u8],
        aad: &[u8],
        ct: &[u8],
        psk: Option<&[u8]>,
        psk_id: Option<&[u8]>,
        pk_s: Option<&[u8]>,
    ) -> Vec<u8> {
        let mut context = self.setup_receiver(enc, sk_r, info, psk, psk_id, pk_s);
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
            &"HPKE".as_bytes(),
            &(self.kem_id as u16).to_be_bytes(),
            &(self.kdf_id as u16).to_be_bytes(),
            &(self.aead_id as u16).to_be_bytes(),
        ])
    }

    #[inline]
    fn get_key_schedule_context(&self, info: &[u8], psk_id: &[u8], suite_id: &[u8]) -> Vec<u8> {
        let psk_id_hash = self
            .kdf
            .labeled_extract(&[0], suite_id, "pskID_hash", psk_id);
        let info_hash = self.kdf.labeled_extract(&[0], suite_id, "info_hash", info);
        util::concat(&[&[self.mode as u8], &psk_id_hash, &info_hash])
    }

    #[inline]
    fn get_secret(&self, psk: &[u8], zz: &[u8], suite_id: &[u8]) -> Vec<u8> {
        let psk_hash = self.kdf.labeled_extract(&[], suite_id, "psk_hash", psk);
        self.kdf.labeled_extract(&psk_hash, suite_id, "secret", zz)
    }

    pub fn key_schedule(&self, zz: &[u8], info: &[u8], psk: &[u8], psk_id: &[u8]) -> Context {
        self.verify_psk_inputs(psk, psk_id);
        let suite_id = self.get_ciphersuite();
        let key_schedule_context = self.get_key_schedule_context(info, psk_id, &suite_id);
        let secret = self.get_secret(psk, zz, &suite_id);

        let key =
            self.kdf
                .labeled_expand(&secret, &suite_id, "key", &key_schedule_context, self.nk);
        let nonce =
            self.kdf
                .labeled_expand(&secret, &suite_id, "nonce", &key_schedule_context, self.nn);
        let exporter_secret =
            self.kdf
                .labeled_expand(&secret, &suite_id, "exp", &key_schedule_context, self.nh);

        Context {
            key: key,
            nonce: nonce,
            exporter_secret: exporter_secret,
            sequence_number: 0,
            hpke: self,
        }
    }
}
