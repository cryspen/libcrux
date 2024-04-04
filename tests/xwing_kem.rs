mod test_util;

use core::panic;
use std::{fs::File, io::BufReader};

use libcrux::{
    hpke::{
        self,
        aead::AEAD,
        kdf::KDF,
        kem::{GenerateKeyPair, KEM},
        HPKECiphertext, HPKEConfig, HpkeOpen, HpkeSeal,
    },
    kem::{self, Algorithm, PublicKey},
};

#[cfg(not(target_arch = "wasm32"))]
use libcrux::drbg;
use rand::{CryptoRng, Error};
#[cfg(target_arch = "wasm32")]
use rand_core::OsRng;
use rand_core::RngCore;
use serde::{Deserialize, Serialize};

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn xwing_selftest() {
    let _ = pretty_env_logger::try_init();

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let (skr, pkr) = kem::key_gen(Algorithm::XWingKemDraft02, &mut rng).unwrap();

    let (ss, ct) = pkr.encapsulate(&mut rng).unwrap();
    let rss = ct.decapsulate(&skr).unwrap();

    assert_eq!(rss.encode(), ss.encode());
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn xwing_hpke_selftest() {
    let _ = pretty_env_logger::try_init();

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let config = HPKEConfig(
        hpke::Mode::mode_base,
        KEM::XWingDraft02,
        KDF::HKDF_SHA256,
        AEAD::ChaCha20Poly1305,
    );

    let mut randomness = vec![0u8; 32];
    rng.fill_bytes(&mut randomness);
    let (sk_r, pk_r) = GenerateKeyPair(KEM::XWingDraft02, randomness).unwrap();

    let info = b"xwing hpke selftest info";
    let aad = b"xwing hpke selftest aad";
    let ptxt = b"xwing hpke selftest plaintext";

    let mut randomness = vec![0u8; 32];
    rng.fill_bytes(&mut randomness);

    let HPKECiphertext(enc, ct) =
        HpkeSeal(config, &pk_r, info, aad, ptxt, None, None, None, randomness)
            .expect("Error in hpke seal");

    let decrypted_ptxt = HpkeOpen(
        config,
        &HPKECiphertext(enc, ct),
        &sk_r,
        info,
        aad,
        None,
        None,
        None,
    )
    .expect("Error opening hpke ciphertext");

    assert_eq!(ptxt, decrypted_ptxt.as_slice());
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
#[test]
fn xwing_test_vectors() {
    let _ = pretty_env_logger::try_init();

    #[cfg(not(target_arch = "wasm32"))]
    let mut rng = drbg::Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();
    #[cfg(target_arch = "wasm32")]
    let mut rng = OsRng;

    let (skr, pkr) = kem::key_gen(Algorithm::XWingKemDraft02, &mut rng).unwrap();

    let (ss, ct) = pkr.encapsulate(&mut rng).unwrap();
    let rss = ct.decapsulate(&skr).unwrap();

    assert_eq!(rss.encode(), ss.encode());
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
struct XWingTestVector {
    seed: String,
    sk: String,
    pk: String,
    eseed: String,
    ct: String,
    ss: String,
}

fn kat(tests: Vec<XWingTestVector>) {
    tests.iter().for_each(|test| {
        let kat_seed = test_util::hex_str_to_bytes(&test.seed);
        let kat_sk = test_util::hex_str_to_bytes(&test.sk);
        let kat_pk = test_util::hex_str_to_bytes(&test.pk);
        let kat_eseed = test_util::hex_str_to_bytes(&test.eseed);
        let kat_ct = test_util::hex_str_to_bytes(&test.ct);
        let kat_ss = test_util::hex_str_to_bytes(&test.ss);

        // Split the seeds for ML-KEM and X25519
        let (seed_m, seed_x) = kat_seed.split_at(64);
        let (eseed_m, eseed_x) = kat_eseed.split_at(32);

        // Since the kat version is not clamped, we can't compare the X25519
        // keys directly and we need to clamp the keys manually
        let mut clamped_seed_x = seed_x.to_owned();
        clamped_seed_x[0] &= 248u8;
        clamped_seed_x[31] &= 127u8;
        clamped_seed_x[31] |= 64u8;

        // We also clamp the kat sk
        let mut clamped_kat_sk = kat_sk.clone();
        clamped_kat_sk[2400 + 0] &= 248u8;
        clamped_kat_sk[2400 + 31] &= 127u8;
        clamped_kat_sk[2400 + 31] |= 64u8;

        let mut rng = DeterministicRng::new(
            seed_m.to_owned(),
            clamped_seed_x,
            eseed_m.to_owned(),
            eseed_x.to_owned(),
        );

        // Generate the key pair
        let (skr, pkr) = kem::key_gen(Algorithm::XWingKemDraft02, &mut rng).unwrap();

        // Compare the public key
        assert_eq!(kat_pk, pkr.encode());

        // Compare the private key
        assert_eq!(clamped_kat_sk, skr.encode());

        // Because of the missing clamping we use the kat version of the public
        // key for the rest of the tests
        let pkr = PublicKey::decode(Algorithm::XWingKemDraft02, &kat_pk).unwrap();

        // Encapsulate and compare the ciphertext and shared secret
        let (ss_computed, ct_computed) = pkr.encapsulate(&mut rng).unwrap();

        assert_eq!(kat_ct, ct_computed.encode());
        assert_eq!(kat_ss, ss_computed.encode());
    });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
fn xwing_test_kat() {
    let file = "tests/xwing_test_vectors.json";
    let file = match File::open(file) {
        Ok(f) => f,
        Err(_) => panic!("Couldn't open file {}.", file),
    };
    let reader = BufReader::new(file);
    let tests: Vec<XWingTestVector> = match serde_json::from_reader(reader) {
        Ok(r) => r,
        Err(e) => panic!("Error reading file.\n{:?}", e),
    };

    kat(tests);
}

enum RngStep {
    SeedM,
    SeedX,
    ESeedM,
    ESeedX,
}

struct DeterministicRng {
    seed_m: Vec<u8>,
    seed_x: Vec<u8>,
    eseed_m: Vec<u8>,
    eseed_x: Vec<u8>,
    step: RngStep,
}

impl DeterministicRng {
    fn new(mseed: Vec<u8>, xseed: Vec<u8>, eseed1: Vec<u8>, eseed2: Vec<u8>) -> Self {
        Self {
            seed_m: mseed,
            seed_x: xseed,
            eseed_m: eseed1,
            eseed_x: eseed2,
            step: RngStep::SeedM,
        }
    }

    fn fill_with_data(&mut self, dest: &mut [u8]) {
        println!("DeterministicRng::fill_with_data: length: {}", dest.len());
        match self.step {
            RngStep::SeedM => {
                dest.copy_from_slice(&self.seed_m);
                self.step = RngStep::SeedX;
            }
            RngStep::SeedX => {
                dest.copy_from_slice(&self.seed_x);
                self.step = RngStep::ESeedM;
            }
            RngStep::ESeedM => {
                dest.copy_from_slice(&self.eseed_m);
                self.step = RngStep::ESeedX;
            }
            RngStep::ESeedX => {
                dest.copy_from_slice(&self.eseed_x);
                self.step = RngStep::SeedM;
            }
        }
    }
}

impl RngCore for DeterministicRng {
    fn next_u32(&mut self) -> u32 {
        unimplemented!()
    }

    fn next_u64(&mut self) -> u64 {
        unimplemented!()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.fill_with_data(dest);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.fill_with_data(dest);
        Ok(())
    }
}

impl CryptoRng for DeterministicRng {}
