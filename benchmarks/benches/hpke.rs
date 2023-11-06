use std::num::ParseIntError;
use std::time::{Duration, Instant};

use libcrux::hpke::aead::*;
use libcrux::hpke::kdf::KDF;
use libcrux::hpke::kem::{GenerateKeyPair, KEM};
use libcrux::{aes_ni_support, hpke::*};
use rand::{rngs::OsRng, RngCore};

pub(crate) fn hex_str_to_bytes(val: &str) -> Vec<u8> {
    let b: Result<Vec<u8>, ParseIntError> = (0..val.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&val[i..i + 2], 16))
        .collect();
    b.expect("Error parsing hex string")
}

fn duration(d: Duration) -> f64 {
    ((d.as_secs() as f64) + (d.subsec_nanos() as f64 * 1e-9)) * 1000000f64
}

pub trait ProviderName {
    fn name() -> &'static str;
}

const MODES: [Mode; 4] = [
    Mode::mode_base,
    Mode::mode_auth,
    Mode::mode_psk,
    Mode::mode_auth_psk,
];
const AEAD_IDS: [AEAD; 2] = [AEAD::AES_128_GCM, AEAD::ChaCha20Poly1305];
const KDF_IDS: [KDF; 1] = [KDF::HKDF_SHA256];
const KEM_IDS: [KEM; 2] = [KEM::DHKEM_P256_HKDF_SHA256, KEM::DHKEM_X25519_HKDF_SHA256];

const AEAD_PAYLOAD: usize = 64;
const AEAD_AAD: usize = 64;

const ITERATIONS: usize = 1_000;

fn benchmark() {
    for hpke_mode in MODES {
        for aead_mode in AEAD_IDS {
            if aead_mode == AEAD::AES_128_GCM
                && (cfg!(not(target_arch = "x86_64")) || !aes_ni_support())
            {
                // AES is not supported on all platforms yet.
                continue;
            }
            for kdf_mode in KDF_IDS {
                for kem_mode in KEM_IDS {
                    let label = format!(
                        "{:?} {:?} {:?} {:?}",
                        hpke_mode, kem_mode, kdf_mode, aead_mode
                    );
                    println!("{}", label);

                    let mut randomness = [0u8; 32];
                    OsRng.fill_bytes(&mut randomness);
                    let (_sk, enc) = GenerateKeyPair(kem_mode, randomness.to_vec()).unwrap();
                    let mut randomness = [0u8; 32];
                    OsRng.fill_bytes(&mut randomness);
                    let (sk_rm, pk_rm) = GenerateKeyPair(kem_mode, randomness.to_vec()).unwrap();
                    let info = hex_str_to_bytes("4f6465206f6e2061204772656369616e2055726e");
                    let psk = if hpke_mode == Mode::mode_auth_psk || hpke_mode == Mode::mode_psk {
                        Some(hex_str_to_bytes("0247fd33b913760fa1fa51e1892d9f30"))
                    } else {
                        None
                    };
                    let psk_id = if hpke_mode == Mode::mode_auth_psk || hpke_mode == Mode::mode_psk
                    {
                        Some(hex_str_to_bytes("456e6e796e204475"))
                    } else {
                        None
                    };
                    let (pk_sm, sk_sm) =
                        if hpke_mode == Mode::mode_auth_psk || hpke_mode == Mode::mode_auth {
                            let mut randomness = [0u8; 32];
                            OsRng.fill_bytes(&mut randomness);
                            let (sk, pk) = GenerateKeyPair(kem_mode, randomness.to_vec()).unwrap();
                            (Some(pk), Some(sk))
                        } else {
                            (None, None)
                        };

                    let config = HPKEConfig(hpke_mode, kem_mode, kdf_mode, aead_mode);

                    let mut randomness = [0u8; 32];
                    OsRng.fill_bytes(&mut randomness);
                    let randomness = randomness.to_vec();
                    let start = Instant::now();
                    for _ in 0..ITERATIONS {
                        let _sender = match hpke_mode {
                            Mode::mode_base => {
                                SetupBaseS(config, &pk_rm, &info, randomness.clone())
                            }
                            Mode::mode_psk => SetupPSKS(
                                config,
                                &pk_rm,
                                &info,
                                &psk.clone().unwrap(),
                                &psk_id.clone().unwrap(),
                                randomness.clone(),
                            ),
                            Mode::mode_auth => SetupAuthS(
                                config,
                                &pk_rm,
                                &info,
                                &sk_sm.clone().unwrap(),
                                randomness.clone(),
                            ),
                            Mode::mode_auth_psk => SetupAuthPSKS(
                                config,
                                &pk_rm,
                                &info,
                                &psk.clone().unwrap(),
                                &psk_id.clone().unwrap(),
                                &sk_sm.clone().unwrap(),
                                randomness.clone(),
                            ),
                        }
                        .unwrap();
                    }
                    let end = Instant::now();
                    let time = duration(end.duration_since(start));
                    println!("\tSetup Sender: {}μs", time / (ITERATIONS as f64));

                    let start = Instant::now();
                    for _ in 0..ITERATIONS {
                        let _receiver = match hpke_mode {
                            Mode::mode_base => SetupBaseR(config, &enc, &sk_rm, &info),
                            Mode::mode_psk => SetupPSKR(
                                config,
                                &enc,
                                &sk_rm,
                                &info,
                                &psk.clone().unwrap(),
                                &psk_id.clone().unwrap(),
                            ),
                            Mode::mode_auth => {
                                SetupAuthR(config, &enc, &sk_rm, &info, &pk_sm.clone().unwrap())
                            }
                            Mode::mode_auth_psk => SetupAuthPSKR(
                                config,
                                &enc,
                                &sk_rm,
                                &info,
                                &psk.clone().unwrap(),
                                &psk_id.clone().unwrap(),
                                &pk_sm.clone().unwrap(),
                            ),
                        }
                        .unwrap();
                    }
                    let end = Instant::now();
                    let time = duration(end.duration_since(start));
                    println!("\tSetup Receiver: {}μs", time / (ITERATIONS as f64));

                    let (enc, mut context) = match hpke_mode {
                        Mode::mode_base => SetupBaseS(config, &pk_rm, &info, randomness.clone()),
                        Mode::mode_psk => SetupPSKS(
                            config,
                            &pk_rm,
                            &info,
                            &psk.clone().unwrap(),
                            &psk_id.clone().unwrap(),
                            randomness.clone(),
                        ),
                        Mode::mode_auth => SetupAuthS(
                            config,
                            &pk_rm,
                            &info,
                            &sk_sm.clone().unwrap(),
                            randomness.clone(),
                        ),
                        Mode::mode_auth_psk => SetupAuthPSKS(
                            config,
                            &pk_rm,
                            &info,
                            &psk.clone().unwrap(),
                            &psk_id.clone().unwrap(),
                            &sk_sm.clone().unwrap(),
                            randomness.clone(),
                        ),
                    }
                    .unwrap();

                    let mut aad = vec![0u8; AEAD_AAD];
                    OsRng.fill_bytes(&mut aad);
                    let aad = aad.to_vec();
                    let mut ptxt = vec![0u8; AEAD_PAYLOAD];
                    OsRng.fill_bytes(&mut ptxt);
                    let ptxt = ptxt.to_vec();

                    let mut ctxts = Vec::with_capacity((AEAD_PAYLOAD + 16) * ITERATIONS);
                    let start = Instant::now();
                    for _ in 0..ITERATIONS {
                        let (ctxt, new_context) =
                            ContextS_Seal(aead_mode, context, &aad, &ptxt).unwrap();
                        ctxts.push(ctxt);
                        context = new_context;
                    }
                    let end = Instant::now();
                    let time = duration(end.duration_since(start));
                    println!(
                        "\tSeal {}({}): {}μs",
                        AEAD_PAYLOAD,
                        AEAD_AAD,
                        time / (ITERATIONS as f64)
                    );

                    let mut receiver_context = match hpke_mode {
                        Mode::mode_base => SetupBaseR(config, &enc, &sk_rm, &info),
                        Mode::mode_psk => SetupPSKR(
                            config,
                            &enc,
                            &sk_rm,
                            &info,
                            &psk.clone().unwrap(),
                            &psk_id.clone().unwrap(),
                        ),
                        Mode::mode_auth => {
                            SetupAuthR(config, &enc, &sk_rm, &info, &pk_sm.clone().unwrap())
                        }
                        Mode::mode_auth_psk => SetupAuthPSKR(
                            config,
                            &enc,
                            &sk_rm,
                            &info,
                            &psk.clone().unwrap(),
                            &psk_id.clone().unwrap(),
                            &pk_sm.clone().unwrap(),
                        ),
                    }
                    .unwrap();

                    let mut ptxts = Vec::with_capacity((AEAD_PAYLOAD + 16) * ITERATIONS);
                    let start = Instant::now();
                    for ctxt in ctxts.iter() {
                        let (ptxt_out, new_context) =
                            ContextR_Open(aead_mode, receiver_context, &aad, ctxt).unwrap();
                        receiver_context = new_context;
                        ptxts.push(ptxt_out);
                    }
                    let end = Instant::now();
                    let time = duration(end.duration_since(start));
                    println!(
                        "\tOpen {}({}): {}μs",
                        AEAD_PAYLOAD,
                        AEAD_AAD,
                        time / (ITERATIONS as f64)
                    );
                    assert_eq!(ptxts[0], ptxt);

                    let mut aad = vec![0u8; AEAD_AAD];
                    OsRng.fill_bytes(&mut aad);
                    let aad = aad.to_vec();
                    let mut ptxt = vec![0u8; AEAD_PAYLOAD];
                    OsRng.fill_bytes(&mut ptxt);
                    let ptxt = ptxt.to_vec();
                    let mut randomness = [0u8; 32];
                    OsRng.fill_bytes(&mut randomness);
                    let randomness = randomness.to_vec();

                    let mut ctxt = HPKECiphertext(vec![], vec![]);
                    let start = Instant::now();
                    for _ in 0..ITERATIONS {
                        ctxt = HpkeSeal(
                            config,
                            &pk_rm,
                            &info,
                            &aad,
                            &ptxt,
                            psk.as_ref().map(|v| v.as_slice()),
                            psk_id.as_ref().map(|v| v.as_slice()),
                            sk_sm.as_ref().map(|v| v.as_slice()),
                            randomness.clone(),
                        )
                        .unwrap();
                    }
                    let end = Instant::now();
                    let time = duration(end.duration_since(start));
                    println!(
                        "\tSingle-Shot Seal {}({}): {}μs",
                        AEAD_PAYLOAD,
                        AEAD_AAD,
                        time / (ITERATIONS as f64)
                    );

                    let mut ptxt_out = vec![];
                    let start = Instant::now();
                    for _ in 0..ITERATIONS {
                        ptxt_out = HpkeOpen(
                            config,
                            &ctxt,
                            &sk_rm,
                            &info,
                            &aad,
                            psk.as_ref().map(|v| v.as_slice()),
                            psk_id.as_ref().map(|v| v.as_slice()),
                            pk_sm.as_ref().map(|v| v.as_slice()),
                        )
                        .unwrap();
                    }
                    let end = Instant::now();
                    let time = duration(end.duration_since(start));
                    println!(
                        "\tSingle-Shot Open {}({}): {}μs",
                        AEAD_PAYLOAD,
                        AEAD_AAD,
                        time / (ITERATIONS as f64)
                    );
                    assert_eq!(ptxt_out, ptxt);
                }
            }
        }
    }
}

fn main() {
    benchmark();
}
