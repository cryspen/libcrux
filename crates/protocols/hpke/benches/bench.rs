use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs::{prelude::*, test_util::hex_to_bytes};
use hpke_rs_crypto::{types::*, HpkeCrypto, RngCore};
use hpke_rs_evercrypt::*;
use hpke_rs_rust_crypto::*;
use rand::rngs::OsRng;

pub trait ProviderName {
    fn name() -> &'static str;
}

impl ProviderName for HpkeRustCrypto {
    fn name() -> &'static str {
        "RustCrypto"
    }
}

impl ProviderName for HpkeEvercrypt {
    fn name() -> &'static str {
        "Evercrypt"
    }
}

fn criterion_benchmark<Crypto: HpkeCrypto + ProviderName + 'static>(c: &mut Criterion) {
    for mode in 0u8..4 {
        let hpke_mode = HpkeMode::try_from(mode).unwrap();
        for aead_mode in 3u16..4 {
            let aead_mode = AeadAlgorithm::try_from(aead_mode).unwrap();
            for kdf_mode in 1u16..4 {
                let kdf_mode = KdfAlgorithm::try_from(kdf_mode).unwrap();
                for &kem_mode in &[0x10u16, 0x20] {
                    let kem_mode = KemAlgorithm::try_from(kem_mode).unwrap();
                    let hpke = Hpke::<Crypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode);
                    let label = format!("{} {}", Crypto::name(), hpke);
                    let kp = hpke.generate_key_pair().unwrap();
                    let enc = kp.public_key().as_slice();
                    let kp_r = hpke.generate_key_pair().unwrap();
                    let sk_rm = kp_r.private_key();
                    let pk_rm = kp_r.public_key();
                    let info = hex_to_bytes("4f6465206f6e2061204772656369616e2055726e");
                    let psk = if hpke_mode == HpkeMode::AuthPsk || hpke_mode == HpkeMode::Psk {
                        Some(hex_to_bytes(
                            "0247fd33b913760fa1fa51e1892d9f307fbe65eb171e8132c2af18555a738b82",
                        ))
                    } else {
                        None
                    };
                    let psk_id = if hpke_mode == HpkeMode::AuthPsk || hpke_mode == HpkeMode::Psk {
                        Some(hex_to_bytes("456e6e796e20447572696e206172616e204d6f726961"))
                    } else {
                        None
                    };
                    let (pk_sm, sk_sm) =
                        if hpke_mode == HpkeMode::AuthPsk || hpke_mode == HpkeMode::Auth {
                            let kp = hpke.generate_key_pair().unwrap();
                            (
                                Some(kp.public_key().clone()),
                                Some(kp.private_key().clone()),
                            )
                        } else {
                            (None, None)
                        };
                    c.bench_function(&format!("Setup Receiver {}", label), |b| {
                        b.iter(|| {
                            let hpke =
                                Hpke::<Crypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode);
                            hpke.setup_receiver(
                                enc,
                                &sk_rm,
                                &info,
                                psk.as_ref().map(Vec::as_ref),
                                psk_id.as_ref().map(Vec::as_ref),
                                pk_sm.as_ref(),
                            )
                            .unwrap();
                        })
                    });
                    c.bench_function(&format!("Setup Sender {}", label), |b| {
                        b.iter(|| {
                            let hpke =
                                Hpke::<Crypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode);
                            hpke.setup_sender(
                                &pk_rm,
                                &info,
                                psk.as_ref().map(Vec::as_ref),
                                psk_id.as_ref().map(Vec::as_ref),
                                sk_sm.as_ref(),
                            )
                            .unwrap();
                        })
                    });
                    c.bench_function(&format!("Seal {}", label), |b| {
                        b.iter_batched(
                            || {
                                let hpke =
                                    Hpke::<Crypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode);
                                let (_enc, context) = hpke
                                    .setup_sender(
                                        &pk_rm,
                                        &info,
                                        psk.as_ref().map(Vec::as_ref),
                                        psk_id.as_ref().map(Vec::as_ref),
                                        sk_sm.as_ref(),
                                    )
                                    .unwrap();
                                let mut aad = vec![0u8; 44];
                                OsRng.fill_bytes(&mut aad);
                                let mut ptxt = vec![0u8; 199];
                                OsRng.fill_bytes(&mut ptxt);
                                (context, aad, ptxt)
                            },
                            |(mut context, aad, ptxt)| {
                                let _ctxt = context.seal(&aad, &ptxt).unwrap();
                            },
                            BatchSize::SmallInput,
                        )
                    });
                    c.bench_function(&format!("Open {}", label), |b| {
                        b.iter_batched(
                            || {
                                let hpke =
                                    Hpke::<Crypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode);
                                let (enc, mut sender_context) = hpke
                                    .setup_sender(
                                        &pk_rm,
                                        &info,
                                        psk.as_ref().map(Vec::as_ref),
                                        psk_id.as_ref().map(Vec::as_ref),
                                        sk_sm.as_ref(),
                                    )
                                    .unwrap();
                                let mut aad = vec![0u8; 44];
                                OsRng.fill_bytes(&mut aad);
                                let mut ptxt = vec![0u8; 199];
                                OsRng.fill_bytes(&mut ptxt);
                                let ctxt = sender_context.seal(&aad, &ptxt).unwrap();

                                let context = hpke
                                    .setup_receiver(
                                        &enc,
                                        &sk_rm,
                                        &info,
                                        psk.as_ref().map(Vec::as_ref),
                                        psk_id.as_ref().map(Vec::as_ref),
                                        pk_sm.as_ref(),
                                    )
                                    .unwrap();
                                (context, aad, ctxt)
                            },
                            |(mut context, aad, ctxt)| {
                                let _ctxt_out = context.open(&aad, &ctxt).unwrap();
                            },
                            BatchSize::SmallInput,
                        )
                    });
                    break;
                }
                break;
            }
            break;
        }
        break;
    }
}

criterion_group!(
    benches,
    criterion_benchmark::<HpkeEvercrypt>,
    criterion_benchmark::<HpkeRustCrypto>,
);
criterion_main!(benches);
