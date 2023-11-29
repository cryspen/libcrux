use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs::{prelude::*, test_util::hex_to_bytes};
use hpke_rs_crypto::{
    types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm},
    HpkeCrypto, RngCore,
};
// use hpke_rs_evercrypt::*;
use hpke_rs_rust_crypto::*;
use rand::rngs::OsRng;

const MODES: [Mode; 4] = [
    HpkeMode::Base,
    HpkeMode::Auth,
    HpkeMode::Psk,
    HpkeMode::AuthPsk,
];
const AEAD_IDS: [AeadAlgorithm; 3] = [
    AeadAlgorithm::Aes128Gcm,
    AeadAlgorithm::Aes256Gcm,
    AeadAlgorithm::ChaCha20Poly1305,
];
const KDF_IDS: [KdfAlgorithm; 3] = [
    KdfAlgorithm::HkdfSha256,
    KdfAlgorithm::HkdfSha384,
    KdfAlgorithm::HkdfSha512,
];
const KEM_IDS: [KemAlgorithm; 5] = [
    KemAlgorithm::DhKemP256,
    KemAlgorithm::DhKemP384,
    KemAlgorithm::DhKemP521,
    KemAlgorithm::DhKem25519,
    KemAlgorithm::DhKem448,
];

const AEAD_PAYLOAD: usize = 128;
const AEAD_AAD: usize = 48;

fn benchmark<Crypto: HpkeCrypto + 'static>(c: &mut Criterion) {
    for hpke_mode in MODES {
        for aead_mode in AEAD_IDS {
            if Crypto::supports_aead(aead_mode).is_err() {
                continue;
            }
            for kdf_mode in KDF_IDS {
                if Crypto::supports_kdf(kdf_mode).is_err() {
                    continue;
                }
                for kem_mode in KEM_IDS {
                    if Crypto::supports_kem(kem_mode).is_err() {
                        continue;
                    }
                    let mut hpke = Hpke::<Crypto>::new(hpke_mode, kem_mode, kdf_mode, aead_mode);
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

                    let mut group = c.benchmark_group(format!("{}", label));
                    group.bench_function("Setup Sender", |b| {
                        b.iter(|| {
                            let mut hpke =
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
                    group.bench_function("Setup Receiver", |b| {
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

                    group.bench_function(&format!("Seal {}({})", AEAD_PAYLOAD, AEAD_AAD), |b| {
                        b.iter_batched(
                            || {
                                let mut hpke =
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
                                let mut aad = vec![0u8; AEAD_AAD];
                                OsRng.fill_bytes(&mut aad);
                                let mut ptxt = vec![0u8; AEAD_PAYLOAD];
                                OsRng.fill_bytes(&mut ptxt);
                                (context, aad, ptxt)
                            },
                            |(mut context, aad, ptxt)| {
                                let _ctxt = context.seal(&aad, &ptxt).unwrap();
                            },
                            BatchSize::SmallInput,
                        )
                    });
                    group.bench_function(&format!("Open {}({})", AEAD_PAYLOAD, AEAD_AAD), |b| {
                        b.iter_batched(
                            || {
                                let mut hpke =
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
                                let mut aad = vec![0u8; AEAD_AAD];
                                OsRng.fill_bytes(&mut aad);
                                let mut ptxt = vec![0u8; AEAD_PAYLOAD];
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

                    group.bench_function(
                        &format!("Single-Shot Seal {}({})", AEAD_PAYLOAD, AEAD_AAD),
                        |b| {
                            b.iter_batched(
                                || {
                                    let hpke = Hpke::<Crypto>::new(
                                        hpke_mode, kem_mode, kdf_mode, aead_mode,
                                    );
                                    let mut aad = vec![0u8; AEAD_AAD];
                                    OsRng.fill_bytes(&mut aad);
                                    let mut ptxt = vec![0u8; AEAD_PAYLOAD];
                                    OsRng.fill_bytes(&mut ptxt);
                                    (hpke, aad, ptxt)
                                },
                                |(mut hpke, aad, ptxt)| {
                                    let _ctxt = hpke
                                        .seal(
                                            &pk_rm,
                                            &info,
                                            &aad,
                                            &ptxt,
                                            psk.as_ref().map(Vec::as_ref),
                                            psk_id.as_ref().map(Vec::as_ref),
                                            sk_sm.as_ref(),
                                        )
                                        .unwrap();
                                },
                                BatchSize::SmallInput,
                            )
                        },
                    );
                    group.bench_function(
                        &format!("Single-Shot Open {}({})", AEAD_PAYLOAD, AEAD_AAD),
                        |b| {
                            b.iter_batched(
                                || {
                                    let mut hpke = Hpke::<Crypto>::new(
                                        hpke_mode, kem_mode, kdf_mode, aead_mode,
                                    );
                                    let (enc, mut sender_context) = hpke
                                        .setup_sender(
                                            &pk_rm,
                                            &info,
                                            psk.as_ref().map(Vec::as_ref),
                                            psk_id.as_ref().map(Vec::as_ref),
                                            sk_sm.as_ref(),
                                        )
                                        .unwrap();
                                    let mut aad = vec![0u8; AEAD_AAD];
                                    OsRng.fill_bytes(&mut aad);
                                    let mut ptxt = vec![0u8; AEAD_PAYLOAD];
                                    OsRng.fill_bytes(&mut ptxt);
                                    let ctxt = sender_context.seal(&aad, &ptxt).unwrap();

                                    (hpke, aad, ctxt, enc)
                                },
                                |(hpke, aad, ctxt, enc)| {
                                    let _ctxt_out = hpke
                                        .open(
                                            &enc,
                                            &sk_rm,
                                            &info,
                                            &aad,
                                            &ctxt,
                                            psk.as_ref().map(Vec::as_ref),
                                            psk_id.as_ref().map(Vec::as_ref),
                                            pk_sm.as_ref(),
                                        )
                                        .unwrap();
                                },
                                BatchSize::SmallInput,
                            )
                        },
                    );
                }
            }
        }
    }
}

criterion_group!(
    benches,
    // benchmark::<HpkeEvercrypt>,
    benchmark::<HpkeRustCrypto>,
);
criterion_main!(benches);
