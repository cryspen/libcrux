use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use benchmarks::util::*;
use rand::RngCore;

const PAYLOAD_SIZE: usize = 32; // bytes

fn sign(c: &mut Criterion) {
    let mut group = c.benchmark_group("ed25519/sign");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let sk: [u8; 32] = randombytes(32).try_into().unwrap();
                let mut pk = [0; 32];
                libcrux_ed25519::secret_to_public(&mut pk, &sk);

                let payload = randombytes(PAYLOAD_SIZE);

                (sk, payload)
            },
            |(sk, payload)| {
                let _signature = libcrux_ed25519::sign(&payload, &sk).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Ring", |b| {
        use ring::{rand::SystemRandom, signature::Ed25519KeyPair};

        b.iter_batched(
            || {
                let rng = SystemRandom::new();

                let document = Ed25519KeyPair::generate_pkcs8(&rng).unwrap();
                let keypair = Ed25519KeyPair::from_pkcs8(document.as_ref()).unwrap();
                let payload = randombytes(PAYLOAD_SIZE);

                (keypair, payload)
            },
            |(keypair, payload)| {
                let _signature = keypair.sign(&payload);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
    group.bench_function("OpenSSL", |b| {
        use openssl::pkey::PKey;
        use openssl::sign::Signer;

        b.iter_batched(
            || {
                let key = PKey::generate_ed25519().unwrap();
                let payload = randombytes(PAYLOAD_SIZE);
                (key, payload)
            },
            |(key, payload)| {
                let mut signer = Signer::new_without_digest(&key).unwrap();
                let _signature = signer.sign_oneshot_to_vec(&payload).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("Dalek", |b| {
        use ed25519_dalek::{Signer, SigningKey};
        use rand_core::OsRng;

        b.iter_batched(
            || {
                let mut csprng = OsRng;
                let signing_key = SigningKey::generate(&mut csprng);
                let payload = randombytes(PAYLOAD_SIZE);

                (signing_key, payload)
            },
            |(signing_key, payload)| {
                let _signature = signing_key.sign(&payload);
            },
            BatchSize::SmallInput,
        )
    });
}
fn verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("ed25519/verify");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let sk: [u8; 32] = randombytes(32).try_into().unwrap();
                let mut pk = [0; 32];
                libcrux_ed25519::secret_to_public(&mut pk, &sk);

                let payload = randombytes(PAYLOAD_SIZE);

                let signature = libcrux_ed25519::sign(&payload, &sk).unwrap();

                (pk, payload, signature)
            },
            |(pk, payload, signature)| {
                libcrux_ed25519::verify(&payload, &pk, &signature).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Ring", |b| {
        use ring::{
            rand::SystemRandom,
            signature::{Ed25519KeyPair, KeyPair, VerificationAlgorithm, ED25519},
        };
        use untrusted::Input;

        b.iter_batched(
            || {
                let rng = SystemRandom::new();

                let document = Ed25519KeyPair::generate_pkcs8(&rng).unwrap();
                let keypair = Ed25519KeyPair::from_pkcs8(document.as_ref()).unwrap();
                let payload = randombytes(PAYLOAD_SIZE);
                let signature = keypair.sign(&payload);

                let pk = keypair.public_key().as_ref().to_vec();

                (pk, payload, signature)
            },
            |(pk, payload, signature)| {
                ED25519
                    .verify(
                        Input::from(pk.as_ref()),
                        Input::from(payload.as_ref()),
                        Input::from(signature.as_ref()),
                    )
                    .unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
    group.bench_function("OpenSSL", |b| {
        use openssl::pkey::{Id, PKey};
        use openssl::sign::{Signer, Verifier};

        b.iter_batched(
            || {
                let key = PKey::generate_ed25519().unwrap();
                let pk = key.raw_public_key().unwrap();
                let pk = PKey::public_key_from_raw_bytes(&pk, Id::ED25519).unwrap();
                let payload = randombytes(PAYLOAD_SIZE);

                let mut signer = Signer::new_without_digest(&key).unwrap();
                let signature = signer.sign_oneshot_to_vec(&payload).unwrap();
                (pk, payload, signature)
            },
            |(pk, payload, signature)| {
                let mut verifier = Verifier::new_without_digest(&pk).unwrap();

                let matches = verifier.verify_oneshot(&signature, &payload).unwrap();
                assert!(matches);
            },
            BatchSize::SmallInput,
        )
    });
    group.bench_function("Dalek", |b| {
        use ed25519_dalek::{Signer, SigningKey};
        use rand_core::OsRng;

        b.iter_batched(
            || {
                let mut csprng = OsRng;
                let signing_key = SigningKey::generate(&mut csprng);
                let payload = randombytes(PAYLOAD_SIZE);
                let signature = signing_key.sign(&payload);

                (signing_key, payload, signature)
            },
            |(signing_key, payload, signature)| {
                signing_key.verify(&payload, &signature).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, sign, verify);
criterion_main!(benches);
