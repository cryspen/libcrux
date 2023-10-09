use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use libcrux::ecdh;

mod util;
use util::*;

fn derive(c: &mut Criterion) {
    // Comparing libcrux performance for different payload sizes and other implementations.
    let mut group = c.benchmark_group("x25519 derive");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let sk1 = randombytes(32);
                let pk1 = ecdh::secret_to_public(ecdh::Algorithm::X25519, &sk1).unwrap();
                let sk2 = randombytes(32);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = ecdh::derive(ecdh::Algorithm::X25519, &pk1, &sk2).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Ring", |b| {
        use ring::{agreement, rand::SystemRandom};

        b.iter_batched(
            || {
                let rng = SystemRandom::new();
                let sk1 =
                    agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
                let pk1 = sk1.compute_public_key().unwrap();
                let sk2 =
                    agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();

                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz: Result<Vec<u8>, ring::error::Unspecified> = agreement::agree_ephemeral(
                    sk2,
                    &agreement::UnparsedPublicKey::new(&agreement::X25519, pk1),
                    |k| Ok(k.to_vec()),
                )
                .unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("RustCrypto", |b| {
        use rand_core::OsRng;
        use x25519_dalek_ng::{EphemeralSecret, PublicKey};

        b.iter_batched(
            || {
                let sk1 = EphemeralSecret::new(OsRng);
                let pk1 = PublicKey::from(&sk1);
                let sk2 = EphemeralSecret::new(OsRng);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = sk2.diffie_hellman(&pk1);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
    group.bench_function("OpenSSL", |b| {
        use openssl::derive::Deriver;
        use openssl::pkey::{Id, PKey};

        b.iter_batched(
            || {
                let pk1 = randombytes(32);
                let pk1 = PKey::public_key_from_raw_bytes(&pk1, Id::X25519).unwrap();

                let sk2 = PKey::generate_x25519().unwrap();

                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let mut deriver = Deriver::new(&sk2).unwrap();
                deriver.set_peer(&pk1).unwrap();
                let _zz = deriver.derive_to_vec().unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

fn secret_to_public(c: &mut Criterion) {
    // Comparing libcrux performance for different payload sizes and other implementations.
    let mut group = c.benchmark_group("x25519 secret to public");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let sk = randombytes(32);
                sk
            },
            |sk| {
                let _pk = ecdh::secret_to_public(ecdh::Algorithm::X25519, &sk).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Ring", |b| {
        use ring::{agreement, rand::SystemRandom};

        b.iter_batched(
            || {
                let rng = SystemRandom::new();
                let sk =
                    agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();

                sk
            },
            |sk| {
                let _pk = sk.compute_public_key().unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("RustCrypto", |b| {
        use rand_core::OsRng;
        use x25519_dalek_ng::{EphemeralSecret, PublicKey};

        b.iter_batched(
            || {
                let sk = EphemeralSecret::new(OsRng);
                sk
            },
            |sk| {
                let _pk = PublicKey::from(&sk);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(not(windows))]
    group.bench_function("OpenSSL", |b| {
        use openssl::pkey::PKey;

        b.iter_batched(
            || {},
            |()| {
                let _pk = PKey::generate_x25519().unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, derive, secret_to_public);
criterion_main!(benches);
