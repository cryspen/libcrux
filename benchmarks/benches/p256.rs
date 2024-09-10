use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use libcrux::ecdh;

use rand_core::OsRng;

fn derive(c: &mut Criterion) {
    // Comparing libcrux performance for different payload sizes and other implementations.
    let mut group = c.benchmark_group("P256 derive");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let (_, pk1) = ecdh::key_gen(ecdh::Algorithm::P256, &mut OsRng).unwrap();
                let (sk2, _) = ecdh::key_gen(ecdh::Algorithm::P256, &mut OsRng).unwrap();
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = ecdh::derive(ecdh::Algorithm::P256, &pk1, &sk2).unwrap();
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
                    agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
                let pk1 = sk1.compute_public_key().unwrap();
                let sk2 =
                    agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();

                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz: Result<Vec<u8>, ring::error::Unspecified> = agreement::agree_ephemeral(
                    sk2,
                    &agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, pk1),
                    |k| Ok(k.to_vec()),
                )
                .unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("RustCrypto", |b| {
        use p256::{ecdh::EphemeralSecret, PublicKey};

        b.iter_batched(
            || {
                let sk1 = EphemeralSecret::random(&mut OsRng);
                let pk1 = PublicKey::from(&sk1);
                let sk2 = EphemeralSecret::random(&mut OsRng);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = sk2.diffie_hellman(&pk1);
            },
            BatchSize::SmallInput,
        )
    });
}

fn secret_to_public(c: &mut Criterion) {
    // Comparing libcrux performance for different payload sizes and other implementations.
    let mut group = c.benchmark_group("P256 secret to public");

    group.bench_function("libcrux", |b| {
        b.iter_batched(
            || {
                let (sk, _) = ecdh::key_gen(ecdh::Algorithm::P256, &mut OsRng).unwrap();
                sk
            },
            |sk| {
                let _pk = ecdh::secret_to_public(ecdh::Algorithm::P256, &sk).unwrap();
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
                    agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();

                sk
            },
            |sk| {
                let _pk = sk.compute_public_key().unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("RustCrypto", |b| {
        use p256::{ecdh::EphemeralSecret, PublicKey};

        b.iter_batched(
            || {
                let sk = EphemeralSecret::random(&mut OsRng);
                sk
            },
            |sk| {
                let _pk = PublicKey::from(&sk);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, derive, secret_to_public);
criterion_main!(benches);
