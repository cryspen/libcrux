use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use libcrux::ecdh;

mod util;
use rand::RngCore;
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

    group.bench_function("Dalek", |b| {
        use rand_core::OsRng;
        use x25519_dalek::{EphemeralSecret, PublicKey};

        b.iter_batched(
            || {
                let sk1 = EphemeralSecret::random_from_rng(OsRng);
                let pk1 = PublicKey::from(&sk1);
                let sk2 = EphemeralSecret::random_from_rng(OsRng);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = sk2.diffie_hellman(&pk1);
            },
            BatchSize::SmallInput,
        )
    }); 

    group.bench_function("Dalek Ristretto", |b| {
        use rand_core::OsRng;
        use curve25519_dalek::ristretto::RistrettoPoint;
        use curve25519_dalek::scalar::Scalar;

        b.iter_batched(
            || {
                let mut sk1_b = [0u8; 32];
                OsRng.fill_bytes(&mut sk1_b);
                let sk1 = Scalar::from_bytes_mod_order(sk1_b);
                let pk1 = RistrettoPoint::mul_base(&sk1);
                let mut sk2_b = [0u8; 32];
                OsRng.fill_bytes(&mut sk2_b);
                let sk2 = Scalar::from_bytes_mod_order(sk2_b);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = pk1 * sk2;
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

    group.bench_function("Dalek", |b| {
        use rand_core::OsRng;
        use x25519_dalek::{EphemeralSecret, PublicKey};

        b.iter_batched(
            || {
                let sk = EphemeralSecret::random_from_rng(OsRng);
                sk
            },
            |sk| {
                let _pk = PublicKey::from(&sk);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("Dalek Ristretto", |b| {
        use rand_core::OsRng;
        use curve25519_dalek::ristretto::RistrettoPoint;
        use curve25519_dalek::scalar::Scalar;


        b.iter_batched(
            || {
                let mut sk_b = [0u8; 32];
                OsRng.fill_bytes(&mut sk_b);
                let sk = Scalar::from_bytes_mod_order(sk_b);
                sk
            },
            |sk| {
                let _pk = RistrettoPoint::mul_base(&sk);
            },
            BatchSize::SmallInput,
        )
    });

    #[cfg(all(not(windows), not(target_arch = "wasm32"), not(target_arch = "x86")))]
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
