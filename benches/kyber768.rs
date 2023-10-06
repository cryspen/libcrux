use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use libcrux::digest;
use libcrux::drbg::Drbg;
use libcrux::kem::Algorithm;
use rand_core::OsRng;

pub fn comparisons_key_generation(c: &mut Criterion) {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
    let mut rng = OsRng;
    let mut group = c.benchmark_group("Kyber768 Key Generation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux portable", |b| {
        b.iter(|| {
            let (_secret_key, _public_key) =
                libcrux::kem::key_gen(Algorithm::Kyber768, &mut drbg).unwrap();
        })
    });

    group.bench_function("libcrux portable OsRng", |b| {
        b.iter(|| {
            let (_secret_key, _public_key) =
                libcrux::kem::key_gen(Algorithm::Kyber768, &mut rng).unwrap();
        })
    });

    group.bench_function("pqclean reference implementation", |b| {
        b.iter(|| {
            let (_public_key, _secret_key) = pqcrypto_kyber::kyber768::keypair();
        })
    });
}

pub fn comparisons_encapsulation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Kyber768 Encapsulation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux portable", |b| {
        b.iter_batched(
            || {
                let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
                let (_secret_key, public_key) =
                    libcrux::kem::key_gen(Algorithm::Kyber768, &mut drbg).unwrap();

                (drbg, public_key)
            },
            |(mut rng, public_key)| {
                let (_shared_secret, _ciphertext) =
                    libcrux::kem::encapsulate(&public_key, &mut rng).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux portable OsRng", |b| {
        b.iter_batched(
            || {
                let mut drbg = OsRng;
                let (_secret_key, public_key) =
                    libcrux::kem::key_gen(Algorithm::Kyber768, &mut drbg).unwrap();

                (drbg, public_key)
            },
            |(mut rng, public_key)| {
                let (_shared_secret, _ciphertext) =
                    libcrux::kem::encapsulate(&public_key, &mut rng).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("pqclean reference implementation", |b| {
        b.iter_batched(
            || {
                let (public_key, _secret_key) = pqcrypto_kyber::kyber768::keypair();

                public_key
            },
            |public_key| {
                let (_shared_secret, _ciphertext) =
                    pqcrypto_kyber::kyber768::encapsulate(&public_key);
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons_decapsulation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Kyber768 Decapsulation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux portable", |b| {
        b.iter_batched(
            || {
                let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
                let (secret_key, public_key) =
                    libcrux::kem::key_gen(Algorithm::Kyber768, &mut drbg).unwrap();
                let (_shared_secret, ciphertext) =
                    libcrux::kem::encapsulate(&public_key, &mut drbg).unwrap();
                (secret_key, ciphertext)
            },
            |(secret_key, ciphertext)| {
                let _shared_secret = libcrux::kem::decapsulate(&ciphertext, &secret_key);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("pqclean reference implementation", |b| {
        b.iter_batched(
            || {
                let (public_key, secret_key) = pqcrypto_kyber::kyber768::keypair();
                let (_shared_secret, ciphertext) =
                    pqcrypto_kyber::kyber768::encapsulate(&public_key);

                (ciphertext, secret_key)
            },
            |(ciphertext, secret_key)| {
                let _shared_secret =
                    pqcrypto_kyber::kyber768::decapsulate(&ciphertext, &secret_key);
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons(c: &mut Criterion) {
    comparisons_key_generation(c);
    comparisons_encapsulation(c);
    comparisons_decapsulation(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
