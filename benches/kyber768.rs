use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use libcrux::digest;
use libcrux::drbg::Drbg;
use libcrux::kem::Algorithm;

pub fn comparisons_key_generation(c: &mut Criterion) {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
    let mut group = c.benchmark_group("Kyber768 Key Generation");

    group.bench_function("libcrux reference implementation", |b| {
        b.iter(|| {
            let (_secret_key, _public_key) =
                libcrux::kem::key_gen(Algorithm::Kyber768, &mut drbg).unwrap();
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

    group.bench_function("libcrux reference implementation", |b| {
        b.iter_batched(
            || {
                let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
                let (_secret_key, public_key) =
                    libcrux::kem::key_gen(Algorithm::Kyber768, &mut drbg).unwrap();

                (drbg, public_key)
            },
            |(mut rng, public_key)| {
                let (_shared_secret, _ciphertext) =
                    libcrux::kem::encapsulate(Algorithm::Kyber768, &public_key, &mut rng).unwrap();
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

    group.bench_function("libcrux specification", |b| {
        b.iter_batched(
            || {
                let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
                let (secret_key, public_key) =
                    libcrux::kem::key_gen(Algorithm::Kyber768, &mut drbg).unwrap();
                let (_shared_secret, ciphertext) =
                    libcrux::kem::encapsulate(Algorithm::Kyber768, &public_key, &mut drbg).unwrap();
                (secret_key, ciphertext)
            },
            |(secret_key, ciphertext)| {
                let _shared_secret =
                    libcrux::kem::decapsulate(Algorithm::Kyber768, &ciphertext, &secret_key);
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
