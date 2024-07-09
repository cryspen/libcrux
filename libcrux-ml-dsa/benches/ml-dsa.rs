use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use rand::{rngs::OsRng, RngCore};

use libcrux_ml_dsa::ml_dsa_65;

pub fn comparisons_key_generation(c: &mut Criterion) {
    let mut rng = OsRng;
    let mut group = c.benchmark_group("ML-DSA-65 Key Generation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux portable (external random)", |b| {
        let mut randomness = [0; 32];
        rng.fill_bytes(&mut randomness);
        b.iter(|| {
            let _ = ml_dsa_65::generate_key_pair(randomness);
        })
    });

    group.bench_function("pqclean reference implementation (internal random)", |b| {
        b.iter(|| {
            let (_, _) = pqcrypto_dilithium::dilithium3::keypair();
        })
    });
}

pub fn comparisons_signing(c: &mut Criterion) {
    let mut rng = OsRng;
    let mut group = c.benchmark_group("ML-DSA-65 Signing");
    group.measurement_time(Duration::from_secs(10));

    let mut message = [0u8; 511];
    rng.fill_bytes(&mut message);

    group.bench_function("libcrux portable (external random)", |b| {
        let mut randomness = [0; 32];
        rng.fill_bytes(&mut randomness);
        let keypair = ml_dsa_65::generate_key_pair(randomness);

        rng.fill_bytes(&mut randomness);
        b.iter(|| {
            let _ = ml_dsa_65::sign(keypair.signing_key, &message, randomness);
        })
    });

    group.bench_function("pqclean reference implementation (internal random)", |b| {
        let (_, sk) = pqcrypto_dilithium::dilithium3::keypair();
        b.iter(|| {
            let _ = pqcrypto_dilithium::dilithium3::detached_sign(&message, &sk);
        })
    });
}

pub fn comparisons_verification(c: &mut Criterion) {
    let mut rng = OsRng;
    let mut group = c.benchmark_group("ML-DSA-65 Verification");
    group.measurement_time(Duration::from_secs(10));

    let mut message = [0u8; 511];
    rng.fill_bytes(&mut message);

    group.bench_function("libcrux portable", |b| {
        let mut randomness = [0; 32];
        rng.fill_bytes(&mut randomness);
        let keypair = ml_dsa_65::generate_key_pair(randomness);

        rng.fill_bytes(&mut randomness);
        let signature = ml_dsa_65::sign(keypair.signing_key, &message, randomness);
        b.iter(|| {
            let _ = ml_dsa_65::verify(keypair.verification_key, &message, signature).unwrap();
        })
    });

    group.bench_function("pqclean reference implementation", |b| {
        let (vk, sk) = pqcrypto_dilithium::dilithium3::keypair();
        let signature = pqcrypto_dilithium::dilithium3::detached_sign(&message, &sk);
        b.iter(|| {
            let _ = pqcrypto_dilithium::dilithium3::verify_detached_signature(
                &signature, &message, &vk,
            )
            .unwrap();
        })
    });
}

pub fn comparisons(c: &mut Criterion) {
    comparisons_key_generation(c);
    comparisons_signing(c);
    comparisons_verification(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
