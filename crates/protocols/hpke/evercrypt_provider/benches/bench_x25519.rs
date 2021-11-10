use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs_crypto::{types::*, HpkeCrypto};
use hpke_rs_evercrypt::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(&format!("x25519 Derive"), |b| {
        b.iter_batched(
            || {
                let sk = HpkeEvercrypt::kem_key_gen(
                    KemAlgorithm::DhKem25519,
                    &mut HpkeEvercrypt::prng(),
                )
                .unwrap();
                let pk = HpkeEvercrypt::kem_derive_base(KemAlgorithm::DhKem25519, &sk).unwrap();
                (sk.clone(), pk.clone())
            },
            |(sk, pk)| {
                let _ = HpkeEvercrypt::kem_derive(KemAlgorithm::DhKem25519, &pk, &sk);
            },
            BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("x25519 Derive Base"), |b| {
        b.iter_batched(
            || {
                let sk = HpkeEvercrypt::kem_key_gen(
                    KemAlgorithm::DhKem25519,
                    &mut HpkeEvercrypt::prng(),
                )
                .unwrap();
                sk.clone()
            },
            |sk| {
                let _pk = HpkeEvercrypt::kem_derive_base(KemAlgorithm::DhKem25519, &sk).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark,);
criterion_main!(benches);
