use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs_crypto::{types::KemAlgorithm, HpkeCrypto};
use hpke_rs_evercrypt::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(&format!("P256 Derive"), |b| {
        b.iter_batched(
            || {
                let sk = HpkeEvercrypt::kem_key_gen(
                    KemAlgorithm::DhKemP256,
                    &mut HpkeEvercrypt::prng(),
                )
                .unwrap();
                let pk = HpkeEvercrypt::kem_derive_base(KemAlgorithm::DhKemP256, &sk).unwrap();
                (sk.clone(), pk.clone())
            },
            |(sk, pk)| {
                let _ = HpkeEvercrypt::kem_derive(KemAlgorithm::DhKemP256, &pk, &sk);
            },
            BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("P256 Derive Base"), |b| {
        b.iter_batched(
            || {
                let sk = HpkeEvercrypt::kem_key_gen(
                    KemAlgorithm::DhKemP256,
                    &mut HpkeEvercrypt::prng(),
                )
                .unwrap();
                sk.clone()
            },
            |sk| {
                let _pk = HpkeEvercrypt::kem_derive_base(KemAlgorithm::DhKemP256, &sk).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark,);
criterion_main!(benches);
