use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs_crypto::{types::KemAlgorithm, HpkeCrypto};
use hpke_rs_rust_crypto::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(&format!("K256 Derive"), |b| {
        b.iter_batched(
            || {
                let sk = HpkeRustCrypto::kem_key_gen(
                    KemAlgorithm::DhKemK256,
                    &mut HpkeRustCrypto::prng(),
                )
                .unwrap();
                let pk = HpkeRustCrypto::kem_derive_base(KemAlgorithm::DhKemK256, &sk).unwrap();
                (sk.clone(), pk.clone())
            },
            |(sk, pk)| {
                let _ = HpkeRustCrypto::kem_derive(KemAlgorithm::DhKemK256, &pk, &sk);
            },
            BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("K256 Derive Base"), |b| {
        b.iter_batched(
            || {
                let sk = HpkeRustCrypto::kem_key_gen(
                    KemAlgorithm::DhKemK256,
                    &mut HpkeRustCrypto::prng(),
                )
                .unwrap();
                sk.clone()
            },
            |sk| {
                let _pk = HpkeRustCrypto::kem_derive_base(KemAlgorithm::DhKemK256, &sk).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark,);
criterion_main!(benches);
