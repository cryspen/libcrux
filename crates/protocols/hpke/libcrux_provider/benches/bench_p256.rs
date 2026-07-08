use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use hpke_rs_crypto::{types::KemAlgorithm, HpkeCrypto};
use hpke_rs_libcrux::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function(&format!("P256 Derive"), |b| {
        b.iter_batched(
            || {
                let (pk, sk) =
                    HpkeLibcrux::kem_key_gen(KemAlgorithm::DhKemP256, &mut HpkeLibcrux::prng())
                        .unwrap();
                (sk.clone(), pk.clone())
            },
            |(sk, pk)| {
                let _ = HpkeLibcrux::dh(KemAlgorithm::DhKemP256, &pk, &sk);
            },
            BatchSize::SmallInput,
        )
    });
    c.bench_function(&format!("P256 Derive Base"), |b| {
        b.iter_batched(
            || {
                let (_pk, sk) =
                    HpkeLibcrux::kem_key_gen(KemAlgorithm::DhKemP256, &mut HpkeLibcrux::prng())
                        .unwrap();
                sk.clone()
            },
            |sk| {
                let _pk = HpkeLibcrux::secret_to_public(KemAlgorithm::DhKemP256, &sk).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark,);
criterion_main!(benches);
