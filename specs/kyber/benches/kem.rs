use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use pqcrypto_kyber::kyber768;

use rand;

pub fn randombytes<const N: usize>() -> [u8; N] {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = [0u8; N];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

pub fn comparisons_key_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Kyber768 Key Generation");

    group.bench_function("libcrux specification", |b| {
        b.iter_batched(
            || {
                let seed = randombytes::<{ hacspec_kyber::KYBER768_KEY_GENERATION_SEED_SIZE }>();
                seed
            },
            |seed| {
                let _key_pair = hacspec_kyber::generate_keypair(seed).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("pqclean reference implementation", |b| {
        b.iter(|| {
            let (_public_key, _secret_key) = kyber768::keypair();
        })
    });
}

pub fn comparisons_encapsulation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Kyber768 Encapsulation");

    group.bench_function("libcrux specification", |b| {
        b.iter_batched(
            || {
                let keygen_seed =
                    randombytes::<{ hacspec_kyber::KYBER768_KEY_GENERATION_SEED_SIZE }>();
                let key_pair = hacspec_kyber::generate_keypair(keygen_seed).unwrap();

                let encaps_seed = randombytes::<{ hacspec_kyber::KYBER768_SHARED_SECRET_SIZE }>();

                (key_pair.pk().clone(), encaps_seed)
            },
            |(public_key, encaps_seed)| {
                let (_ciphertext, _shared_secret) =
                    hacspec_kyber::encapsulate(public_key, encaps_seed).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("pqclean reference implementation", |b| {
        b.iter_batched(
            || {
                let (public_key, _secret_key) = kyber768::keypair();

                public_key
            },
            |public_key| {
                let (_shared_secret, _ciphertext) = kyber768::encapsulate(&public_key);
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
                let keygen_seed =
                    randombytes::<{ hacspec_kyber::KYBER768_KEY_GENERATION_SEED_SIZE }>();
                let key_pair = hacspec_kyber::generate_keypair(keygen_seed).unwrap();

                let encaps_seed = randombytes::<{ hacspec_kyber::KYBER768_SHARED_SECRET_SIZE }>();
                let (ciphertext, _shared_secret) =
                    hacspec_kyber::encapsulate(key_pair.pk().clone(), encaps_seed).unwrap();

                (key_pair.sk().clone(), ciphertext)
            },
            |(secret_key, ciphertext)| {
                let _shared_secret = hacspec_kyber::decapsulate(ciphertext, secret_key);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("pqclean reference implementation", |b| {
        b.iter_batched(
            || {
                let (public_key, secret_key) = kyber768::keypair();
                let (_shared_secret, ciphertext) = kyber768::encapsulate(&public_key);

                (ciphertext, secret_key)
            },
            |(ciphertext, secret_key)| {
                let _shared_secret = kyber768::decapsulate(&ciphertext, &secret_key);
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
