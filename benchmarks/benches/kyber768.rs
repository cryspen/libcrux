use std::time::Duration;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use libcrux::digest;
use libcrux::drbg::Drbg;
use libcrux::kem::Algorithm;
use rand_core::OsRng;
use rand_core::RngCore;

pub fn comparisons_key_generation(c: &mut Criterion) {
    let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
    let mut rng = OsRng;
    let mut group = c.benchmark_group("Kyber768 Key Generation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux portable (external random)", |b| {
        let mut seed = [0; 64];
        rng.fill_bytes(&mut seed);
        b.iter(|| {
            let _kp = libcrux::kem::deterministic::kyber768_generate_keypair_derand(seed);
        })
    });

    group.bench_function("libcrux portable unpacked (external random)", |b| {
        b.iter(|| {
            let mut seed = [0; 64];
            rng.fill_bytes(&mut seed);
            let _tuple =
                libcrux::kem::kyber::kyber768::generate_key_pair_unpacked(seed);
        })
    });

    group.bench_function("libcrux portable (HACL-DRBG)", |b| {
        b.iter(|| {
            let (_secret_key, _public_key) =
                libcrux::kem::key_gen(Algorithm::MlKem768, &mut drbg).unwrap();
        })
    });

    group.bench_function("libcrux portable (OsRng)", |b| {
        b.iter(|| {
            let (_secret_key, _public_key) =
                libcrux::kem::key_gen(Algorithm::MlKem768, &mut rng).unwrap();
        })
    });


    group.bench_function("pqclean reference implementation", |b| {
        b.iter(|| {
            let (_public_key, _secret_key) = pqcrypto_kyber::kyber768::keypair();
        })
    });
}

pub fn comparisons_pk_validation(c: &mut Criterion) {
    let mut rng = OsRng;
    let mut group = c.benchmark_group("Kyber768 PK Validation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux portable", |b| {
        let mut seed = [0; 64];
        rng.fill_bytes(&mut seed);
        b.iter_batched(
            || libcrux::kem::deterministic::kyber768_generate_keypair_derand(seed),
            |key_pair| {
                let _valid = libcrux::kem::ml_kem768_validate_public_key(key_pair.into_parts().1);
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn comparisons_encapsulation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Kyber768 Encapsulation");
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("libcrux portable (external random)", |b| {
        let mut seed1 = [0; 64];
        OsRng.fill_bytes(&mut seed1);
        let mut seed2 = [0; 32];
        OsRng.fill_bytes(&mut seed2);
        b.iter_batched(
            || libcrux::kem::deterministic::kyber768_generate_keypair_derand(seed1),
            |keypair| {
                let (_shared_secret, _ciphertext) =
                    libcrux::kem::deterministic::kyber768_encapsulate_derand(
                        &keypair.public_key(),
                        seed2,
                    );
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux portable", |b| {
        b.iter_batched(
            || {
                let mut drbg = Drbg::new(digest::Algorithm::Sha256).unwrap();
                let (_secret_key, public_key) =
                    libcrux::kem::key_gen(Algorithm::MlKem768, &mut drbg).unwrap();

                (drbg, public_key)
            },
            |(mut rng, public_key)| {
                let (_shared_secret, _ciphertext) = public_key.encapsulate(&mut rng).unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux portable OsRng", |b| {
        b.iter_batched(
            || {
                let mut drbg = OsRng;
                let (_secret_key, public_key) =
                    libcrux::kem::key_gen(Algorithm::MlKem768, &mut drbg).unwrap();

                (drbg, public_key)
            },
            |(mut rng, public_key)| {
                let (_shared_secret, _ciphertext) = public_key.encapsulate(&mut rng).unwrap();
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
                    libcrux::kem::key_gen(Algorithm::MlKem768, &mut drbg).unwrap();
                let (_shared_secret, ciphertext) = public_key.encapsulate(&mut drbg).unwrap();
                (secret_key, ciphertext)
            },
            |(secret_key, ciphertext)| {
                let _shared_secret = ciphertext.decapsulate(&secret_key);
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("libcrux portable unpacked", |b| {
        b.iter_batched(
            || {
                let mut seed = [0; 64];
                OsRng.fill_bytes(&mut seed);
                let ((sk,pk,a,rej,pkh),_pk) =
                     libcrux::kem::kyber::kyber768::generate_key_pair_unpacked(seed);
                
                let mut rand = [0; 32];
                let mut seed2 = [0; 64];
                OsRng.fill_bytes(&mut rand);
                OsRng.fill_bytes(&mut seed2);
                let kp =
                    libcrux::kem::kyber::kyber768::generate_key_pair(seed2);
                let (ciphertext,_) = libcrux::kem::kyber::kyber768::encapsulate(&kp.public_key(),rand);
                
                ((sk,pk,a,rej,pkh),ciphertext)
            },
            |((sk,pk,a,rej,pkh),ciphertext)| {
                let _shared_secret = 
                    libcrux::kem::kyber::kyber768::decapsulate_unpacked(&sk,&pk,&a,&rej,&pkh,&ciphertext);
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
    comparisons_pk_validation(c);
    comparisons_key_generation(c);
    comparisons_encapsulation(c);
    comparisons_decapsulation(c);
}

criterion_group!(benches, comparisons);
criterion_main!(benches);
