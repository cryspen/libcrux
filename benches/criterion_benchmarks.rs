#[macro_use]
extern crate criterion;
extern crate libjade;
extern crate rand;

use criterion::{BatchSize, Criterion};

fn randombytes(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::RngCore;

    let mut bytes = vec![0u8; n];
    OsRng.fill_bytes(&mut bytes);
    bytes
}

fn x25519(c: &mut Criterion) {
    // c.bench_function("X25519 base", |b| {
    //     b.iter_batched(
    //         || clone_into_array(&randombytes(32)),
    //         |sk| {
    //             let _pk = x25519_base(&sk);
    //         },
    //         BatchSize::SmallInput,
    //     )
    // });
    c.bench_function("X25519 DH", |b| {
        b.iter_batched(
            || {
                let sk1 = randombytes(32);
                let pk1 = libjade::x25519_base(&sk1).unwrap();
                let sk2 = randombytes(32);
                (pk1, sk2)
            },
            |(pk1, sk2)| {
                let _zz = libjade::x25519(&sk2, &pk1).unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

fn benchmarks(c: &mut Criterion) {
    x25519(c);
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
