use criterion::{black_box, criterion_group, criterion_main, Criterion};

use pprof::criterion::{Output, PProfProfiler};

pub fn curve_bench(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let mut group = c.benchmark_group("Curve 25519");

    let (sk_a, _pk_a) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
    let (_sk_b, pk_b) = libcrux_ecdh::x25519_key_gen(&mut rng).unwrap();
    group.bench_function("ECDH", |b| {
        b.iter(|| libcrux_ecdh::hacl::curve25519::ecdh(black_box(&sk_a), black_box(&pk_b)))
    });
    group.bench_function("Secret to Public", |b| {
        b.iter(|| libcrux_ecdh::hacl::curve25519::secret_to_public(black_box(&sk_a)))
    });
}


criterion_group!{name = benches;
                 config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
                 targets = curve_bench}

criterion_main!(benches);
