use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use libcrux_secrets::AsSecret;

pub fn fmt(x: usize) -> String {
    let base = (x as f64).log(1024f64).floor() as usize;
    let suffix = ["", "KB", "MB", "GB"];
    format!("{} {}", x >> (10 * base), suffix[base])
}

fn benchmarks(c: &mut Criterion) {
    // let mut group = c.benchmark_group("arrays");
    const PAYLOAD_SIZES: [usize; 3] = [128, 1024, 1024 * 1024 * 10];
    let payload = vec![0x13u8; 1024 * 1024 * 10];

    for &payload_size in PAYLOAD_SIZES.iter() {
        c.bench_function("as_secret", |b| {
            b.iter(|| {
                let _x = (&payload[0..payload_size]).as_secret();
            })
        });
    }
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
