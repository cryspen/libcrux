use std::{env, path::Path};

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();

    if Path::new(&format!("{manifest_dir}/../sys/lib25519/lib/lib25519.so")).exists() {
        // Only build benchmarks against lib25519 when the C library is somewhere
        // in the path.
        println!("cargo:rustc-cfg=crypto_lib25519");
    }
}
