use std::env;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-link-search={manifest_dir}/lib");
    println!("cargo:rustc-link-lib=cpucycles");
    println!("cargo:rustc-link-lib=randombytes");
    println!("cargo:rustc-link-lib=25519");
}
