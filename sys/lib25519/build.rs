//! Build script for lib25519 FFI bindings.
//!
//! This script configures linking to the lib25519 C library and its dependencies.

use std::env;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-link-search={manifest_dir}/lib");
    println!("cargo:rustc-link-lib=cpucycles");
    println!("cargo:rustc-link-lib=randombytes");
    println!("cargo:rustc-link-lib=25519");
}
