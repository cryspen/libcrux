fn main() {
    if pkg_config::probe_library("25519").is_ok() {
        // Only build benchmarks against lib25519 when the C library is somewhere
        // in the path.
        println!("cargo:rustc-cfg=lib25519");
    }
}
