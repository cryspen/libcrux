use libcrux_platform::{
    simd128_support,
    simd256_support,
    bmi2_adx_support,
    aes_ni_support
};

fn main() {
    if simd128_support() {
        println!("cargo:rustc-cfg=simd128");
    }
    if simd256_support() {
        println!("cargo:rustc-cfg=simd256");
    }
    if bmi2_adx_support() {
        println!("cargo:rustc-cfg=bmi2");
        println!("cargo:rustc-cfg=adx");
    }
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    if aes_ni_support() {
        println!("cargo:rustc-cfg=aes_ni");
    }
}
