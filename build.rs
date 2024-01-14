use std::env;

fn main() {
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();

    if libcrux_platform::simd128_support() && target_arch != "x86" && !target_arch.contains("wasm")
    {
        println!("cargo:rustc-cfg=simd128");
    }
    if libcrux_platform::simd256_support() && target_arch != "x86" && !target_arch.contains("wasm")
    {
        println!("cargo:rustc-cfg=simd256");
    }
    if libcrux_platform::bmi2_adx_support() {
        println!("cargo:rustc-cfg=bmi2");
        println!("cargo:rustc-cfg=adx");
    }
    if libcrux_platform::aes_ni_support() && target_arch == "x86_64" {
        println!("cargo:rustc-cfg=aes_ni");
    }
}
