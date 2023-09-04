fn main() {
    if libcrux_platform::simd128_support() {
        println!("cargo:rustc-cfg=simd128");
    }
    if libcrux_platform::simd256_support() {
        println!("cargo:rustc-cfg=simd256");
    }
    if libcrux_platform::bmi2_adx_support() {
        println!("cargo:rustc-cfg=bmi2");
        println!("cargo:rustc-cfg=adx");
    }
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    if libcrux_platform::aes_ni_support() {
        println!("cargo:rustc-cfg=aes_ni");
    }
}
