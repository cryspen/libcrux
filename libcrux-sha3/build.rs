use std::env;

fn main() {
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let disable_simd128 = match env::var("LIBCRUX_DISABLE_SIMD128") {
        Ok(s) => s == "1" || s == "y" || s == "Y",
        Err(_) => false,
    };

    let disable_simd256 = match env::var("LIBCRUX_DISABLE_SIMD256") {
        Ok(s) => s == "1" || s == "y" || s == "Y",
        Err(_) => false,
    };

    if target_arch == "aarch64" && !disable_simd128 {
        // We enable simd128 on all aarch64 builds.
        println!("cargo:rustc-cfg=feature=\"simd128\"");
    }
    if (target_arch == "x86_64" || target_arch == "x86") && !disable_simd128 {
        // Enable simd128 version on all x86 and x86_64 platforms.
        println!("cargo:rustc-cfg=feature=\"simd128\"");
    }
    if (target_arch == "x86_64" || target_arch == "x86") && !disable_simd256 {
        // We enable simd256 on all x86 and x86_64 builds.
        // Note that this doesn't mean the required CPU features are available.
        // But the compiler will support them and the runtime checks ensure that
        // it's only used when available.
        println!("cargo:rustc-cfg=feature=\"simd256\"");
    }
}
