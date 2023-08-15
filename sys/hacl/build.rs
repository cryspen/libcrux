#[cfg(not(windows))]
extern crate bindgen;

use std::{env, path::Path};

macro_rules! svec {
    ($($x:expr),*$(,)?) => (vec![$($x.to_string()),*]);
}

fn includes(home_dir: &Path, include_str: &str) -> Vec<String> {
    let c_path = home_dir.join("c");
    vec![
        format!("{}{}", include_str, c_path.join("include").display()),
        format!(
            "{}{}",
            include_str,
            c_path.join("karamel").join("include").display()
        ),
        format!(
            "{}{}",
            include_str,
            c_path
                .join("karamel")
                .join("krmllib")
                .join("dist")
                .join("minimal")
                .display()
        ),
    ]
}

fn append_simd128_flags(flags: &mut Vec<String>) {
    if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
        flags.push("-msse4.1".to_string());
        flags.push("-msse4.2".to_string());
        flags.push("-mavx".to_string());
    }
}

fn append_simd256_flags(flags: &mut Vec<String>) {
    flags.push("-mavx2".to_string());
}

#[cfg(not(windows))]
fn create_bindings(platform: Platform, home_dir: &Path) {
    let mut clang_args = includes(home_dir, "-I");

    let mut bindings = bindgen::Builder::default();
    bindings = bindings
        // Header to wrap HACL headers
        .header("c/include/hacl.h");

    if platform.simd128 {
        append_simd128_flags(&mut clang_args);
        bindings = bindings
            // Header to wrap HACL SIMD 128 headers
            .header("c/include/hacl128.h");
    }
    if platform.simd256 {
        append_simd256_flags(&mut clang_args);
        bindings = bindings
            // Header to wrap HACL SIMD 256 headers
            .header("c/include/hacl256.h");
    }

    let generated_bindings = bindings
        // Set include paths for HACL headers
        .clang_args(clang_args)
        // Allow function we want to have in
        .allowlist_function("Hacl_Chacha20Poly1305.*")
        .allowlist_function("Hacl_Curve25519.*")
        .allowlist_function("Hacl_Hash_SHA2.*")
        .allowlist_function("Hacl_Streaming_SHA2.*")
        .allowlist_function("Hacl_SHA3.*")
        .allowlist_function("Hacl_Hash_SHA3.*")
        .allowlist_function("Hacl_Blake2.*")
        .allowlist_function("Hacl_Streaming_Keccak.*")
        .allowlist_type("Spec_.*")
        .allowlist_type("Hacl_Streaming_SHA2.*")
        // Block everything we don't need or define ourselves.
        .blocklist_type("__.*")
        // XXX: These functions use uint128 in the API, which is not FFI safe
        .blocklist_function("Hacl_Blake2b_32_blake2b_update_multi")
        .blocklist_function("Hacl_Blake2b_32_blake2b_update_last")
        // Disable tests to avoid warnings and keep it portable
        .layout_tests(false)
        // Generate bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .use_core()
        .generate()
        .expect("Unable to generate bindings");

    let home_bindings = home_dir.join("src/bindings.rs");
    generated_bindings
        .write_to_file(home_bindings)
        .expect("Couldn't write bindings!");
}

#[cfg(windows)]
fn create_bindings(_: &Path, _: &Path) {}

fn copy_files(home_path: &Path, out_path: &Path) {
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    fs_extra::dir::copy(home_path.join("c"), out_path, &options).unwrap();
}

fn compile_files(
    library_name: &str,
    files: &[String],
    out_path: &Path,
    args: &[String],
    defines: &[(&str, &str)],
) {
    let src_prefix = out_path.join("c").join("src");

    let mut build = cc::Build::new();
    build
        .files(files.iter().map(|fname| src_prefix.join(fname)))
        // XXX: There are too many warnings for now
        // .warnings_into_errors(true)
        .warnings(true)
        .extra_warnings(true);
    // .no_default_flags(true);

    for include in includes(out_path, "") {
        build.include(include);
    }
    build.flag("-O3").flag("-c");
    for arg in args {
        build.flag(arg);
    }
    for define in defines {
        build.define(define.0, define.1);
    }

    build.compile(library_name);
}

fn build(platform: Platform, out_path: &Path) {
    let files = svec![
        "Hacl_NaCl.c",
        "Hacl_Salsa20.c",
        "Hacl_Poly1305_32.c",
        "Hacl_Curve25519_51.c",
        // "Hacl_Gf128_CT64.c",
        // "Hacl_AES_128_CTR32_BitSlice.c",
        // "Hacl_AES_128_GCM_CT64.c",
        // "Hacl_AES_256_CTR32_BitSlice.c",
        // "Hacl_AES_256_GCM_CT64.c",
        "Hacl_HMAC_DRBG.c",
        "Hacl_HMAC.c",
        "Hacl_Hash_SHA2.c",
        "Hacl_Hash_Blake2.c",
        "Lib_Memzero0.c",
        "Hacl_Ed25519.c",
        "Hacl_EC_Ed25519.c",
        "Hacl_Hash_Base.c",
        "Hacl_Streaming_Blake2.c",
        "Hacl_Bignum256_32.c",
        "Hacl_Bignum.c",
        "Hacl_Bignum256.c",
        "Hacl_Bignum32.c",
        "Hacl_Bignum4096_32.c",
        "Hacl_GenericField32.c",
        "Hacl_Chacha20Poly1305_32.c",
        "Hacl_Chacha20.c",
        "Hacl_Streaming_Poly1305_32.c",
        "Hacl_Chacha20_Vec32.c",
        "Hacl_P256.c",
        "Hacl_K256_ECDSA.c",
        "Hacl_EC_K256.c",
        "Hacl_FFDHE.c",
        "Hacl_Hash_SHA3.c",
        "Hacl_Hash_SHA1.c",
        "Hacl_Hash_MD5.c",
        "Hacl_HKDF.c",
        "Hacl_RSAPSS.c",
    ];
    let mut defines = vec![];

    // Platform detection
    if platform.simd128 {
        let files128 = svec![
            "Hacl_Hash_Blake2s_128.c",
            "Hacl_Streaming_Blake2s_128.c",
            "Hacl_Bignum4096.c",
            "Hacl_Bignum64.c",
            "Hacl_GenericField64.c",
            "Hacl_Chacha20Poly1305_128.c",
            "Hacl_Poly1305_128.c",
            "Hacl_Chacha20_Vec128.c",
            "Hacl_Streaming_Poly1305_128.c",
            "Hacl_SHA2_Vec128.c",
            "Hacl_HKDF_Blake2s_128.c",
            "Hacl_HMAC_Blake2s_128.c",
        ];
        defines.append(&mut vec![("HACL_CAN_COMPILE_VEC128", "1")]);

        let mut simd128_flags = vec![];
        append_simd128_flags(&mut simd128_flags);
        compile_files(
            "libhacl_128.a",
            &files128,
            out_path,
            &simd128_flags,
            &defines,
        );
    }
    if platform.simd256 {
        let files256 = svec![
            "Hacl_Hash_Blake2b_256.c",
            "Hacl_Streaming_Blake2b_256.c",
            "Hacl_Chacha20Poly1305_256.c",
            "Hacl_Poly1305_256.c",
            "Hacl_Chacha20_Vec256.c",
            "Hacl_Streaming_Poly1305_256.c",
            "Hacl_SHA2_Vec256.c",
            "Hacl_HKDF_Blake2b_256.c",
            "Hacl_HMAC_Blake2b_256.c",
        ];
        defines.append(&mut vec![("HACL_CAN_COMPILE_VEC256", "1")]);

        let mut simd256_flags = vec![];
        append_simd256_flags(&mut simd256_flags);
        compile_files(
            "libhacl_256.a",
            &files256,
            out_path,
            &simd256_flags,
            &defines,
        );
    }

    compile_files("libhacl.a", &files, out_path, &[], &defines);
}

#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
struct Platform {
    simd128: bool,
    simd256: bool,
    x25519: bool,
    bmi2_adx_support: bool,
    aes_ni: bool,
    pmull: bool,
    adv_simd: bool,
    sha256: bool,
}

fn main() {
    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);
    let out_dir = env::var("OUT_DIR").unwrap();
    let out_path = Path::new(&out_dir);

    // Check platform support
    let platform = Platform {
        simd128: libcrux_platform::simd128_support(),
        simd256: libcrux_platform::simd256_support(),
        aes_ni: libcrux_platform::aes_ni_support(),
        x25519: libcrux_platform::x25519_support(),
        bmi2_adx_support: libcrux_platform::bmi2_adx_support(),
        pmull: libcrux_platform::pmull_support(),
        adv_simd: libcrux_platform::adv_simd_support(),
        sha256: libcrux_platform::sha256_support(),
    };

    // Set re-run trigger for all of c
    println!("cargo:rerun-if-changed=c");
    println!("cargo:rerun-if-changed=h");

    // Moving C library to output to make build easier.
    copy_files(home_path, out_path);
    eprintln!(" >>> out {:?}", out_path);

    // Build the C files
    build(platform, out_path);

    // Set library name to look up
    let library_name = "hacl";

    // Generate new bindings. This is a no-op on Windows.
    create_bindings(platform, home_path);

    // Link hacl library.
    let mode = "static";
    println!("cargo:rustc-link-lib={}={}", mode, library_name);
    if platform.simd128 {
        println!("cargo:rustc-link-lib={}={}", mode, "hacl_128");
    }
    if platform.simd256 {
        println!("cargo:rustc-link-lib={}={}", mode, "hacl_256");
    }
    println!("cargo:rustc-link-search=native={}", out_path.display());
    println!("cargo:lib={}", out_path.display());
}
