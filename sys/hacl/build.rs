use std::{env, path::Path};

macro_rules! svec {
    ($($x:expr),*$(,)?) => (vec![$($x.to_string()),*]);
}

fn includes(home_dir: &Path, include_str: &str) -> Vec<String> {
    let c_path = home_dir.join("c");
    let mut include_path = c_path.join("include");
    if cfg!(target_env = "msvc") {
        include_path = include_path.join("msvc");
    }
    vec![
        format!("{}{}", include_str, include_path.display()),
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
        format!(
            "{}{}",
            include_str,
            c_path.join("vale").join("include").display()
        ),
    ]
}

#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64"),
    any(
        target_os = "linux",
        target_os = "macos",
        all(target_os = "windows", any(target_env = "msvc", target_env = "gnu"))
    )
))]
fn append_aesgcm_flags(flags: &mut Vec<String>) {
    if cfg!(not(target_env = "msvc")) {
        flags.push("-maes".to_string());
        flags.push("-mpclmul".to_string());
    }
}

fn append_simd128_flags(flags: &mut Vec<String>, is_bindgen: bool) {
    if cfg!(any(target_arch = "x86", target_arch = "x86_64"))
        && (is_bindgen || cfg!(not(target_env = "msvc")))
    {
        flags.push("-msse4.1".to_string());
        flags.push("-msse4.2".to_string());
        flags.push("-mavx".to_string());
    }
}

fn append_simd256_flags(flags: &mut Vec<String>, is_bindgen: bool) {
    if is_bindgen || cfg!(not(target_env = "msvc")) {
        flags.push("-mavx2".to_string());
    }
}

fn create_bindings(platform: Platform, home_dir: &Path) {
    let mut clang_args = includes(home_dir, "-I");

    let mut bindings = bindgen::Builder::default();

    bindings = bindings
        // Header to wrap HACL headers
        .header("c/config/hacl.h");
    if platform.simd128 {
        append_simd128_flags(&mut clang_args, true);
        clang_args.push("-DSIMD128".to_string());
        bindings = bindings
            // Header to wrap HACL SIMD 128 headers
            .header("c/config/hacl128.h");
    }
    if platform.simd256 {
        append_simd256_flags(&mut clang_args, true);
        clang_args.push("-DSIMD256".to_string());
        bindings = bindings
            // Header to wrap HACL SIMD 256 headers
            .header("c/config/hacl256.h");
    }
    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        any(
            target_os = "linux",
            target_os = "macos",
            all(target_os = "windows", any(target_env = "msvc", target_env = "gnu"))
        )
    ))]
    if platform.simd128 && platform.aes_ni && platform.pmull {
        bindings = bindings
            // Header to wrap Vale header
            .header("c/config/vale-aes.h");
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
        .allowlist_function("Hacl_HMAC_DRBG.*")
        .allowlist_function("Hacl_Ed25519.*")
        .allowlist_function("Hacl_HKDF_.*")
        .allowlist_function("Hacl_HMAC_.*")
        .allowlist_function("Hacl_P256_.*")
        .allowlist_function("EverCrypt_AEAD_.*")
        .allowlist_function("aes128_.*")
        .allowlist_function("aes256_.*")
        .allowlist_function("gcm128_.*")
        .allowlist_function("gcm256_.*")
        .allowlist_function("compute_iv_stdcall")
        .allowlist_type("Spec_.*")
        .allowlist_type("Hacl_Streaming_SHA2.*")
        .allowlist_type("Hacl_HMAC_DRBG.*")
        .allowlist_type("Hacl_Streaming.*")
        .allowlist_var("Spec_.*")
        .allowlist_var("Hacl_Streaming.*")
        // XXX: These functions use uint128 in the API, which is not FFI safe
        .blocklist_function("Hacl_Blake2b_32_blake2b_update_multi")
        .blocklist_function("Hacl_Blake2b_32_blake2b_update_last")
        .blocklist_function("Hacl_Blake2b_256_blake2b_update_multi")
        .blocklist_function("Hacl_Blake2b_256_blake2b_update_last")
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

fn compile_files(
    library_name: &str,
    files: &[String],
    home_path: &Path,
    args: &[String],
    defines: &[(&str, &str)],
    is_vale: bool,
) {
    let src_prefix = if is_vale {
        home_path.join("c").join("vale").join("src")
    } else if cfg!(target_env = "msvc") {
        home_path.join("c").join("src").join("msvc")
    } else {
        home_path.join("c").join("src")
    };

    let mut build = cc::Build::new();
    build
        .files(files.iter().map(|fname| src_prefix.join(fname)))
        // XXX: There are too many warnings for now
        .warnings(false);

    for include in includes(home_path, "") {
        build.include(include);
    }
    build.opt_level(3);
    for arg in args {
        build.flag(arg);
    }
    for define in defines {
        build.define(define.0, define.1);
    }

    build.compile(library_name);
}

fn build(platform: Platform, home_path: &Path) {
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
    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        any(
            target_os = "linux",
            target_os = "macos",
            all(target_os = "windows", any(target_env = "msvc", target_env = "gnu"))
        )
    ))]
    if platform.simd128 && platform.aes_ni && platform.pmull {
        let mut files_aesgcm = vec![];
        if cfg!(target_os = "linux") {
            files_aesgcm.push("aesgcm-x86_64-linux.S".to_string())
        } else if cfg!(all(target_os = "windows", target_env = "msvc")) {
            files_aesgcm.push("aesgcm-x86_64-msvc.asm".to_string())
        } else if cfg!(all(target_os = "windows", target_env = "gnu")) {
            files_aesgcm.push("aesgcm-x86_64-mingw.S".to_string())
        } else if cfg!(target_os = "macos") {
            files_aesgcm.push("aesgcm-x86_64-darwin.S".to_string())
        }

        let mut aesgcm_flags = vec![];
        append_simd128_flags(&mut aesgcm_flags, false);
        append_aesgcm_flags(&mut aesgcm_flags);
        compile_files(
            "libhacl_aesgcm.a",
            &files_aesgcm,
            home_path,
            &aesgcm_flags,
            &defines,
            true,
        );
    }
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
        append_simd128_flags(&mut simd128_flags, false);
        compile_files(
            "libhacl_128.a",
            &files128,
            home_path,
            &simd128_flags,
            &defines,
            false,
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
        append_simd256_flags(&mut simd256_flags, false);
        compile_files(
            "libhacl_256.a",
            &files256,
            home_path,
            &simd256_flags,
            &defines,
            false,
        );
    }

    compile_files("libhacl.a", &files, home_path, &[], &defines, false);
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

    // Build the C files
    build(platform, home_path);

    // Set library name to look up
    const LIB_NAME: &str = "hacl";

    // Generate new bindings.
    create_bindings(platform, home_path);

    // Link hacl library.
    const MODE: &str = "static";
    println!("cargo:rustc-link-lib={}={}", MODE, LIB_NAME);
    if platform.simd128 {
        println!("cargo:rustc-link-lib={}={}", MODE, "hacl_128");
    }
    if platform.simd256 {
        println!("cargo:rustc-link-lib={}={}", MODE, "hacl_256");
    }
    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        any(
            target_os = "linux",
            target_os = "macos",
            all(target_os = "windows", any(target_env = "msvc", target_env = "gnu"))
        )
    ))]
    if platform.simd128 && platform.aes_ni && platform.pmull {
        println!("cargo:rustc-link-lib={}={}", MODE, "hacl_aesgcm");
    }
    println!("cargo:rustc-link-search=native={}", out_path.display());
    println!("cargo:lib={}", out_path.display());
}
