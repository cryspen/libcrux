use std::{env, path::Path};

const LIB_NAME: &str = "hacl";
const LIB_128_NAME: &str = "hacl_128";
const LIB_256_NAME: &str = "hacl_256";
#[allow(dead_code)] // FIXME: remove wrong cfg guards
const LIB_25519_NAME: &str = "hacl_curve25519";
#[allow(dead_code)] // FIXME: remove wrong cfg guards
const LIB_VALE_AESGCM_NAME: &str = "vale_aesgcm";

macro_rules! svec {
    ($($x:expr),*$(,)?) => (vec![$($x.to_string()),*]);
}

fn includes(platform: &Platform, home_dir: &Path, include_str: &str) -> Vec<String> {
    let c_path = home_dir.join("c");
    let mut include_path = c_path.join("include");
    if platform.target_env == "msvc" {
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
    ]
}

#[allow(dead_code)]
fn append_aesgcm_flags(platform: &Platform, flags: &mut Vec<String>) {
    if platform.target_env != "msvc" {
        flags.push("-maes".to_string());
        flags.push("-mpclmul".to_string());
    }
}

#[allow(dead_code)]
fn append_simd128_flags(platform: &Platform, flags: &mut Vec<String>, is_bindgen: bool) {
    if (platform.target_arch == "x86" || platform.target_arch == "x86_64")
        && (is_bindgen || platform.target_env != "msvc")
    {
        flags.push("-msse4.1".to_string());
        flags.push("-msse4.2".to_string());
        flags.push("-mavx".to_string());
    }
}

#[allow(dead_code)]
fn append_simd256_flags(platform: &Platform, flags: &mut Vec<String>, is_bindgen: bool) {
    if is_bindgen || platform.target_env != "msvc" {
        flags.push("-mavx2".to_string());
    }
}

#[cfg(feature = "bindings")]
fn create_bindings(platform: &Platform, home_dir: &Path) {
    let mut clang_args = includes(platform, home_dir, "-I");

    let mut bindings = bindgen::Builder::default();

    bindings = bindings
        // Header to wrap HACL headers
        .header("c/config/hacl.h");

    if platform.simd128 {
        append_simd128_flags(platform, &mut clang_args, true);
        clang_args.push("-DHACL_CAN_COMPILE_VEC128".to_string());
        bindings = bindings
            // Header to wrap HACL SIMD 128 headers
            .header("c/config/hacl128.h");
    }

    if platform.simd256 {
        append_simd256_flags(platform, &mut clang_args, true);
        clang_args.push("-DHACL_CAN_COMPILE_VEC256".to_string());
        bindings = bindings
            // Header to wrap HACL SIMD 256 headers
            .header("c/config/hacl256.h");
    }

    if (platform.target_arch == "x86" || platform.target_arch == "x86_64")
        && (platform.target_os == "linux"
            || platform.target_os == "macos"
            || (platform.target_os == "windows"
                && (platform.target_env == "msvc" || platform.target_env == "gnu")))
        && (platform.simd128 && platform.simd256 && platform.aes_ni && platform.pmull)
    {
        clang_args.push("-DHACL_CAN_COMPILE_INLINE_ASM".to_string());
        bindings = bindings
            // Header to wrap EverCrypt_AutoConfig2
            .header("c/config/vale-aes.h");
    }

    let generated_bindings = bindings
        // Set include paths for HACL headers
        .clang_args(clang_args)
        // Allow function we want to have in
        .allowlist_function("Hacl_AEAD_Chacha20Poly1305_.*")
        .allowlist_function("Hacl_Curve25519.*")
        .allowlist_function("Hacl_Hash_SHA2.*")
        .allowlist_function("Hacl_Hash_.*")
        .allowlist_function("Hacl_Blake2.*")
        .allowlist_function("Hacl_HMAC_DRBG.*")
        .allowlist_function("Hacl_Ed25519.*")
        .allowlist_function("Hacl_HKDF_.*")
        .allowlist_function("Hacl_HMAC_.*")
        .allowlist_function("Hacl_P256_.*")
        .allowlist_function("EverCrypt_AEAD_.*")
        .allowlist_function("EverCrypt_AutoConfig2_.*")
        .allowlist_function("Hacl_RSAPSS.*")
        .allowlist_function("hacl_free")
        .allowlist_type("Spec_.*")
        .allowlist_type("Hacl_HMAC_DRBG.*")
        .allowlist_type("Hacl_Streaming.*")
        .allowlist_type("Hacl_Hash_.*")
        .allowlist_var("Spec_.*")
        .allowlist_var("Hacl_Streaming.*")
        // XXX: These functions use uint128 in the API, which is not FFI safe
        .blocklist_type("FStar_UInt128_uint128")
        .blocklist_function("Hacl_Hash_Blake2b_update_multi")
        .blocklist_function("Hacl_Hash_Blake2b_update_last")
        .blocklist_function("Hacl_Hash_Blake2b_Simd256_update_multi")
        .blocklist_function("Hacl_Hash_Blake2b_Simd256_update_last")
        // Disable tests to avoid warnings and keep it portable
        .layout_tests(false)
        // Generate bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .use_core()
        .generate()
        .expect("Unable to generate bindings");

    let home_bindings = home_dir.join("src/bindings.rs");
    generated_bindings
        .write_to_file(home_bindings)
        .expect("Couldn't write bindings!");
}

fn compile_files(
    platform: &Platform,
    library_name: &str,
    files: &[String],
    vale_files: &[String],
    home_path: &Path,
    args: &[String],
    defines: &[(&str, &str)],
) {
    let src_prefix = home_path.join("c").join("src");
    let src_prefix = if platform.target_env == "msvc" {
        src_prefix.join("msvc")
    } else {
        src_prefix
    };
    let vale_prefix = home_path.join("c").join("vale").join("src");

    let mut build = cc::Build::new();
    build.files(
        files
            .iter()
            .map(|fname| {
                if fname == "hacl.c" {
                    home_path.join("c").join("config").join(fname)
                } else {
                    src_prefix.join(fname)
                }
            })
            .chain(vale_files.iter().map(|fname| vale_prefix.join(fname))),
    );
    // TODO: enable this when all warnings are gone
    // Windows: fstar_uint128_msvc.h(220): warning C4554: '>>': check operator precedence for possible error; use parentheses to clarify precedence
    // .warnings_into_errors(true);

    for include in includes(platform, home_path, "") {
        build.include(include);
    }
    build.opt_level(3);
    build.static_crt(true);
    for arg in args {
        build.flag(arg);
    }
    for define in defines {
        build.define(define.0, define.1);
    }

    build.compile(library_name);
}

fn build(platform: &Platform, home_path: &Path) {
    // Select files to build. Right now this is very limited to what we need.
    let mut files = svec!["hacl.c"];
    #[cfg(not(feature = "sha3"))]
    files.append(&mut svec![
        "Hacl_NaCl.c",
        "Hacl_Salsa20.c",
        "Hacl_MAC_Poly1305.c",
        "Hacl_Curve25519_51.c",
        // "Hacl_Gf128_CT64.c",
        // "Hacl_AES_128_CTR32_BitSlice.c",
        // "Hacl_AES_128_GCM_CT64.c",
        // "Hacl_AES_256_CTR32_BitSlice.c",
        // "Hacl_AES_256_GCM_CT64.c",
        "Hacl_HMAC_DRBG.c",
        "Hacl_HMAC.c",
        "Hacl_Hash_SHA2.c",
        "Hacl_Hash_Blake2b.c",
        "Hacl_Hash_Blake2s.c",
        "Lib_Memzero0.c",
        "Hacl_Ed25519.c",
        "Hacl_EC_Ed25519.c",
        "Hacl_Hash_Base.c",
        "Hacl_Bignum256_32.c",
        "Hacl_Bignum.c",
        "Hacl_Bignum256.c",
        "Hacl_Bignum32.c",
        "Hacl_Bignum4096_32.c",
        "Hacl_GenericField32.c",
        "Hacl_AEAD_Chacha20Poly1305.c",
        "Hacl_Chacha20.c",
        "Hacl_Chacha20_Vec32.c",
        "Hacl_P256.c",
        "Hacl_K256_ECDSA.c",
        "Hacl_EC_K256.c",
        "Hacl_FFDHE.c",
        "Hacl_Hash_SHA3.c",
        "Hacl_Hash_SHA3_Scalar.c",
        "Hacl_Hash_SHA1.c",
        "Hacl_Hash_MD5.c",
        "Hacl_HKDF.c",
        "Hacl_RSAPSS.c",
    ]);
    #[cfg(feature = "sha3")]
    files.append(&mut svec!["Hacl_Hash_SHA3_Scalar.c", "Hacl_Hash_SHA3.c"]);

    let mut defines = vec![];
    defines.push(("RELOCATABLE", "1"));

    if platform.int128 {
        defines.push(("HACL_CAN_COMPILE_UINT128", "1"));
    }
    if platform.target_arch == "x86_64" {
        defines.push(("HACL_CAN_COMPILE_VALE", "1"));
        defines.push(("HACL_CAN_COMPILE_INTRINSICS", "1"));
    }
    let hacl_target_arch = platform.hacl_target_arch.to_string();
    defines.push(("TARGET_ARCHITECTURE", hacl_target_arch.as_str()));
    defines.push(("LINUX_NO_EXPLICIT_BZERO", "1")); // We disable this to avoid running into issues.

    // Platform detection
    if platform.simd128 {
        #[cfg(not(feature = "sha3"))]
        let files128 = svec![
            "Hacl_Hash_Blake2s_Simd128.c",
            "Hacl_Bignum4096.c",
            "Hacl_Bignum64.c",
            "Hacl_GenericField64.c",
            "Hacl_AEAD_Chacha20Poly1305_Simd128.c",
            "Hacl_MAC_Poly1305_Simd128.c",
            "Hacl_Chacha20_Vec128.c",
            "Hacl_SHA2_Vec128.c",
            "Hacl_HKDF_Blake2s_128.c",
            "Hacl_HMAC_Blake2s_128.c",
        ];
        #[cfg(feature = "sha3")]
        let files128 = svec![];

        defines.append(&mut vec![("HACL_CAN_COMPILE_VEC128", "1")]);

        let mut simd128_flags = vec![];
        append_simd128_flags(platform, &mut simd128_flags, false);
        if !files128.is_empty() {
            compile_files(
                platform,
                LIB_128_NAME,
                &files128,
                &[],
                home_path,
                &simd128_flags,
                &defines,
            );
        }
    }
    if platform.simd256 {
        #[cfg(not(feature = "sha3"))]
        let files256 = svec![
            "Hacl_Hash_Blake2b_Simd256.c",
            "Hacl_AEAD_Chacha20Poly1305_Simd256.c",
            "Hacl_MAC_Poly1305_Simd256.c",
            "Hacl_Chacha20_Vec256.c",
            "Hacl_SHA2_Vec256.c",
            "Hacl_Hash_SHA3_Simd256.c",
            "Hacl_HKDF_Blake2b_256.c",
            "Hacl_HMAC_Blake2b_256.c",
        ];
        #[cfg(feature = "sha3")]
        let files256 = svec!["Hacl_Hash_SHA3_Simd256.c"];

        defines.append(&mut vec![("HACL_CAN_COMPILE_VEC256", "1")]);

        let mut simd256_flags = vec![];
        append_simd256_flags(platform, &mut simd256_flags, false);
        compile_files(
            platform,
            LIB_256_NAME,
            &files256,
            &[],
            home_path,
            &simd256_flags,
            &defines,
        );
    }

    #[cfg(not(feature = "sha3"))]
    if (platform.target_arch == "x86" || platform.target_arch == "x86_64")
        && (platform.target_env == "gnu"
            || platform.target_os == "linx"
            || platform.target_os == "macos"
            || (platform.target_os == "windows" && platform.target_env == "msvc"))
    {
        if platform.x25519 {
            let files_curve25519_64 = svec!["Hacl_Curve25519_64.c",];
            let mut files_curve25519 = vec![];
            if cfg!(target_os = "linux") {
                files_curve25519.push("curve25519-x86_64-linux.S".to_string());
            } else if cfg!(all(target_os = "windows", target_env = "msvc")) {
                files_curve25519.push("curve25519-x86_64-msvc.asm".to_string());
            } else if cfg!(all(target_os = "windows", target_env = "gnu")) {
                files_curve25519.push("curve25519-x86_64-mingw.S".to_string());
            } else if cfg!(target_os = "macos") {
                files_curve25519.push("curve25519-x86_64-darwin.S".to_string());
            }
            if cfg!(all(target_arch = "x86_64", target_env = "gnu")) {
                defines.append(&mut vec![("HACL_CAN_COMPILE_INLINE_ASM", "1")]);
            }

            compile_files(
                platform,
                LIB_25519_NAME,
                &files_curve25519_64,
                &files_curve25519,
                home_path,
                &[],
                &defines,
            );
        }
    }

    #[cfg(not(feature = "sha3"))]
    if (platform.target_arch == "x86" || platform.target_arch == "x86_64")
        && (platform.target_os == "linux"
            || platform.target_os == "macos"
            || (platform.target_os == "windows"
                || (platform.target_env == "msvc" || platform.target_env == "gnu")))
    {
        if platform.simd128 && platform.simd256 && platform.aes_ni && platform.pmull {
            let files_evercrypt = svec![
                "EverCrypt_AutoConfig2.c",
                "EverCrypt_Chacha20Poly1305.c",
                "EverCrypt_AEAD.c",
            ];
            let mut files_aesgcm = vec![];
            if cfg!(target_os = "linux") {
                files_aesgcm.push("cpuid-x86_64-linux.S".to_string());
                files_aesgcm.push("aesgcm-x86_64-linux.S".to_string());
            } else if cfg!(all(target_os = "windows", target_env = "msvc")) {
                files_aesgcm.push("cpuid-x86_64-msvc.asm".to_string());
                files_aesgcm.push("aesgcm-x86_64-msvc.asm".to_string());
            } else if cfg!(all(target_os = "windows", target_env = "gnu")) {
                files_aesgcm.push("cpuid-x86_64-mingw.S".to_string());
                files_aesgcm.push("aesgcm-x86_64-mingw.S".to_string());
            } else if cfg!(target_os = "macos") {
                files_aesgcm.push("cpuid-x86_64-darwin.S".to_string());
                files_aesgcm.push("aesgcm-x86_64-darwin.S".to_string());
            }
            defines.append(&mut vec![("HACL_CAN_COMPILE_VALE", "1")]);

            let mut aesgcm_flags = vec![];
            append_simd128_flags(platform, &mut aesgcm_flags, false);
            append_simd256_flags(platform, &mut aesgcm_flags, false);
            append_aesgcm_flags(platform, &mut aesgcm_flags);
            compile_files(
                platform,
                LIB_VALE_AESGCM_NAME,
                &files_evercrypt,
                &files_aesgcm,
                home_path,
                &aesgcm_flags,
                &defines,
            );
        }
    }

    compile_files(platform, LIB_NAME, &files, &[], home_path, &[], &defines);
}

#[derive(Clone, Debug, Default)]
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
    int128: bool,
    target_arch: String,
    target_env: String,
    target_os: String,
    hacl_target_arch: u8,
}

fn main() {
    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap();
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap();

    let target = env::var("TARGET").unwrap();
    let host = env::var("HOST").unwrap();

    // Check platform support
    let platform = if target_arch != "wasm32" && host == target {
        let x86 = target_arch == "x86";
        let hacl_target_arch = match target.as_str() {
            "x86" => 1,
            "x86_64" => 2,
            "arm" | "armv7" => 3,
            "aarch64" => 4,
            // 5: not sure what systemz is.
            "powerpc64" => 6,
            _ => 0, //unknown
        };
        Platform {
            simd128: !x86 && libcrux_platform::simd128_support(),
            simd256: !x86 && libcrux_platform::simd256_support(),
            aes_ni: libcrux_platform::aes_ni_support(),
            x25519: !x86 && libcrux_platform::x25519_support(),
            bmi2_adx_support: libcrux_platform::bmi2_adx_support(),
            pmull: libcrux_platform::pmull_support(),
            adv_simd: libcrux_platform::adv_simd_support(),
            sha256: libcrux_platform::sha256_support(),
            target_arch: target_arch.clone(),
            target_env: target_env.clone(),
            target_os: target_os.clone(),
            int128: target_arch == "x86_64" || target_arch == "aarch64",
            hacl_target_arch,
        }
    } else {
        // On wasm or cross compilation we don't enable any specific features.
        Platform {
            target_arch: target_arch.clone(),
            target_env: target_env.clone(),
            target_os: target_os.clone(),
            ..Default::default()
        }
    };

    // Set re-run trigger for all of c
    println!("cargo:rerun-if-changed=c");

    // Build the C files
    build(&platform, home_path);

    // Generate new bindings.
    // This is only done if the corresponding environment variable is set.
    #[cfg(feature = "bindings")]
    if target_arch != "wasm32" {
        create_bindings(&platform, home_path);
    }
}
