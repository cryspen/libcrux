use std::{env, path::Path};

macro_rules! svec {
        ($($x:expr),*$(,)?) => (vec![$($x.to_string()),*]);
    }

fn append_simd128_flags(flags: &mut Vec<String>) {
    flags.push("-mavx".to_string());
}

fn append_simd256_flags(flags: &mut Vec<String>) {
    flags.push("-mavx2".to_string());
}

#[cfg(feature = "bindings")]
fn create_bindings(platform: Platform, home_dir: &Path) {
    let jazz_dir = home_dir.join("jazz");
    let mut clang_args = vec![format!("-I{}", jazz_dir.join("include").display())];
    if platform.simd128 {
        append_simd128_flags(&mut clang_args);
        clang_args.push("-DSIMD128".to_string());
    }
    if platform.simd256 {
        append_simd256_flags(&mut clang_args);
        clang_args.push("-DSIMD256".to_string());
    }

    let bindings = bindgen::Builder::default()
        // Header to wrap headers
        .header("jazz/include/libjade.h")
        // Set include paths for headers
        .clang_args(clang_args)
        // Allow function we want to have in
        .allowlist_function("jade_hash_.*")
        .allowlist_var("JADE_HASH_.*")
        .allowlist_function("jade_scalarmult_curve25519_.*")
        .allowlist_var("JADE_SCALARMULT_CURVE25519_.*")
        .allowlist_function("jade_hash_sha3_.*")
        .allowlist_var("JADE_HASH_SHA3_.*")
        .allowlist_function("jade_onetimeauth_poly1305_.*")
        .allowlist_var("JADE_ONETIMEAUTH_POLY1305_.*")
        .allowlist_function("jade_stream_chacha_chacha20.*")
        .allowlist_var("JADE_STREAM_CHACHA_CHACHA20_.*")
        .allowlist_function("jade_kem_kyber_kyber768_.*")
        .allowlist_var("JADE_KEM_KYBER_KYBER768_.*")
        .allowlist_function("randombytes")
        .allowlist_function("__jasmin_syscall_randombytes__")
        // Block everything we don't need or define ourselves.
        .blocklist_type("__.*")
        // Disable tests to avoid warnings and keep it portable
        .layout_tests(false)
        // Generate bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .use_core()
        .generate()
        .expect("Unable to generate bindings");

    let home_bindings = home_dir.join("src/bindings.rs");
    bindings
        .write_to_file(home_bindings)
        .expect("Couldn't write bindings!");
}

fn compile_files(library_name: &str, files: &[String], home_path: &Path, args: &[String]) {
    let jazz_dir = home_path.join("jazz");

    let mut build = cc::Build::new();
    build
        .files(files.iter().map(|fname| jazz_dir.join(fname)))
        .warnings_into_errors(true)
        .no_default_flags(true);

    build.include(jazz_dir.join("include"));
    build.opt_level(3);
    for arg in args {
        build.flag(arg);
    }

    build.compile(library_name);
}

fn build(platform: Platform, home_path: &Path) {
    let args = Vec::new();

    let files = svec![
        "sha256.s",
        "x25519_ref.s",
        "x25519_mulx.s",
        "sha3_224_ref.s",
        "sha3_256_ref.s",
        "sha3_384_ref.s",
        "sha3_512_ref.s",
        "chacha20_ref.s",
        "poly1305_ref.s",
        "kyber_kyber768_ref.s",
        "randombytes.c",
    ];
    compile_files("jade", &files, home_path, &args);

    if platform.simd256 {
        let files256 = svec![
            "sha3_224_avx2.s",
            "sha3_256_avx2.s",
            "sha3_384_avx2.s",
            "sha3_512_avx2.s",
            "chacha20_avx2.s",
            "poly1305_avx2.s",
            "kyber_kyber768_avx2.s",
        ];

        let mut simd256_flags = args.clone();
        append_simd256_flags(&mut simd256_flags);
        compile_files("jade_256", &files256, home_path, &simd256_flags);
    }

    if platform.simd128 {
        let files128 = svec!["chacha20_avx.s", "poly1305_avx.s",];

        let mut simd128_flags = args.clone();
        append_simd128_flags(&mut simd128_flags);
        compile_files("jade_128", &files128, home_path, &simd128_flags);
    }
}

#[derive(Debug, Clone, Copy)]
struct Platform {
    simd128: bool,
    simd256: bool,
}

pub fn main() {
    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);
    let target = env::var("TARGET").unwrap();
    let host = env::var("HOST").unwrap();

    // If cross compiling, we assume to have it all.
    let platform = if target != host {
        Platform {
            simd128: true,
            simd256: true,
        }
    } else {
        Platform {
            simd128: libcrux_platform::simd128_support(),
            simd256: libcrux_platform::simd256_support(),
        }
    };

    // Build the C/ASM files
    build(platform, home_path);

    // Set re-run trigger for all of s
    println!("cargo:rerun-if-changed=jazz");

    // Generate new bindings.
    #[cfg(feature = "bindings")]
    create_bindings(platform, home_path);
}
