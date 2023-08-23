use std::{env, path::Path};

macro_rules! svec {
        ($($x:expr),*$(,)?) => (vec![$($x.to_string()),*]);
    }

fn copy_files(home_path: &Path, out_path: &Path) {
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    fs_extra::dir::copy(home_path.join("jazz"), out_path, &options).unwrap();
}

fn append_simd128_flags(flags: &mut Vec<String>) {
    flags.push("-DSIMD128".to_string());
    flags.push("-mavx".to_string());
}

fn append_simd256_flags(flags: &mut Vec<String>) {
    flags.push("-DSIMD256".to_string());
    flags.push("-mavx2".to_string());
}

#[cfg(not(windows))]
fn create_bindings(platform: Platform, home_dir: &Path) {
    let jazz_dir = home_dir.join("jazz");
    let mut clang_args = vec![format!("-I{}", jazz_dir.join("include").display())];
    if platform.simd128 {
        append_simd128_flags(&mut clang_args);
    }
    if platform.simd256 {
        append_simd256_flags(&mut clang_args);
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
        // Block everything we don't need or define ourselves.
        .blocklist_type("__.*")
        // Disable tests to avoid warnings and keep it portable
        .layout_tests(false)
        // Generate bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .use_core()
        .generate()
        .expect("Unable to generate bindings");

    let home_bindings = home_dir.join("src/bindings.rs");
    bindings
        .write_to_file(home_bindings)
        .expect("Couldn't write bindings!");
}

#[cfg(windows)]
fn create_bindings(platform: Platform, _: &Path) {}

fn compile_files(library_name: &str, files: &[String], out_path: &Path, args: &[String]) {
    let jazz_dir = out_path.join("jazz");

    let mut build = cc::Build::new();
    build
        .files(files.iter().map(|fname| jazz_dir.join(fname)))
        .warnings_into_errors(true)
        .no_default_flags(true);

    build.include(jazz_dir.join("include"));
    build.flag("-O3").flag("-c");
    for arg in args {
        build.flag(arg);
    }

    build.compile(library_name);
}

fn build(platform: Platform, out_path: &Path, cross_target: Option<String>) {
    let args = cross_target
        .map(|s| match s.as_str() {
            // We only support cross compilation here for now.
            "x86_64-apple-darwin" => svec!["-target", "x86_64-apple-darwin"],
            _ => panic!("Unsupported cross compilation target {s}"),
        })
        .unwrap_or_default();

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
    ];
    compile_files("libjade.a", &files, out_path, &args);

    if platform.simd256 {
        let files256 = svec![
            "sha3_224_avx2.s",
            "sha3_256_avx2.s",
            "sha3_384_avx2.s",
            "sha3_512_avx2.s",
            "chacha20_avx2.s",
            "poly1305_avx2.s",
        ];

        let mut simd256_flags = args.clone();
        append_simd256_flags(&mut simd256_flags);
        compile_files("libjade_256.a", &files256, out_path, &simd256_flags);
    }

    if platform.simd128 {
        let files128 = svec!["chacha20_avx.s", "poly1305_avx.s",];

        let mut simd128_flags = args.clone();
        append_simd128_flags(&mut simd128_flags);
        compile_files("libjade_128.a", &files128, out_path, &simd128_flags);
    }
}

#[derive(Debug, Clone, Copy)]
struct Platform {
    simd128: bool,
    simd256: bool,
}

pub fn main() -> Result<(), u8> {
    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);
    let out_dir = env::var("OUT_DIR").unwrap();
    let out_path = Path::new(&out_dir);
    let target = env::var("TARGET").unwrap();
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let host = env::var("HOST").unwrap();

    if target_arch != "x86_64" && target_arch != "x86" {
        eprintln!(" ! Only x86 and x64 CPUs are supported !");
        return Err(1);
    }

    let cross_target = if target != host {
        Some(target.clone())
    } else {
        None
    };

    // If cross compiling, we assume to have it all.
    let platform = if cross_target.is_some() {
        Platform {
            simd128: true,
            simd256: true,
        }
    } else {
        Platform {
            simd128: std::arch::is_x86_feature_detected!("avx"),
            simd256: std::arch::is_x86_feature_detected!("avx2"),
        }
    };

    // Moving C/ASM code to output to make build easier.
    copy_files(home_path, out_path);
    eprintln!(" >>> out {:?}", out_path);

    // Build the C/ASM files
    build(platform, out_path, cross_target);

    // Set library name to look up
    let library_name = "jade";

    // Set re-run trigger for all of s
    println!("cargo:rerun-if-changed=cs");

    // Generate new bindings. This is a no-op on Windows.
    create_bindings(platform, home_path);

    // Link hacl library.
    let mode = "static";
    println!("cargo:rustc-link-lib={}={}", mode, library_name);
    if platform.simd128 {
        println!("cargo:rustc-link-lib={}={}", mode, "jade_128");
    }
    if platform.simd256 {
        println!("cargo:rustc-link-lib={}={}", mode, "jade_256");
    }
    println!("cargo:rustc-link-search=native={}", out_path.display());
    println!("cargo:lib={}", out_path.display());

    Ok(())
}
