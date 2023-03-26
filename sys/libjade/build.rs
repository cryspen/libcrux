#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x64_build {
    use std::{path::Path, process::Command};

    macro_rules! svec {
        ($($x:expr),*$(,)?) => (vec![$($x.to_string()),*]);
    }

    pub fn copy_files(home_path: &Path, out_path: &Path) {
        let mut options = fs_extra::dir::CopyOptions::new();
        options.overwrite = true;
        fs_extra::dir::copy(home_path.join("jazz"), out_path, &options).unwrap();
    }

    pub fn append_simd128_flags(flags: &mut Vec<String>) {
        // Platform detection
        if simd128_support() {
            flags.push("-DSIMD128".to_string());
            flags.push("-mavx".to_string());
        }
    }

    pub fn append_simd256_flags(flags: &mut Vec<String>) {
        // Platform detection
        if simd256_support() {
            flags.push("-DSIMD256".to_string());
            flags.push("-mavx2".to_string());
        }
    }

    #[cfg(not(windows))]
    pub fn create_bindings(home_dir: &Path) {
        let jazz_dir = home_dir.join("jazz");
        let mut clang_args = vec![format!("-I{}", jazz_dir.join("include").display())];
        append_simd128_flags(&mut clang_args);
        append_simd256_flags(&mut clang_args);

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
            // Block everything we don't need or define ourselves.
            .blocklist_type("__.*")
            // Disable tests to avoid warnings and keep it portable
            .layout_tests(false)
            // Generate bindings
            .parse_callbacks(Box::new(bindgen::CargoCallbacks))
            .generate()
            .expect("Unable to generate bindings");

        let home_bindings = home_dir.join("src/bindings.rs");
        bindings
            .write_to_file(home_bindings)
            .expect("Couldn't write bindings!");
    }

    #[cfg(windows)]
    pub fn create_bindings(_: &Path, _: &Path) {}

    pub fn compile_files(files: &[String], out_path: &Path, args: &[String]) {
        let jazz_dir = out_path.join("jazz");
        let mut clang_args = vec![format!("-I{}", jazz_dir.join("include").display())];
        clang_args.push("-O3".to_string());
        clang_args.push("-c".to_string());
        clang_args.extend_from_slice(args);

        let mut build_cmd = Command::new("clang");
        let mut build_args = clang_args;
        build_args.extend_from_slice(files);
        println!(" >>> {}", out_path.join("jazz").display());
        println!(" >>> {}", build_args.join(" "));

        build_cmd
            .current_dir(out_path.join("jazz"))
            .args(&build_args);
        println!(" >>> build_cmd: {:?}", build_cmd);
        println!("     current dir: {:?}", build_cmd.get_current_dir());

        let build_status = build_cmd.status().expect("Failed to run build.");
        println!(" >>> build status: {:?}", build_status);
        println!(" >>> out {:?}", out_path);
        assert!(build_status.success());
    }

    pub fn build(out_path: &Path, cross_target: Option<String>) {
        let args = cross_target
            .map(|s| match s.as_str() {
                // We only support cross compilation here for now.
                // We assume that we're using clang and can just add the target
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
        ];
        let mut all_files = files.clone();

        // Platform detection
        if simd256_support() {
            let files256 = svec![
                "sha3_224_avx2.s",
                "sha3_256_avx2.s",
                "sha3_384_avx2.s",
                "sha3_512_avx2.s",
                "chacha20_avx2.s",
                "poly1305_avx2.s",
            ];
            all_files.extend_from_slice(&files256);

            let mut simd256_flags = args.clone();
            append_simd256_flags(&mut simd256_flags);
            compile_files(&files256, out_path, &simd256_flags);
        }
        if simd128_support() {
            let files128 = svec!["chacha20_avx.s", "poly1305_avx.s",];
            all_files.extend_from_slice(&files128);

            let mut simd128_flags = args.clone();
            append_simd128_flags(&mut simd128_flags);
            compile_files(&files128, out_path, &simd128_flags);
        }

        let mut object_files = vec![];
        compile_files(&files, out_path, &args);
        for file in all_files {
            object_files.push(Path::new(&file).with_extension("o"));
        }

        // Link
        let mut build_cmd = Command::new("ar");
        build_cmd
            .current_dir(out_path.join("jazz"))
            .args(&["-r", &out_path.join("libjade.a").display().to_string()])
            .args(&object_files);
        println!(" >>> build_cmd: {:?}", build_cmd);
        println!("     current dir: {:?}", build_cmd.get_current_dir());

        let build_status = build_cmd.status().expect("Failed to link.");
        println!("{:?}", build_status);
        assert!(build_status.success());
    }

    // === hardware detection
    pub fn simd128_support() -> bool {
        std::arch::is_x86_feature_detected!("avx")
    }

    pub fn simd256_support() -> bool {
        std::arch::is_x86_feature_detected!("avx2")
    }
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn main() {
    use std::{env, path::Path};
    use x64_build::*;

    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);
    let out_dir = env::var("OUT_DIR").unwrap();
    let out_path = Path::new(&out_dir);
    let target = env::var("TARGET").unwrap();
    let host = env::var("HOST").unwrap();

    let cross_target = if target != host { Some(target) } else { None };
    if cross_target.is_none() && host == "aarch64-apple-darwin" {
        panic!("libjade does not support aarch64-apple-darwin");
    }

    if simd128_support() {
        println!("cargo:rustc-cfg=simd128");
    }
    if simd256_support() {
        println!("cargo:rustc-cfg=simd256");
    }

    // Moving C/ASM code to output to make build easier.
    copy_files(home_path, out_path);
    eprintln!(" >>> out {:?}", out_path);

    // Build the C/ASM files
    build(out_path, cross_target);

    // Set library name to look up
    let library_name = "jade";

    // Set re-run trigger for all of s
    println!("cargo:rerun-if-changed=cs");

    // Generate new bindings. This is a no-op on Windows.
    create_bindings(home_path);

    // Link hacl library.
    let mode = "static";
    println!("cargo:rustc-link-lib={}={}", mode, library_name);
    println!("cargo:rustc-link-search=native={}", out_path.display());
    println!("cargo:lib={}", out_path.display());
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn main() {
    eprintln!("Only x86 and x64 CPUs are supported.");
}
