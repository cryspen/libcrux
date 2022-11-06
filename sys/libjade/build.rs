use std::{env, path::Path, process::Command};

macro_rules! svec {
    ($($x:expr),*$(,)?) => (vec![$($x.to_string()),*]);
}

fn copy_files(home_path: &Path, out_path: &Path) {
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    fs_extra::dir::copy(home_path.join("jazz"), out_path, &options).unwrap();
}

fn append_simd128_flags(flags: &mut Vec<String>) {
    // Platform detection
    if cfg!(simd128) {
        flags.push("-DSIMD128".to_string());
        flags.push("-mavx".to_string());
    }
}

fn append_simd256_flags(flags: &mut Vec<String>) {
    // Platform detection
    if cfg!(simd256) {
        flags.push("-DSIMD256".to_string());
        flags.push("-mavx2".to_string());
    }
}

#[cfg(not(windows))]
fn create_bindings(home_dir: &Path) {
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
fn create_bindings(_: &Path, _: &Path) {}

fn compile_files(files: &[String], out_path: &Path, args: &[String]) {
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

fn build(out_path: &Path) {
    let files = svec![
        "sha256.s",
        "x25519_ref.s",
        "x25519_mulx.s",
        "sha3_224_ref.s",
        "sha3_256_ref.s",
        "sha3_384_ref.s",
        "sha3_512_ref.s",
    ];
    let mut all_files = files.clone();

    // Platform detection
    if cfg!(simd256) {
        let files256 = svec![
            "sha3_224_avx2.s",
            "sha3_256_avx2.s",
            "sha3_384_avx2.s",
            "sha3_512_avx2.s",
        ];
        all_files.extend_from_slice(&files256);

        let mut simd256_flags = vec![];
        append_simd256_flags(&mut simd256_flags);
        compile_files(&files256, out_path, &simd256_flags);
    }

    let mut object_files = vec![];
    compile_files(&files, out_path, &[]);
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

fn main() {
    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);
    let out_dir = env::var("OUT_DIR").unwrap();
    let out_path = Path::new(&out_dir);

    // Moving C/ASM code to output to make build easier.
    copy_files(home_path, out_path);
    eprintln!(" >>> out {:?}", out_path);

    // Build the C/ASM files
    build(out_path);

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
