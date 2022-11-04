#[cfg(not(windows))]
extern crate bindgen;

use std::{env, path::Path, process::Command};

fn includes(home_dir: &Path) -> Vec<String> {
    let c_path = home_dir.join("c");
    vec![
        format!("-I{}", c_path.join("include").display()),
        format!("-I{}", c_path.join("karamel").join("include").display()),
        format!(
            "-I{}",
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
    // Platform detection
    if cfg!(simd128) {
        flags.push("-DSIMD128".to_string());
        if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
            flags.push("-msse4.1".to_string());
            flags.push("-msse4.2".to_string());
            flags.push("-mavx".to_string());
        }
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
    let mut clang_args = includes(home_dir);
    append_simd128_flags(&mut clang_args);
    append_simd256_flags(&mut clang_args);

    let bindings = bindgen::Builder::default()
        // Header to wrap HACL headers
        .header("c/include/hacl.h")
        // Set include paths for HACL headers
        .clang_args(clang_args)
        // Allow function we want to have in
        .allowlist_function("Hacl_Chacha20Poly1305.*")
        // .allowlist_var("Spec_.*")
        // .allowlist_type("Spec_.*")
        // Block everything we don't need or define ourselves.
        // .blocklist_type("Hacl_Streaming_.*")
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

fn copy_files(home_path: &Path, out_path: &Path) {
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    fs_extra::dir::copy(home_path.join("c"), out_path, &options).unwrap();
}

fn compile_files(files: &[String], out_path: &Path, args: &[String]) {
    let mut clang_args = includes(out_path);

    clang_args.push("-O3".to_string());
    clang_args.push("-c".to_string());
    clang_args.extend_from_slice(args);

    let mut build_cmd = Command::new("clang");
    let mut build_args = clang_args;
    build_args.extend_from_slice(files);
    println!(" >>> {}", out_path.join("c").join("src").display());
    println!(" >>> {}", build_args.join(" "));
    build_cmd
        .current_dir(out_path.join("c").join("src"))
        .args(&build_args);
    println!(" >>> build_cmd: {:?}", build_cmd);
    println!("     current dir: {:?}", build_cmd.get_current_dir());
    let build_status = build_cmd.status().expect("Failed to run build.");
    println!(" >>> build status: {:?}", build_status);
    println!(" >>> out {:?}", out_path);
    assert!(build_status.success());
}

fn build_chacha20poly1305(out_path: &Path) {
    let files = vec![
        "Hacl_Chacha20.c".to_string(),
        "Hacl_Chacha20Poly1305_32.c".to_string(),
        "Hacl_Poly1305_32.c".to_string(),
    ];
    let mut all_files = files.clone();

    // Platform detection
    if cfg!(simd128) {
        let files128 = vec![
            format!("Hacl_Chacha20Poly1305_128.c"),
            format!("Hacl_Chacha20_Vec128.c"),
            format!("Hacl_Poly1305_128.c"),
        ];
        all_files.extend_from_slice(&files128);

        let mut simd128_flags = vec![];
        append_simd128_flags(&mut simd128_flags);
        compile_files(&files128, out_path, &simd128_flags);
    }
    if cfg!(simd256) {
        let files256 = vec![
            "Hacl_Chacha20Poly1305_256.c".to_string(),
            "Hacl_Chacha20_Vec256.c".to_string(),
            "Hacl_Poly1305_256.c".to_string(),
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
        .current_dir(out_path.join("c").join("src"))
        .args(&[
            "-r",
            &out_path.join("libchacha20poly1305.a").display().to_string(),
        ])
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

    // Moving C library to output to make build easier.
    copy_files(home_path, out_path);
    eprintln!(" >>> out {:?}", out_path);

    // Build the C files
    build_chacha20poly1305(out_path);

    // Set library name to look up
    let library_name = "chacha20poly1305";

    // Set re-run trigger for all of c
    println!("cargo:rerun-if-changed=c");

    // Generate new bindings. This is a no-op on Windows.
    create_bindings(home_path);

    // Link hacl library.
    let mode = "static";
    println!("cargo:rustc-link-lib={}={}", mode, library_name);
    println!("cargo:rustc-link-search=native={}", out_path.display());
    println!("cargo:lib={}", out_path.display());
}
