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

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn simd128_support() -> bool {
    std::arch::is_x86_feature_detected!("sse2")
        && std::arch::is_x86_feature_detected!("sse3")
        && std::arch::is_x86_feature_detected!("sse4.1")
        && std::arch::is_x86_feature_detected!("avx")
}

#[cfg(target_arch = "aarch64")]
fn simd128_support() -> bool {
    true
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
fn simd128_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn simd256_support() -> bool {
    simd128_support() && std::arch::is_x86_feature_detected!("avx2")
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn simd256_support() -> bool {
    // XXX: Check for z14 or z15
    false
}

#[cfg(not(windows))]
fn create_bindings(home_dir: &Path) {
    let mut clang_args = includes(home_dir);
    // Platform detection
    if simd128_support() {
        clang_args.push("-DSIMD128".to_string());
    }
    if simd256_support() {
        clang_args.push("-DSIMD256".to_string());
    }

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

// const CFLAGS: &'static str = "-c";
// const DEBUG_CFLAGS: &'static str = "-g";
// const RELEASE_CFLAGS: &'static str = "-O3";
// const OUTPUT_FLAGS: &'static str = "-o chacha20poly1305_32.o";

fn copy_files(home_path: &Path, out_path: &Path) {
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    fs_extra::dir::copy(home_path.join("c"), out_path, &options).unwrap();
}

fn compile_files(files: &[String], out_path: &Path) {
    let mut clang_args = includes(out_path);
    // Platform detection
    if simd128_support() {
        clang_args.push("-DSIMD128".to_string());
    }
    if simd256_support() {
        clang_args.push("-DSIMD256".to_string());
    }
    clang_args.push("-O3".to_string());
    clang_args.push("-c".to_string());

    // let object_file = out_path.join(file).with_extension("o");
    let mut build_cmd = Command::new("clang");
    let mut build_args = clang_args;
    // vec![
    //     CFLAGS.to_string(),
    //     RELEASE_CFLAGS.to_string(),
    //     // "-o".to_string(),
    //     // object_file.to_str().unwrap().to_string(),
    // ];
    // build_args.append(&mut clang_args);
    // build_args.append(&mut includes(out_path));
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
    let mut files = vec![
        "Hacl_Chacha20.c",
        "Hacl_Chacha20Poly1305_32.c",
        "Hacl_Poly1305_32.c",
    ];
    // Platform detection
    if simd128_support() {
        files.append(&mut vec![
            "Hacl_Chacha20Poly1305_128.c",
            "Hacl_Chacha20_Vec128.c",
            "Hacl_Poly1305_128.c",
        ]);
    }
    if simd256_support() {
        files.append(&mut vec![
            "Hacl_Chacha20Poly1305_256.c",
            "Hacl_Chacha20_Vec256.c",
            "Hacl_Poly1305_256.c",
        ]);
    }

    let mut object_files = vec![];
    let files: Vec<String> = files.drain(..).map(|f| f.to_string()).collect();
    compile_files(&files, out_path);
    for file in files {
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
