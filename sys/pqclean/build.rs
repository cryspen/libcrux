use std::{env, path::Path};

fn copy_files(home_path: &Path, out_path: &Path) {
    let mut options = fs_extra::dir::CopyOptions::new();
    options.overwrite = true;
    fs_extra::dir::copy(home_path.join("c"), out_path, &options).unwrap();
}

#[cfg(not(windows))]
fn create_bindings(home_dir: &Path) {
    let c_dir = home_dir.join("c");
    let clang_args = vec![format!("-I{}", c_dir.display())];

    let bindings = bindgen::Builder::default()
        // Header to wrap headers
        .header("c/fips202.h")
        // Set include paths for headers
        .clang_args(clang_args)
        // Include the things we want
        .allowlist_function("shake.*")
        .allowlist_function("sha3.*")
        .allowlist_type("sha3.*")
        .allowlist_type("shake.*")
        .allowlist_type("SHAKE.*")
        .allowlist_type("SHA3.*")
        .allowlist_var("SHAKE.*")
        .allowlist_var("SHA3.*")
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
fn create_bindings(_: &Path) {}

fn compile_files(library_name: &str, files: &[String], out_path: &Path, args: &[String]) {
    let c_dir = out_path.join("c");

    let mut build = cc::Build::new();
    build
        .files(files.iter().map(|fname| c_dir.join(fname)))
        .warnings_into_errors(true)
        .no_default_flags(true);

    build.include(c_dir.join("include"));
    build.opt_level(3);
    for arg in args {
        build.flag(arg);
    }

    build.compile(library_name);
}

fn build(out_path: &Path) {
    let files = vec!["fips202.c".to_string()];
    let args = vec![];
    compile_files("pqclean", &files, out_path, &args);
}

pub fn main() {
    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);
    let out_dir = env::var("OUT_DIR").unwrap();
    let out_path = Path::new(&out_dir);

    // Moving C/ASM code to output to make build easier.
    copy_files(home_path, out_path);

    // Build the C/ASM files
    build(out_path);

    // Set re-run trigger for all of s
    println!("cargo:rerun-if-changed=c");

    // Generate new bindings. This is a no-op on Windows.
    create_bindings(home_path);
}
