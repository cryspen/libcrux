# Using `cargo stack-sizes`

The current version of the tool only supports use as a library, so we
need to `cargo install stack-sizes@=0.4` instead.

The tool does not properly understand workspace packages it seems, so
we have to replace `package.version.workspace = true` in `Cargo.toml`
with `package.version`"0.0.2-beta.2"= or whatever the appropriate
version is.

The tool relies on the nightly feature `-Zemit-stack-sizes`, so we
need the nightly toolchain, e.g. by putting `rust-toolchain.toml` file
in the crate root, containing the following:

    [toolchain]
    channel = "nightly"
    profile = "minimal"

To run the tool on an example, then, invoke it like so:

    RUSTFLAGS="-C embed-bitcode=yes" cargo stack-sizes --release --example sign_65 | sort -g -k 2

This prints out the functions it found ordered by their stack
sizes. (Also try without `--release`).

