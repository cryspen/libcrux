# Contributing

Third-party contributions to libcrux are welcome, be it in the form of an issue
report or a feature request via [issues](https://github.com/cryspen/libcrux)
or in the form of new code and documentation via [pull requests](https://github.com/cryspen/libcrux/pulls).

## Repository Structure

### Crates

We are in the process of restructuring the directory structure of the repository.
While many old crates do not yet follow the new structure, please use it for new
crates:

```
/crates/                 -- contains all crates except `libcrux`
/crates/primitives       -- contains crypto primitive crates
/crates/primitives/aead  -- the crate `libcrux-aead`
/crates/algorithms       -- contains crypto algorithm crates
/crates/algorithms/chacha20poly1305 -- the crate `libcrux-chacha20poly1305`
/crates/specs/           -- specification crates
/crates/utils/           -- miscellaneous crates
/crates/utils/macros     -- the `libcrux-macros` crate
/crates/utils/secrets    -- the `libcrux-secrets` crate
/crates/utils/test-utils -- the `libcrux-test-utils` crate
/crates/sys/...          -- the sys crates
```

### Per-Crate Structure

#### Crate Metadata

**Readme:** Every crate has its own readme. Ensure that the Cargo.toml refers to
that instead of the one at the repo root.

**License:** Make sure the code is appropriately licensed, most likely with
Apache-2.0 and MIT.

#### Extracted C Code

Some crates contain scripts and configuration for extracting C code from the
Rust code, and possibly a pre-extracted C version of the crate.
Relative to the crate root, the structure we aim to use is:

```
/Cargo.toml -- we are at the crate root
/extracts/
/extracts/$name/extract.sh   -- the script that extracts the code
/extracts/$name/extract.yaml -- the eurydice config for the extraction
/extracts/$name/out/         -- the extracted code
/extracts/$name/...          -- per-extraction extra data
```

where `$name` identifies a C extraction in a particular configuration.

## Coding style

In order to help contributors adhere to the style guidelines of this project,
we've provided a [Python3 script](git-hooks/pre-commit.py) that serves as a Git pre-commit hook.

In addition to Python3, you will also need to install [rustfmt](https://github.com/rust-lang/rustfmt) and the [black](https://github.com/psf/black) formatter to use this hook. Once they're installed, simply
run `./git-hooks/setup.py` in the project root directory.
