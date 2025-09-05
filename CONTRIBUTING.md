# Contributing

Third-party contributions to libcrux are welcome, be it in the form of an issue
report or a feature request via [issues](https://github.com/cryspen/libcrux)
or in the form of new code and documentation via [pull requests](https://github.com/cryspen/libcrux/pulls).

### Coding style

In order to help contributors adhere to the style guidelines of this project,
we've provided a [Python3 script](git-hooks/pre-commit.py) that serves as a Git pre-commit hook.

In addition to Python3, you will also need to install [rustfmt](https://github.com/rust-lang/rustfmt) and the [black](https://github.com/psf/black) formatter to use this hook. Once they're installed, simply
run `./git-hooks/setup.py` in the project root directory.

### Working with Proofs

Most of the code in libcrux is formally verified (each crate marks its verification status at the top of its Readme file).

Some of the crates contain Rust code generated from the [HACL* project](https://hacl-star.github.io).
Modifications to this code would mean that the proofs in HACL* no longer apply, so for modifications to this code,
get in touch with the libcrux or HACL* maintainers.

Other crates (specifically `libcrux-ml-kem` and `libcrux-ml-dsa`) are verified using [hax](https://cryspen.com/hax) and  [F\*](https://fstar-lang.org).
To re-run proofs on these crates, follow the instructions in their Readme files.
These proofs depend on specific versions of the `hax` binary, the `hax-lib` proof and annotations library, and the `fstar` proof assistant.

The version of `hax` is set globally for the `libcrux` workspace via the `hax-lib` Cargo dependency.
The developer is expected to install the `hax` binary at the same version as `hax-lib` by cloning the [hax repository](https://github.com/hacspec/hax),
checking out the revision corresponding to the `hax-lib` version release, and running `./setup.sh` as documented in the hax Readme.

We use the same version throughout libcrux, and inconsistencies can lead to verification or build failures (see e.g. [issue #1125](https://github.com/cryspen/libcrux/issues/1125)).
The F\*  proofs use a [Makefile](./fstar-helpers/Makefile.generic), which relies on Cargo and the workspace's version of `hax-lib` to locate F\* libraries.
Specifically, those under the [`proof-libs` directory in hax-lib](https://github.com/cryspen/hax/tree/main/hax-lib/proof-libs).

If you need to work with a specific version of `hax-lib` or `proof-libs`, update the `hax-lib` dependency in the workspace's `Cargo.toml`.  
You may use a [path dependency](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#specifying-path-dependencies), or a [Git dependency](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#specifying-dependencies-from-git-repositories) for development purposes.
If your pull request includes such a non-default dependency (e.g., a Git or path-based reference), **please mention it clearly in the PR description**.
Using a non-[crates.io](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#specifying-dependencies-from-cratesio) dependency in a PR is acceptable for development. However, **before merging**, the dependency must be updated to point to a released version of `hax`.
If a new `hax` release is required for your PR to be merged, please [open an issue on the hax repository](https://github.com/cryspen/hax/issues/new?title=Release%20request&body=For%20libcrux%20PR%20%23XX,%20I%20need%20a%20release%20of%20hax.) to request it.
