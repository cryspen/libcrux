# Release


## Crates

Main crate: `libcrux`

Crates that can be used directly
- blake2
- sha2
- sha3
- ml-dsa
- ml-kem
- chacha20poly1305
- hkdf
- hmac
- curve25519
- ecdsa
- ed25519
- rsa

Additional protocols
- psq

Higher level crates
- ecdh
- kem

### Utility crates

- hacl-rs
- traits
- macros
- poly1305
- p256

### Other libraries

- sys/libjade

### Legacy

- sys/hacl

### Independently Versioned

- blake2

## Release Order

This snippet prints a valid publishing order of the crates in the workspace:

```
cargo depgraph --workspace-only --all-deps |
  gvpr 'E { string tl = gsub($.tail.label, " ", "-"), hl = gsub($.head.label, " ", "-"); printf("%s %s\n", hl, tl); }' |
  tsort
```

> [!NOTE]
> <details><summary>Explanation</summary>
>
>   - `cargo depgraph --workspace-only --all-deps` generates a graph of all dependencies of crates in the workspace in the graphviz dot format
>   - the `gvpr` script translates the graph into a representation that `tsort` can handle
>      - i.e. lines of "$dependency $dependent" - we want the dependencies to come before
>   - `tsort` performs topological sorting
>
> Requires [cargo-depgraph] and [graphviz] to be installed. On Linux you probably want to install graphviz through your distribution.
>
> [cargo-depgraph]: https://github.com/jplatte/cargo-depgraph
> [graphviz]: https://graphviz.org/download/
>
> </details>

## Releasing a Crate

### Update Version

#### Version Scheme

Initially, all crate versions in this repository were in sync, but we moved away
from that model. Now, a crate _may_ follow the workspace version, but is not
required to.

We use semantic versioning. So far, all version parts except PATCH are 0. Before
releasing `0.0.X`, we release `0.0.X-pre.Y`, starting with `0.0.X-pre.1`. Only
once we released all crates in the workspace we move on to publish the real
version.


It is most robust to update versions manually. We experimented with using
`cargo-release`, but its behaviour around bumping workspace versions makes it a
bit less useful in our context.

### Update Dependent Crates

If there are crates that depend on this crate, bump the dependency in them and
later update these as well.

### Running `cargo publish`

This pushes the crate to crates.io. Before running the full push, do a dry run.
