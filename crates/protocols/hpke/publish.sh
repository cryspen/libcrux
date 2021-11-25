#!/bin/bash
# Helper to publish all crates in this repository.

set -e

# "hpke-rs-crypto
cd traits && cargo publish $@ && cd -

# hpke-rs
cargo publish $@

# hpke-rs-evercrypt
cd evercrypt_provider && cargo publish $@ && cd -

# hpke-rs-rust-crypto
cd rust_crypto_provider && cargo publish $@ && cd -
