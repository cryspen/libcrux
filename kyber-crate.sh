#!/bin/bash

set -e

mkdir -p kyber-crate/src
cp -r src/kem/kyber* kyber-crate/src
cd kyber-crate
mv src/kyber.rs src/lib.rs
mv src/kyber/* src

SED=$(which gsed &>/dev/null && echo gsed || echo sed)

cat > Cargo.toml <<EOF
[package]
name = "libcrux_kyber"
version = "0.1.0"
authors = ["Cryspen"]
edition = "2021"

[workspace]
members = ["."]

[dependencies]
hax-lib = { git = "https://github.com/hacspec/hax/", branch = "main" }
libcrux = { path = "../" }
libcrux-platform = { path = "../sys/platform" }
hex = { version = "0.4.3", features = ["serde"] }

[dev-dependencies]
serde_json = { version = "1.0" }
serde = { version = "1.0", features = ["derive"] }
rand = { version = "0.8" }
EOF

for file in src/*; do 
    if [ -f "$file" ]; then 
        echo "fixing up $file ..."
        $SED -i 's/pub(in .*)/pub(crate)/g' $file
        $SED -i 's/pub(super)/pub(crate)/g' $file
        $SED -i 's/crate::/libcrux::/g' $file
    fi 
done

mkdir -p tests
cp -r ../kyber-crate-tests/* tests/

# Build & test
cargo test

# Extract
CHARON_HOME=${CHARON_HOME:-~/repos/charon/}
EURYDICE_HOME=${EURYDICE_HOME:-~/repos/eurydice/}
$CHARON_HOME/bin/charon --errors-as-warnings
mkdir c
cd c
$EURYDICE_HOME/eurydice ../libcrux_kyber.llbc
cp $EURYDICE_HOME/include/eurydice_glue.h .
