#!/bin/bash

set -e

mkdir -p kyber-crate/src
cp -r src/kem/kyber* kyber-crate/src
cd kyber-crate
mv src/kyber.rs src/lib.rs
mv src/kyber/* src

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
libcrux ={ path = "../" }
EOF

for file in src/*; do 
    if [ -f "$file" ]; then 
        echo "fixing up $file ..."
        sed -i 's/pub(in .*)/pub(crate)/g' $file
        sed -i 's/pub(super)/pub(crate)/g' $file
        sed -i 's/crate::/libcrux::/g' $file
    fi 
done

cargo build
