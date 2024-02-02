#!/bin/bash

set -e

mkdir -p kyber-crate/src
cp -r src/kem/kyber* kyber-crate/src
cp src/hax_utils.rs kyber-crate/src/hax_utils.rs
cd kyber-crate
mv src/kyber.rs src/lib.rs
mv src/kyber/* src

SED=$(which gsed &>/dev/null && echo gsed || echo sed)

cat >Cargo.toml <<EOF
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
rand_core = { version = "0.6" }
EOF

# Fixup Rust for standalone crate
for file in src/*; do
    if [ -f "$file" ]; then
        echo "fixing up $file ..."
        $SED -i 's/pub(in .*)/pub(crate)/g' $file
        $SED -i 's/pub(super)/pub(crate)/g' $file
        $SED -i 's/crate::/libcrux::/g' $file
        $SED -i 's/libcrux::hax_utils/crate::hax_utils/g' $file
        $SED -i 's/kem::kyber/crate/g' $file
        $SED -i 's/pub mod kyber512;//g' $file
        $SED -i 's/pub mod kyber1024;//g' $file
    fi
done

$SED -i '1ipub(crate) mod hax_utils;' src/lib.rs

mkdir -p tests
cp -r ../kyber-crate-tests/* tests/
rm src/kyber512.rs
rm src/kyber1024.rs

# Build & test
cargo build

# Extract
if [[ -z "$CHARON_HOME" ]]; then
    echo "Please set CHARON_HOME to the Charon directory" 1>&2
    exit 1
fi
if [[ -z "$EURYDICE_HOME" ]]; then
    echo "Please set EURYDICE_HOME to the Eurydice directory" 1>&2
    exit 1
fi
if [[ -z "$HACL_PACKAGES_HOME" ]]; then
    echo "Please set HACL_PACKAGES_HOME to the hacl-packages directory" 1>&2
    exit 1
fi

echo "Running charon ..."
$CHARON_HOME/bin/charon --errors-as-warnings
mkdir -p c
cd c

echo "Running eurydice ..."
$EURYDICE_HOME/eurydice ../libcrux_kyber.llbc
# Add header
$SED -i -z 's!\(#include "libcrux_kyber.h"\)!\1\n#include "libcrux_hacl_glue.h"!g' libcrux_kyber.c
# Drop definition
$SED -i -z 's!typedef struct __uint8_t_840size_t__uint8_t_840size_t__uint8_t_840size_t__uint8_t_840size_t__s.*__uint8_t_840size_t__uint8_t_840size_t__uint8_t_840size_t__uint8_t_840size_t_;!!g' libcrux_kyber.c
clang-format --style=Mozilla -i libcrux_kyber.c libcrux_kyber.h

cp $EURYDICE_HOME/include/eurydice_glue.h .
cp internal/*.h $HACL_PACKAGES_HOME/libcrux/include/internal/
cp *.h $HACL_PACKAGES_HOME/libcrux/include
cp *.c $HACL_PACKAGES_HOME/libcrux/src
