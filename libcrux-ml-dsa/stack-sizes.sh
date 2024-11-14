#!/bin/bash

# This script runs `cargo stack-sizes` to obtain stack frame sizes for
# functions in the crate. 

set -euo pipefail

FRAME_SIZE_LIMIT=25344

function setup {
    cargo install stack-sizes@=0.4
    
    if [ -f "./rust-toolchain.toml" ]; then
        if [ -f "./rust-toolchain.toml.bak" ]; then
            echo "Error: An old rust-toolchain.toml.bak was found."
        fi
        mv "./rust-toolchain.toml" "./rust-toolchain.toml.bak"
    fi
    {
        echo "[toolchain]"
        echo "channel = \"nightly\""
        echo "profile = \"minimal\""
    } >> "./rust-toolchain.toml"

    if [ -f "./Cargo.toml" ]; then
        if [ -f "./Cargo.toml.bak" ]; then
            echo "Error: An old Cargo.toml.bak was found."
        fi
        cp "./Cargo.toml" "./Cargo.toml.bak"
    fi

    if [ -f "./Cargo.lock" ]; then
        if [ -f "./Cargo.lock.bak" ]; then
            echo "Error: An old Cargo.lock.bak was found."
        fi
        cp "./Cargo.lock" "./Cargo.lock.bak"
    fi

    sed -i -e 's/version.workspace.*/version = "0.0.0"/g' "./Cargo.toml"
}

function teardown {
    if [ -f "./rust-toolchain.toml.bak" ]; then
        mv "./rust-toolchain.toml.bak" "./rust-toolchain.toml"
    else
        rm "./rust-toolchain.toml"
    fi

    if [ -f "./Cargo.toml.bak" ]; then
        mv "./Cargo.toml.bak" "./Cargo.toml"
    fi

    if [ -f "./Cargo.lock.bak" ]; then
        mv "./Cargo.lock.bak" "./Cargo.lock"
    fi
    
    cargo uninstall stack-sizes
}

trap teardown EXIT

setup;

function largest_stack_frame {
    RUSTFLAGS="-C embed-bitcode=yes"
    FRAME_SIZES="$(cargo stack-sizes --release --example $1 | sort -g -k 2)"

    echo "(% STACK FRAME SIZES %)"
    echo "$FRAME_SIZES"
    echo "(% -------END------- %)"
    
    MAX_FRAME_SIZE=$(echo "$FRAME_SIZES" | tail -n 1 | awk '{print $2}')
    MAX_FRAME_NAME=$(echo "$FRAME_SIZES" | tail -n 1 | awk '{print $3}')


    if (( MAX_FRAME_SIZE > FRAME_SIZE_LIMIT)); then
        echo ""
        echo "Function $MAX_FRAME_NAME is above the limit:"
        echo "Limit:         $FRAME_SIZE_LIMIT"
        echo "Frame Size:    $MAX_FRAME_SIZE"
        echo ""
        exit 1
    else
        echo ""
        echo "All functions below stack frame limit"
        echo ""
    fi
}

largest_stack_frame $1;

