#!/usr/bin/env bash
# Simple script to run all the tests.

set -euo pipefail

cwd="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$cwd" || { echo "Failed to navigate to $cwd"; exit 1; }

test_dir="./build/Debug"

tests=(
    "ml_dsa_test44"
    "ml_dsa_test87"
    "ml_kem_test512"
    "sha3_test"
    "ml_dsa_test65"
    "ml_kem_test1024"
    "ml_kem_test768"
)

for bin in "${tests[@]}"; do
    # Combine prefix directory and binary name
    full_path="${test_dir}/${bin}"

    # Verify executable existence
    if [ -x "$full_path" ] || command -v "$full_path" &> /dev/null; then
        echo "Executing..."
        "$full_path"
        echo "Successfully finished ${bin}"
    else
        echo "Error: '${full_path}' not found or lacks execute permissions (+x)." >&2
    fi

    echo "--------------------------------------------------"
done
 