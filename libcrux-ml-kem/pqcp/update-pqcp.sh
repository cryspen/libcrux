#!/usr/bin/env bash
#
# This script copies files to be included in the `mlkem-rust-libcrux`
# crate for the PQ code package. Files and directories to be copied
# are listed, one per line, in a file at `ALLOWLIST` and copied to the
# PQCP submodule. The copied files include a custom .gitignore file
# for mlkem-rust-libcrux. On successful completion of `cargo test`, a
# signed-off commit is created in the target repository.

set -e
set -o pipefail

if [ -z "$(which pip)" ]
then
    echo "Error: Python (>= 3.7) required to run this script."
fi

if [ -z "$(pip list | grep tomlkit)" ]
then
    echo "Error: Pythong package tomlkit required to run this script."
    echo "To install it using pip, run"
    echo ""
    echo "    pip install tomlkit"
    echo ""
    exit 1
fi

libcrux_root="$(git rev-parse --show-toplevel)"
libcrux_ml_kem_crate="$libcrux_root/libcrux-ml-kem"
allowlist="$libcrux_ml_kem_crate/pqcp/allowlist.txt"
pqcp_repo="$libcrux_ml_kem_crate/pqcp/repo"

cd "$libcrux_ml_kem_crate"
while read -r item; do
    cp -r "$item" "$pqcp_repo"
done < "$allowlist"

python "$libcrux_ml_kem_crate/pqcp/cargo.py" "$libcrux_root"

cd "$pqcp_repo"
cargo test
cargo clean

message="$(printf "mlkem-rust-libcrux PQ code packages update\n\n$(date): libcrux revision $(git -C $libcrux_root rev-parse HEAD)")"
git switch -c "libcrux-ml-kem-$(git -C $libcrux_root rev-parse HEAD)"
git add .
git commit -sm "$message"
