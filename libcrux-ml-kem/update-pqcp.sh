#!/usr/bin/env bash
#
# This script copies files to be included in the `mlkem-rust-libcrux`
# crate for the PQ code package. Files and directories to be copied
# are listed, one per line, in a file at `ALLOWLIST` and copied to
# `TARGET_DIR`, which should be the `mlkem-rust-libcrux` git
# repository. The copied files include custom Cargo.toml and
# .gitignore files for mlkem-rust-libcrux. On successful completion of
# `cargo test`, a signed-off commit is created in the target
# repository.

set -e
set -o pipefail

ALLOWLIST="pqcp/allowlist.txt"
LIBCRUX_HOME="$(pwd)"

if [[ -z "$TARGET_DIRECTORY" ]]; then
    echo "Please set TARGET_DIRECTORY to the libcrux-ml-kem PQ code packages repository"
    exit 1
fi

while read -r item; do
    cp -r "$item" "$TARGET_DIRECTORY"
done < "$ALLOWLIST"

cd "$TARGET_DIRECTORY"
cargo test
cargo clean

git add .
git commit -sm "mlkem-rust-libcrux PQ code packages update ($(date)) - libcrux revision $(git -C $LIBCRUX_HOME rev-parse HEAD)"
