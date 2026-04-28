#!/usr/bin/env bash
# After `cargo hax extract` (or `./hax.sh extract`), F* files in the
# various proofs/fstar/extraction/ trees get fresh mtime even when
# their content is unchanged.  Make then re-verifies every dependent
# .checked file — slow cascade for purely-cosmetic re-extractions
# (e.g. when the underlying Rust change only touches one trait method).
#
# This script runs in two modes:
#
#   ./touch-unchanged-checked.sh snapshot
#       — Pre-extract.  Records SHA-256 of every tracked F* file in
#         the configured trees to /tmp/<repo-name>-fstar-shas.txt.
#         Run BEFORE `./hax.sh extract`.
#
#   ./touch-unchanged-checked.sh skip-unchanged
#       — Post-extract.  Compares current SHA-256 of every F* file
#         against the snapshot.  For files whose SHA matches (i.e.,
#         content unchanged but mtime was bumped by `cargo hax`),
#         touches the corresponding .checked file in
#         <repo>/.fstar-cache/checked/ so make skips re-verification.
#         Run AFTER `./hax.sh extract`, BEFORE `./hax.sh prove`.
#
# Usage:
#   proofs/agent-status/touch-unchanged-checked.sh snapshot
#   ./hax.sh extract
#   proofs/agent-status/touch-unchanged-checked.sh skip-unchanged
#   ./hax.sh prove
#
# Safety: F*'s `--cache_checked_modules` validates by content hash
# stored inside the .checked file itself.  If the cached .checked is
# internally inconsistent (e.g. a transitive dependency actually
# changed), F* rebuilds the affected target on its own.  The worst
# case is a wasted touch.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
CHECKED_DIR="${REPO_ROOT}/.fstar-cache/checked"
SNAPSHOT_FILE="/tmp/$(basename "$REPO_ROOT")-fstar-shas.txt"

TREES=(
  "${REPO_ROOT}/libcrux-ml-dsa/proofs/fstar/extraction"
  "${REPO_ROOT}/libcrux-ml-kem/proofs/fstar/extraction"
  "${REPO_ROOT}/libcrux-ml-kem/proofs/fstar/spec"
  "${REPO_ROOT}/specs/ml-dsa/proofs/fstar/extraction"
  "${REPO_ROOT}/specs/ml-dsa/proofs/fstar/commute"
  "${REPO_ROOT}/specs/ml-kem/proofs/fstar/extraction"
  "${REPO_ROOT}/specs/sha3/proofs/fstar/extraction"
  "${REPO_ROOT}/crates/utils/core-models/proofs/fstar/extraction"
  "${REPO_ROOT}/crates/utils/intrinsics/proofs/fstar/extraction"
  "${REPO_ROOT}/crates/sys/platform/proofs/fstar/extraction"
  "${REPO_ROOT}/crates/algorithms/sha3/proofs/fstar/extraction"
  "${REPO_ROOT}/crates/algorithms/aesgcm/proofs/fstar/extraction"
  "${REPO_ROOT}/libcrux-intrinsics/proofs/fstar/extraction"
  "${REPO_ROOT}/fstar-helpers/fstar-bitvec"
)

# Find every .fst / .fsti file across the tracked trees and compute
# its SHA-256.  Output `<sha>  <abs_path>` per line.
all_fstar_shas() {
  for tree in "${TREES[@]}"; do
    [ -d "$tree" ] || continue
    for f in "$tree"/*.fst "$tree"/*.fsti; do
      [ -f "$f" ] || continue
      shasum -a 256 "$f"
    done
  done
}

cmd="${1:-skip-unchanged}"

case "$cmd" in
  snapshot)
    all_fstar_shas > "$SNAPSHOT_FILE"
    n=$(wc -l < "$SNAPSHOT_FILE" | tr -d '[:space:]')
    echo "snapshot: ${n} F* files saved to ${SNAPSHOT_FILE}"
    ;;
  skip-unchanged)
    if [ ! -f "$SNAPSHOT_FILE" ]; then
      echo "error: no snapshot at ${SNAPSHOT_FILE}; run \`$0 snapshot\` before \`./hax.sh extract\`" >&2
      exit 1
    fi
    if [ ! -d "$CHECKED_DIR" ]; then
      echo "error: no .fstar-cache/checked at ${CHECKED_DIR}" >&2
      exit 1
    fi

    touched=0
    changed=0
    nocache=0
    missing=0

    while IFS= read -r line; do
      old_sha="${line%% *}"
      old_path="${line#*  }"
      [ -f "$old_path" ] || { missing=$((missing + 1)); continue; }
      new_sha=$(shasum -a 256 "$old_path" | awk '{print $1}')
      if [ "$old_sha" = "$new_sha" ]; then
        # Content unchanged.  Touch the .checked file so make skips it.
        bn=$(basename "$old_path")
        checked="${CHECKED_DIR}/${bn}.checked"
        if [ -f "$checked" ]; then
          touch "$checked"
          touched=$((touched + 1))
        else
          nocache=$((nocache + 1))
        fi
      else
        changed=$((changed + 1))
      fi
    done < "$SNAPSHOT_FILE"

    echo "skip-unchanged: touched=${touched} content-changed=${changed} no-cache=${nocache} now-missing=${missing}"
    ;;
  *)
    echo "Usage: $0 {snapshot|skip-unchanged}" >&2
    exit 1
    ;;
esac
