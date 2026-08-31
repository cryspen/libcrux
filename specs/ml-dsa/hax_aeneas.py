#!/usr/bin/env python3

import subprocess
import re
import sys
from pathlib import Path

import os

HAX_VERSION = "4c9e2b7c75ab1e2b645a4a8361ae86c4504f9800"
AENEAS_VERSION = "f8a0eb8"


def check_version(cmd: list[str], name: str, expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        print(f"Version mismatch for {name}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], "hax", HAX_VERSION)
# As of cargo-hax 0.4, aeneas and charon are downloaded and checksum-verified
# by cargo-hax itself into a machine-wide cache and are not put on PATH, so
# ask cargo-hax which version the project resolves to instead of running the
# binary. `cargo hax tools install` fetches them if they are missing.
check_version(["cargo", "hax", "tools", "show"], "aeneas", AENEAS_VERSION)

result = subprocess.run(
    ["cargo", "hax", "into", "lean"],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"}
)
if result.returncode != 0:
    print(f"warning: hax/aeneas exited with code {result.returncode}; "
          f"continuing with post-processing.", file=sys.stderr)

# Post-process the generated Funs.lean for hax-lean v0.2.0 gaps (mirrors ml-kem).
funs_lean = Path("proofs/lean/HacspecMlDsa/Extraction/Funs.lean")
content = funs_lean.read_text()

# 1. `core.cmp.PartialEq` has no `ne` field in hax-lean v0.2.0 (it is a default
#    method, not a struct field). Drop the generated `ne := …default …` field.
content = re.sub(
    r"\n[ \t]*ne := core\.cmp\.PartialEq\.ne\.default\n[ \t]*[^\n]+\n(\s*})",
    r"\n\1", content)

# 2. Inside `matrix.matrix_vector_ntt` the `matrix` parameter shadows the
#    `matrix` sub-namespace, so the closure-instance reference passed to
#    `createi` fails to resolve. Force top-level resolution with `_root_.`.
for _fn in ("matrix_vector_ntt",):
    content = content.replace(
        f"(matrix.{_fn}.closure",
        f"(_root_.hacspec_ml_dsa.matrix.{_fn}.closure")

funs_lean.write_text(content)
