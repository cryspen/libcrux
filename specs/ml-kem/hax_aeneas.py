#!/usr/bin/env python3

import subprocess
import re
import sys
from pathlib import Path

import os

HAX_VERSION = "2fedcb2b196f5adea55975d0a023596ec6383ff2"
AENEAS_VERSION = "52fd438"


def check_version(cmd: list[str], name: str, expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        print(f"Version mismatch for {name}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], "hax", HAX_VERSION)
check_version(["aeneas", "-version"], "aeneas", AENEAS_VERSION)

result = subprocess.run(
    ["cargo", "hax", "into", "lean"],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"}
)
if result.returncode != 0:
    print(f"warning: hax/aeneas exited with code {result.returncode}; "
          f"continuing with post-processing.", file=sys.stderr)

# Post-process the generated Funs.lean for hax-lean v0.2.0 gaps.
funs_lean = Path("proofs/lean/HacspecMlKem/Extraction/Funs.lean")
content = funs_lean.read_text()

# 1. Drop the `core.fmt.{Display,Arguments}` panic-formatting machinery before
#    each `fail panic` (hax-lean v0.2.0 does not model it). Leaves `fail panic`.
content = re.sub(
    r"[ \t]*let a ←\n[ \t]*core\.fmt\.rt\.Argument\.new_display.*?"
    r"\(Array\.make \d+#usize \[ a[^\]]*\]\)\n",
    "", content, flags=re.DOTALL)

# 2. `core.cmp.PartialEq` has no `ne` field in hax-lean v0.2.0 (it is a default
#    method, not a struct field). Drop the generated `ne := …default …` field.
content = re.sub(
    r"\n[ \t]*ne := core\.cmp\.PartialEq\.ne\.default\n[ \t]*[^\n]+\n(\s*})",
    r"\n\1", content)

# 3. Inside `matrix.{multiply_matrix_by_column,transpose}` the `matrix` parameter
#    shadows the `matrix` sub-namespace, so the closure-instance reference passed
#    to `createi` fails to resolve. Force top-level resolution with `_root_.`.
for _fn in ("multiply_matrix_by_column", "transpose"):
    content = content.replace(
        f"(matrix.{_fn}.closure",
        f"(_root_.hacspec_ml_kem.matrix.{_fn}.closure")

funs_lean.write_text(content)
