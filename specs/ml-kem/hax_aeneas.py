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

# Post-process the generated Funs.lean for hax-lean v0.2.0 gaps.
funs_lean = Path("proofs/lean/HacspecMlKem/Extraction/Funs.lean")
content = funs_lean.read_text()

# 1. Drop the `core.fmt.{Display,Arguments}` panic-formatting machinery before
#    each `fail panic` (hax-lean v0.2.0 does not model it). Leaves `fail panic`.
content = re.sub(
    r"[ \t]*let a ←\n[ \t]*core\.fmt\.rt\.Argument\.new_display.*?"
    r"\(Array\.make \d+#usize \[ a[^\]]*\]\)\n",
    "", content, flags=re.DOTALL)

# NOTE: a pass here used to strip the generated `ne := core.cmp.PartialEq.ne.default`
# field, because hax-lean v0.2.0 had no `ne` field on `core.cmp.PartialEq` (it was a
# default method). v0.3.12 does have it, so stripping it now breaks the extraction
# with "Fields missing: `ne`". Removed.

# 3. Inside `matrix.{multiply_matrix_by_column,transpose}` the `matrix` parameter
#    shadows the `matrix` sub-namespace, so the closure-instance reference passed
#    to `createi` fails to resolve. Force top-level resolution with `_root_.`.
for _fn in ("multiply_matrix_by_column", "transpose"):
    content = content.replace(
        f"(matrix.{_fn}.closure",
        f"(_root_.hacspec_ml_kem.matrix.{_fn}.closure")


# 4. aeneas emits `PartialEq`'s `ne := ...default` field but not `PartialOrd`'s
#    `lt`/`le`/`gt`/`ge`, so every generated `core.cmp.PartialOrd` record literal
#    is rejected with "Fields missing: `lt`, `le`, `gt`, `ge`". Fill them in with
#    the CoreModels defaults, self-referentially, exactly as CoreModels does for
#    its own instances (`impl_def` permits the self-reference).
def _complete_partial_ord(text: str) -> str:
    """Fill in the `lt`/`le`/`gt`/`ge` fields aeneas omits from `PartialOrd` records.

    Anchors on the record's type line (`core.cmp.PartialOrd ... := {`), walks back
    to the declaration it belongs to, and appends the four CoreModels defaults
    applied to that declaration -- the idiom CoreModels itself uses. The
    self-reference needs `impl_def`, which aeneas only emits when it fills the
    fields in itself, so the `def` is promoted.
    """
    lines = text.split("\n")
    TYPE = re.compile(r"^\s+core\.cmp\.PartialOrd\b.*:= \{$")
    DECL = re.compile(r"^(impl_def|def) (\S+)")
    for t, line in enumerate(lines):
        if not TYPE.match(line):
            continue
        d = next((k for k in range(t - 1, max(t - 4, -1), -1) if DECL.match(lines[k])), None)
        if d is None:
            continue
        name = DECL.match(lines[d]).group(2)
        close = next((k for k in range(t + 1, min(t + 40, len(lines))) if lines[k] == "}"), None)
        if close is None or any(l.startswith("  lt :=") for l in lines[t + 1:close]):
            continue
        fields = []
        for f in ("lt", "le", "gt", "ge"):
            fields += [f"  {f} := core.cmp.PartialOrd.{f}.default", f"    {name}"]
        lines[close:close] = fields
        lines[d] = re.sub(r"^def ", "impl_def ", lines[d])
    return "\n".join(lines)

content = _complete_partial_ord(content)

funs_lean.write_text(content)
