#!/usr/bin/env python3

import subprocess
import re
import sys
from pathlib import Path

HAX_VERSION = "7b4bd97058e0fcbf9135b76297ca91942f2327a6"
AENEAS_VERSION = "863909af"


def check_version(cmd: list[str], expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        print(f"Version mismatch for {cmd[0]}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], HAX_VERSION)
check_version(["aeneas", "-version"], AENEAS_VERSION)

subprocess.run(
    ["cargo", "hax", "into", "aeneas-lean"],
    env={**__import__("os").environ, "RUSTFLAGS": "--cfg charon"},
    check=True,
)

funs_lean = Path("proofs/aeneas-lean/HacspecSha3/Extraction/Funs.lean")
content = funs_lean.read_text()
content = re.sub(
    r"import Aeneas",
    "import Aeneas\nimport HacspecSha3.Missing\nopen core_models",
    content,
)

# https://github.com/AeneasVerif/aeneas/issues/984
content = re.sub(
    r"(/-- \[hacspec_sha3::keccak_f::theta\]:)",
    "set_option Aeneas.customDoElab false in\n\\1",
    content,
)
funs_lean.write_text(content)
