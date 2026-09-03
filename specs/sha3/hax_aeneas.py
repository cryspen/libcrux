#!/usr/bin/env python3

import subprocess
import re
import sys
from pathlib import Path

import os

HAX_VERSION = "cbce2c3bfcf50e853d3115c45cd592004d7d092f"
AENEAS_VERSION = "6852e64"


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
