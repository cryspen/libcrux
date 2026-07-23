#!/usr/bin/env python3
"""Proof-annotation placement lint (see PROOF_CONVENTIONS.md).

Checks the hax-verified crates for convention violations:

  V1  A multi-line F* *definition* block (containing `val`/`let`/`Lemma`)
      inside a `#[hax_lib::fstar::before/after(...)]` attribute, without a
      `proof-residence:` exception tag on a comment line directly above the
      attribute. Named theory belongs in `proofs/fstar/spec/` companions.

Modes:
  report (default)  print violations, always exit 0 — for the migration period.
  --strict          exit 1 on any violation — for CI, once the sweep completes.
"""
import os
import re
import sys

CRATES = ["libcrux-ml-kem/src", "libcrux-ml-dsa/src"]
BA_RX = re.compile(
    r"#\[\s*(?:cfg_attr\s*\(\s*hax\s*,\s*)?hax_lib::fstar::(before|after)\s*\("
)
DEF_RX = re.compile(r"\blet\b|\bval\b|\bLemma\b")
TAG_RX = re.compile(
    r"proof-residence:\s*(locked|hint-keystone|cold-gate|spec-host|clean-context)"
)


def raw_string_body(text, start, cap=30000):
    seg = text[start : start + cap]
    # Only accept a string that is the attribute's own argument (directly after
    # its opening paren) — a plain-string attr like before("open Foo") must not
    # match the NEXT raw string in the file (bogus-block false positive).
    m = re.match(r'[^(]*\(\s*r(#+)"(.*?)"\1', seg, re.S)
    if m:
        return m.group(2)
    m = re.match(r'[^(]*\(\s*"((?:[^"\\]|\\.)*)"', seg, re.S)
    return m.group(1) if m else ""


def check_file(path, repo_root):
    text = open(path).read()
    line_start = [0]
    for line in text.split("\n"):
        line_start.append(line_start[-1] + len(line) + 1)
    violations = []
    for m in BA_RX.finditer(text):
        head = text[m.start() : m.start() + 120].split("r#")[0]
        body = raw_string_body(text, m.start())
        n_lines = body.count("\n") + 1
        if n_lines <= 2 or not DEF_RX.search(body):
            continue  # one-line directives / non-definition text are fine
        if "interface" in head:
            continue  # hax-required interface injection
        # look for a tag in the 3 lines above the attribute
        import bisect

        lineno = bisect.bisect_right(line_start, m.start()) - 1
        context = "\n".join(text.split("\n")[max(0, lineno - 3) : lineno])
        if TAG_RX.search(context):
            continue
        violations.append(
            (os.path.relpath(path, repo_root), lineno + 1, n_lines)
        )
    return violations


def main():
    strict = "--strict" in sys.argv
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    all_violations = []
    for crate in CRATES:
        for dirpath, _, files in os.walk(os.path.join(repo_root, crate)):
            for f in sorted(files):
                if f.endswith(".rs"):
                    all_violations += check_file(
                        os.path.join(dirpath, f), repo_root
                    )
    if all_violations:
        print(
            f"{len(all_violations)} untagged multi-line definition block(s) "
            "in before/after attributes (see PROOF_CONVENTIONS.md):"
        )
        for path, line, n in sorted(all_violations):
            print(f"  {path}:{line}  ({n} lines)")
    else:
        print("annotation lint: clean")
    sys.exit(1 if strict and all_violations else 0)


if __name__ == "__main__":
    main()
