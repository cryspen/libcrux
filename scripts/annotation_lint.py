#!/usr/bin/env python3
"""Proof-annotation placement + trust-marker lint (see PROOF_CONVENTIONS.md).

Checks the hax-verified crates for convention violations:

  V1  A multi-line F* *definition* block (containing `val`/`let`/`Lemma`)
      inside a `#[hax_lib::fstar::before/after(...)]` attribute, without a
      `proof-residence:` exception tag on a comment line directly above the
      attribute. Named theory belongs in `proofs/fstar/spec/` companions.

  V2  A trust reason that does not start with a valid category prefix
      (`hax-limitation:`, `pending-proof(<ref>):`, …). Covers both the G1 body
      wrappers (`trusted_admit!` / `trusted_assume!`) and the G2 whole-function
      attribute wrappers (`#[trusted(lax|panic_free|opaque|exclude, "reason")]`).

  V2b Fn-level inline-trust label sync (both directions): a fn whose body
      carries a `trusted_admit!` / `trusted_assume!` MUST also carry the
      matching-kind `#[libcrux_macros::trusted(inline-admit|inline-assume)]`
      summary label, and every such label must have a matching body macro.

  V3  A raw obligation-producing mechanism outside the trust wrappers —
      `proof!("admit ()")` / `proof!(assume …)` must be `trusted_admit!` /
      `trusted_assume!` so the trust surface is declared, not laundered.

  V4  A hand-written companion AXIOM (an F* obligation in a git-tracked
      `proofs/fstar/spec/` module) without exactly one `[@@ "trusted: <cat>:
      <reason>"]` tag, or a tag whose reason lacks a valid category prefix.

  V5  A Makefile `SLOW_MODULES` / `ADMIT_MODULES` entry without a
      `# trusted-module: <module> : <reason>` mirror, or a non-empty ADMIT ratchet.

  V6  A `-<crate>::…` hax extraction-exclusion (`-i` filter) without a
      `# trusted-module: <token> : <reason>` mirror in hax.py / hax.sh.

V4/V5/V6 share their implementation with `trust_ledger.py --check` (they are its
CLAIMS-side lints) and run on the committed tree — no extraction needed.

Modes:
  report (default)  print violations, always exit 0 — for the migration period.
  --strict          exit 1 on any violation — for CI, once the sweep completes.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trust_scan as ts
import trust_ledger as tl

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


def marker_violations(repo_root):
    """V2/V2b/V3 trust-marker checks over the Rust source of every crate.

    Returns (v2, v2b, v3) lists of printable tuples."""
    v2, v2b, v3 = [], [], []
    for crate in CRATES:
        markers = ts.scan_rust_trust_markers(os.path.join(repo_root, crate), repo_root)

        # V2 — reason must carry a valid category prefix. Covers BOTH the G1 body
        # wrappers (trusted_admit!/trusted_assume!) and the G2 whole-function
        # attribute wrappers (#[trusted(lax|panic_free|opaque|exclude, "reason")]);
        # a reason-less G2 wrapper scans as reason "" and is flagged here.
        for b in markers["body"] + markers["attr"]:
            if not ts.reason_ok(b["reason"]):
                v2.append((b["file"], b["line"], b["kind"],
                           (b["reason"].strip()[:60] or "<empty>")))

        # V2b — fn-level label ↔ body macro must agree (both directions).
        # V3  — no raw obligation mechanisms outside the wrappers.
        missing, stale, raw = ts.marker_soundness(markers)
        for f, fn, k in missing:
            v2b.append((f, fn or "<unknown fn>",
                        f"body {k} without fn-level #[libcrux_macros::trusted({k})]"))
        for f, fn, k in stale:
            v2b.append((f, fn or "<unknown fn>",
                        f"stale fn-level #[libcrux_macros::trusted({k})] (no matching body macro)"))
        for f, line, k in raw:
            wrap = "trusted_admit!" if k == "admit" else "trusted_assume!"
            v3.append((f, line, f"proof!({k} …) — use {wrap}"))
    return v2, v2b, v3


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
    v2, v2b, v3 = marker_violations(repo_root)

    # V4/V5/V6 — companion-axiom tags + module/config mirrors. Shared with
    # trust_ledger --check; scoped to the two hax-verified crates with companions.
    v4, v5v6 = [], []
    for cn in ("ml-dsa", "ml-kem"):
        creg, _ = tl.check_companion_tags(repo_root, cn)
        vreg, _ = tl.check_module_mirrors(repo_root, cn)
        v4 += creg
        v5v6 += vreg

    if all_violations:
        print(
            f"V1: {len(all_violations)} untagged multi-line definition block(s) "
            "in before/after attributes (see PROOF_CONVENTIONS.md):"
        )
        for path, line, n in sorted(all_violations):
            print(f"  {path}:{line}  ({n} lines)")
    if v2:
        print(f"V2: {len(v2)} trust reason(s) without a valid category prefix:")
        for path, line, kind, reason in sorted(v2):
            print(f"  {path}:{line}  ({kind}) {reason}")
    if v2b:
        print(f"V2b: {len(v2b)} fn-level trust-label mismatch(es):")
        for path, fn, msg in sorted(v2b):
            print(f"  {path}  fn {fn}: {msg}")
    if v3:
        print(f"V3: {len(v3)} raw trust mechanism(s) outside the wrappers:")
        for path, line, msg in sorted(v3):
            print(f"  {path}:{line}  {msg}")
    if v4:
        print(f"V4: {len(v4)} companion-axiom tag issue(s):")
        for msg in sorted(v4):
            print(f"  {msg}")
    if v5v6:
        print(f"V5/V6: {len(v5v6)} module/config trust-mirror issue(s):")
        for msg in sorted(v5v6):
            print(f"  {msg}")

    total = (len(all_violations) + len(v2) + len(v2b) + len(v3)
             + len(v4) + len(v5v6))
    if total == 0:
        print("annotation lint: clean")
    sys.exit(1 if strict and total else 0)


if __name__ == "__main__":
    main()
