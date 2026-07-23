#!/usr/bin/env python3
"""Shared OBSERVED-SIDE scanner for the trust-annotation ledger (V7 reconciler).

Pure Python, no F*/proxy/`make` dependency — safe to run in CI after `extract`.
This is the single shared scanner the trust campaign's plan calls for: it computes
the *observed* trust surface directly from build artifacts, so the ledger can never
be shrunk by a stale or optimistic source marker (see the plan's V7 section).

Four observed planes, one function each:

  plane 1  fstar       unproven obligations in the extracted .fst/.fsti + hand-written
                       companions (admit ()/magic ()/assume/assume val/--admit_smt_queries
                       true). Reproduces the `fstar_admits` MCP tool WITHOUT the proxy.
  plane 2  extraction  the set of extracted F* modules (coverage). A module that stops
                       extracting (hax `-i` filter, deleted .fst) drops out of this set.
  plane 3  makefile    SLOW_MODULES / ADMIT_MODULES declared in the F* Makefile — the
                       modules verified-on-cadence or admitted-in-default-build (plane
                       that fstar_admits alone cannot see).
  plane 4  patches     post-extraction *.patch files under proofs/fstar (count + digest).

`generate_verification_status.py` reuses the plane-1 scanner and the Makefile parser
here so there is exactly one obligation-scanning implementation in the tree.
"""

import hashlib
import os
import re

# ---------------------------------------------------------------------------
# Directories never scanned for F* obligations (caches, VCS, build output).
# ---------------------------------------------------------------------------
_SKIP_DIRS = {".fstar-cache", ".git", "target", "cache", "hints", "node_modules"}


# ===========================================================================
# Plane 1 — F* obligations (reproduces the fstar_admits MCP tool, proxy-free)
# ===========================================================================

def mask_fstar_comments(text):
    """Replace F* comments with spaces (newlines preserved so line numbers hold).

    Handles NESTED block comments `(* ... (* ... *) ... *)` and `//` line comments.
    String literals are intentionally NOT masked — mirrors fstar_admits, where a
    marker inside a string literal can still be reported."""
    out = []
    i, n = 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "(*":
            depth = 1
            out.append("  ")
            i += 2
            while i < n and depth > 0:
                t2 = text[i:i + 2]
                if t2 == "(*":
                    depth += 1
                    out.append("  ")
                    i += 2
                elif t2 == "*)":
                    depth -= 1
                    out.append("  ")
                    i += 2
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
            continue
        if two == "//":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


# One record kind per pattern. `assume val` is matched before bare `assume`
# (the bare pattern uses a negative lookahead so the two never double-count).
_ASSUME_VAL_RE = re.compile(r"\bassume\s+val\b")
_ASSUME_RE = re.compile(r"\bassume\b(?!\s+val\b)")
_ADMIT_RE = re.compile(r"\badmit\s*\(\s*\)")
_MAGIC_RE = re.compile(r"\bmagic\s*\(\s*\)")
_ADMIT_SMT_RE = re.compile(r"admit_smt_queries\s+true")

_KIND_PATTERNS = [
    ("assume_val", _ASSUME_VAL_RE),
    ("assume", _ASSUME_RE),
    ("admit", _ADMIT_RE),
    ("magic", _MAGIC_RE),
    ("admit_smt_queries", _ADMIT_SMT_RE),
]


def _line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def module_name_of(path):
    """`.../Libcrux_ml_dsa.Matrix.fst` -> `Libcrux_ml_dsa.Matrix`."""
    base = os.path.basename(path)
    return base.removesuffix(".fsti").removesuffix(".fst")


def scan_file_obligations(path):
    """Return a list of {file, module, line, kind} obligation records for one
    .fst/.fsti file, matching the fstar_admits tokenizer (comment-masked)."""
    with open(path, encoding="utf-8", errors="replace") as f:
        text = f.read()
    masked = mask_fstar_comments(text)
    module = module_name_of(path)
    records = []
    for kind, rx in _KIND_PATTERNS:
        for m in rx.finditer(masked):
            records.append({
                "file": path,
                "module": module,
                "line": _line_of(masked, m.start()),
                "kind": kind,
            })
    return records


def scan_obligations(root):
    """Walk `root` for .fst/.fsti (skipping caches) and collect all obligation
    records. Returns dict with total, by_kind, by_file (module->count), records,
    and scanned_files — the same shape the fstar_admits summary exposes."""
    records = []
    scanned = 0
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS]
        for fn in filenames:
            if fn.endswith(".fst") or fn.endswith(".fsti"):
                scanned += 1
                records.extend(scan_file_obligations(os.path.join(dirpath, fn)))
    by_kind, by_file = {}, {}
    for r in records:
        by_kind[r["kind"]] = by_kind.get(r["kind"], 0) + 1
        by_file[r["module"]] = by_file.get(r["module"], 0) + 1
    return {
        "total": len(records),
        "scanned_files": scanned,
        "by_kind": by_kind,
        "by_file": by_file,
        "records": records,
    }


# ===========================================================================
# Plane 2 — extraction coverage (the set of extracted F* modules)
# ===========================================================================

def list_extracted_module_names(extraction_dir, prefix):
    """Return the sorted set of extracted F* module names under `extraction_dir`
    whose name starts with `prefix` (e.g. `Libcrux_ml_dsa.`). A module dropping
    out of this set means it stopped extracting (hax `-i` filter / deletion)."""
    if not os.path.isdir(extraction_dir):
        return []
    names = set()
    for fn in os.listdir(extraction_dir):
        if (fn.endswith(".fst") or fn.endswith(".fsti")) and fn.startswith(prefix):
            names.add(module_name_of(fn))
    return sorted(names)


# ===========================================================================
# Plane 3 — Makefile SLOW_MODULES / ADMIT_MODULES (build-admitted plane)
# ===========================================================================

def parse_makefile_module_list(makefile_path, var_name):
    """Read a Makefile variable that lists F* module names (`+=`/`=`, one per line,
    `\\`-continued) and return them as a sorted list of module names. Tokens that
    aren't module-shaped (`$(...)`, `filter-out`, operators) are ignored."""
    if not os.path.isfile(makefile_path):
        return []
    mods = set()
    in_var = False
    with open(makefile_path) as f:
        for line in f:
            head = line.lstrip()
            if head.startswith(var_name) and (
                head[len(var_name):len(var_name) + 1] in (" ", "\t", "+", "=", ":")
            ):
                in_var = True
                line = line.split("=", 1)[1] if "=" in line else ""
            if in_var:
                for token in line.split():
                    tok = token.removesuffix(".fst").removesuffix(".fsti")
                    if re.fullmatch(r"[A-Za-z0-9_.]+", tok) and "." in tok:
                        mods.add(tok)
                if not line.rstrip().endswith("\\"):
                    in_var = False
    return sorted(mods)


# ===========================================================================
# Plane 4 — post-extraction patches (count + digest)
# ===========================================================================

def list_fstar_patches(crate_root):
    """Return sorted [{path, sha256}] for every *.patch under <crate>/proofs/fstar.
    These are the manual post-extraction edits applied to the F* tree."""
    fstar_root = os.path.join(crate_root, "proofs", "fstar")
    out = []
    for dirpath, dirnames, filenames in os.walk(fstar_root):
        dirnames[:] = [d for d in dirnames if d not in _SKIP_DIRS]
        for fn in sorted(filenames):
            if fn.endswith(".patch"):
                p = os.path.join(dirpath, fn)
                with open(p, "rb") as fh:
                    digest = hashlib.sha256(fh.read()).hexdigest()
                out.append({
                    "path": os.path.relpath(p, crate_root),
                    "sha256": digest,
                })
    return sorted(out, key=lambda d: d["path"])
