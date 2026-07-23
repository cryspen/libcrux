#!/usr/bin/env python3
"""Trust-ledger reconciler (V7) — the trust campaign's ground-truth centerpiece.

Computes the OBSERVED trust surface of each hax-verified crate directly from build
artifacts (via scripts/trust_scan.py), stores it as a committed per-crate baseline
JSON, and fails CI on any *regression* — a new unproven obligation, a module that
silently stopped extracting, or a grown ADMIT_MODULES list. The ledger is computed
EXCLUSIVELY from the observed side, so no source marker can shrink the reported
surface (plan requirement).

Four observed planes (see trust_scan.py):
  fstar       admit ()/magic ()/assume/assume val/--admit_smt_queries true obligations
  extraction  the set of extracted F* modules (coverage)
  makefile    SLOW_MODULES / ADMIT_MODULES declared in the F* Makefile
  patches     post-extraction *.patch files (count + digest)

Baselines: <crate>/proofs/trust-ledger.baseline.json (git-tracked).

Usage:
  trust_ledger.py [--repo-root PATH] [--crate ml-dsa|ml-kem|sha3] [--json]
  trust_ledger.py --check           # default: compare observed vs baseline, exit 1 on regression
  trust_ledger.py --update-baseline # rewrite baselines from the current observed surface

MARKER RECONCILIATION (G1+): once the `#[trusted(kind, "reason")]` attribute + body
macros land, `reconcile_markers()` gains a second direction — every observed obligation
must map to a matching-kind marker / F* `[@@ "trusted: ..."]` tag / trusted-base
allowlist entry, and every marker must map forward to an observed obligation. At G0
there are no such markers, so only the observed-side baseline + regression gate run.
"""

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trust_scan as ts

# ---------------------------------------------------------------------------
# Crate registry. Paths are relative to the repo root.
# ---------------------------------------------------------------------------
CRATES = {
    "ml-dsa": {
        "root": "libcrux-ml-dsa",
        "prefix": "Libcrux_ml_dsa.",
    },
    "ml-kem": {
        "root": "libcrux-ml-kem",
        "prefix": "Libcrux_ml_kem.",
    },
    "sha3": {
        "root": "crates/algorithms/sha3",
        "prefix": "Libcrux_sha3.",
    },
}

BASELINE_NAME = os.path.join("proofs", "trust-ledger.baseline.json")


def _abs(repo_root, *parts):
    return os.path.join(repo_root, *parts)


# ===========================================================================
# Observed-surface computation
# ===========================================================================

def observe(repo_root, crate_name):
    """Compute the observed 4-plane trust surface for one crate."""
    spec = CRATES[crate_name]
    crate_root = _abs(repo_root, spec["root"])
    fstar_root = os.path.join(crate_root, "proofs", "fstar")
    extraction_dir = os.path.join(fstar_root, "extraction")
    makefile = os.path.join(extraction_dir, "Makefile")

    obl = ts.scan_obligations(fstar_root)
    return {
        "crate": crate_name,
        "planes": {
            "fstar": {
                "total": obl["total"],
                "scanned_files": obl["scanned_files"],
                "by_kind": dict(sorted(obl["by_kind"].items())),
                "by_module": dict(sorted(obl["by_file"].items())),
            },
            "extraction": {
                "modules": ts.list_extracted_module_names(extraction_dir, spec["prefix"]),
            },
            "makefile": {
                "slow_modules": ts.parse_makefile_module_list(makefile, "SLOW_MODULES"),
                "admit_modules": ts.parse_makefile_module_list(makefile, "ADMIT_MODULES"),
            },
            "patches": ts.list_fstar_patches(crate_root),
        },
    }


# ===========================================================================
# Baseline I/O
# ===========================================================================

def baseline_path(repo_root, crate_name):
    return _abs(repo_root, CRATES[crate_name]["root"], BASELINE_NAME)


def load_baseline(repo_root, crate_name):
    p = baseline_path(repo_root, crate_name)
    if not os.path.isfile(p):
        return None
    with open(p) as f:
        return json.load(f)


def write_baseline(repo_root, crate_name, observed):
    p = baseline_path(repo_root, crate_name)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    header = (
        "// AUTO-GENERATED observed-side trust ledger baseline "
        "(scripts/trust_ledger.py). Do not edit by hand.\n"
    )
    with open(p, "w") as f:
        # A leading // comment keeps the intent visible; strip it before json.load.
        f.write(header)
        json.dump(observed, f, indent=2, sort_keys=True)
        f.write("\n")
    return p


def _load_json_with_comment(path):
    with open(path) as f:
        text = f.read()
    lines = [ln for ln in text.splitlines() if not ln.lstrip().startswith("//")]
    return json.loads("\n".join(lines))


# ===========================================================================
# Regression gate (observed vs baseline)
# ===========================================================================

def reconcile(observed, baseline):
    """Compare an observed surface against its baseline.

    Returns (regressions, notes). `regressions` are hard failures (the trust
    surface grew); `notes` are non-failing changes worth a human glance
    (reductions — rebaseline! — new coverage, SLOW/patch churn)."""
    regressions, notes = [], []
    op, bp = observed["planes"], baseline["planes"]

    # ---- plane 1: F* obligations ----------------------------------------
    ot, bt = op["fstar"]["total"], bp["fstar"]["total"]
    if ot > bt:
        regressions.append(f"[fstar] total obligations {bt} -> {ot} (+{ot - bt})")
    elif ot < bt:
        notes.append(f"[fstar] total obligations {bt} -> {ot} ({ot - bt}); rebaseline to lock the win")

    obm, bbm = op["fstar"]["by_module"], bp["fstar"]["by_module"]
    for mod in sorted(set(obm) | set(bbm)):
        o, b = obm.get(mod, 0), bbm.get(mod, 0)
        if o > b:
            what = "NEW module with obligations" if b == 0 else f"{b} -> {o}"
            regressions.append(f"[fstar] {mod}: {what} (+{o - b})")

    obk, bbk = op["fstar"]["by_kind"], bp["fstar"]["by_kind"]
    for kind in sorted(set(obk) - set(bbk)):
        regressions.append(f"[fstar] new obligation kind '{kind}' x{obk[kind]}")

    # ---- plane 2: extraction coverage -----------------------------------
    oe, be = set(op["extraction"]["modules"]), set(bp["extraction"]["modules"])
    for mod in sorted(be - oe):
        regressions.append(f"[extraction] module no longer extracted: {mod}")
    for mod in sorted(oe - be):
        notes.append(f"[extraction] newly extracted module: {mod}")

    # ---- plane 3: Makefile SLOW / ADMIT ---------------------------------
    oa, ba = set(op["makefile"]["admit_modules"]), set(bp["makefile"]["admit_modules"])
    for mod in sorted(oa - ba):
        regressions.append(f"[makefile] ADMIT_MODULES grew (ratchet is empty): +{mod}")
    for mod in sorted(ba - oa):
        notes.append(f"[makefile] ADMIT_MODULES shrank: -{mod}")
    os_, bs_ = set(op["makefile"]["slow_modules"]), set(bp["makefile"]["slow_modules"])
    for mod in sorted(os_ - bs_):
        regressions.append(f"[makefile] SLOW_MODULES grew (verified-on-cadence trust): +{mod}")
    for mod in sorted(bs_ - os_):
        notes.append(f"[makefile] SLOW_MODULES shrank: -{mod}")

    # ---- plane 4: patches (count-only regression, digest churn is a note)
    opatch = {d["path"]: d["sha256"] for d in op["patches"]}
    bpatch = {d["path"]: d["sha256"] for d in bp["patches"]}
    for path in sorted(set(opatch) - set(bpatch)):
        regressions.append(f"[patches] new post-extraction patch: {path}")
    for path in sorted(set(bpatch) - set(opatch)):
        notes.append(f"[patches] patch removed: {path}")
    for path in sorted(set(opatch) & set(bpatch)):
        if opatch[path] != bpatch[path]:
            notes.append(f"[patches] patch content changed: {path}")

    return regressions, notes


# ===========================================================================
# Reporting
# ===========================================================================

def summarize(observed):
    p = observed["planes"]
    return (
        f"{observed['crate']:>7}: "
        f"fstar={p['fstar']['total']:<4} "
        f"kinds={p['fstar']['by_kind']} "
        f"extracted={len(p['extraction']['modules'])} "
        f"slow={len(p['makefile']['slow_modules'])} "
        f"admit={len(p['makefile']['admit_modules'])} "
        f"patches={len(p['patches'])}"
    )


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo-root", default=None,
                    help="Repo root (default: parent of scripts/)")
    ap.add_argument("--crate", choices=sorted(CRATES), action="append",
                    help="Restrict to one crate (repeatable). Default: all.")
    ap.add_argument("--check", action="store_true",
                    help="Compare observed vs baseline; exit 1 on regression (default action).")
    ap.add_argument("--update-baseline", action="store_true",
                    help="Rewrite baselines from the current observed surface.")
    ap.add_argument("--json", action="store_true",
                    help="Print the observed surface as JSON instead of the summary.")
    args = ap.parse_args()

    repo_root = os.path.abspath(
        args.repo_root or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    )
    crates = args.crate or sorted(CRATES)

    if args.json:
        out = {c: observe(repo_root, c) for c in crates}
        print(json.dumps(out, indent=2, sort_keys=True))
        return 0

    if args.update_baseline:
        for c in crates:
            observed = observe(repo_root, c)
            p = write_baseline(repo_root, c, observed)
            print(f"wrote {os.path.relpath(p, repo_root)}")
            print("  " + summarize(observed))
        return 0

    # default: --check
    exit_code = 0
    for c in crates:
        observed = observe(repo_root, c)
        print(summarize(observed))
        bpath = baseline_path(repo_root, c)
        if not os.path.isfile(bpath):
            print(f"  no baseline yet ({os.path.relpath(bpath, repo_root)}); run --update-baseline")
            continue
        baseline = _load_json_with_comment(bpath)
        regressions, notes = reconcile(observed, baseline)
        for n in notes:
            print(f"  note: {n}")
        for r in regressions:
            print(f"  REGRESSION: {r}")
        if regressions:
            exit_code = 1
    if exit_code:
        print("\ntrust-ledger: REGRESSION — the trust surface grew. "
              "Prove the new obligation away, or justify + rebaseline deliberately.")
    else:
        print("\ntrust-ledger: clean (observed surface within baseline).")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
