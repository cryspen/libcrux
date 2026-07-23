#!/usr/bin/env python3
"""Self-tests for the trust-ledger tooling (trust_scan.py + trust_ledger.py).

Runs with plain `python3 scripts/test_trust_ledger.py` — no pytest, no repo tree
needed (all synthetic). Locks the two behaviours that matter: the plane-1 obligation
tokenizer (kinds + comment masking) and the reconcile() regression/note gate. Uses
synthetic surfaces so it never depends on the live obligation counts (which drift as
admits are proved away)."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trust_scan as ts
import trust_ledger as tl

FAILURES = []


def check(cond, msg):
    if not cond:
        FAILURES.append(msg)
        print(f"  FAIL: {msg}")
    else:
        print(f"  ok:   {msg}")


# --------------------------------------------------------------------------
# Plane 1 — tokenizer + comment masking
# --------------------------------------------------------------------------
def test_tokenizer(tmp):
    src = r'''module Foo
let a = admit ()
val b : int -> int          // assume val here is a comment, must be masked
assume val real_stub : int
let c (x:int) = assume (x > 0); x
let d = magic ()
(* admit () inside a block comment, masked *)
[@@ "opaque"] let e = 1
#push-options "--admit_smt_queries true"
let f = 2
#pop-options
(* nested (* admit () *) still masked *)
'''
    p = os.path.join(tmp, "Foo.fst")
    open(p, "w").write(src)
    r = ts.scan_file_obligations(p)
    kinds = {}
    for rec in r:
        kinds[rec["kind"]] = kinds.get(rec["kind"], 0) + 1
    check(kinds.get("admit") == 1, f"one admit (masked comments excluded): got {kinds.get('admit')}")
    check(kinds.get("assume_val") == 1, f"one assume val (comment 'assume val' masked): got {kinds.get('assume_val')}")
    check(kinds.get("assume") == 1, f"one bare assume: got {kinds.get('assume')}")
    check(kinds.get("magic") == 1, f"one magic: got {kinds.get('magic')}")
    check(kinds.get("admit_smt_queries") == 1, f"one admit_smt_queries pragma: got {kinds.get('admit_smt_queries')}")
    check(len(r) == 5, f"exactly 5 obligations total: got {len(r)}")


def test_masking_preserves_lines(tmp):
    src = "let a = 1\n(* multi\nline\ncomment *)\nlet b = admit ()\n"
    p = os.path.join(tmp, "Bar.fst")
    open(p, "w").write(src)
    r = ts.scan_file_obligations(p)
    check(len(r) == 1 and r[0]["line"] == 5,
          f"admit reported at correct line 5 (masking keeps newlines): got {r and r[0]['line']}")


# --------------------------------------------------------------------------
# Reconcile — regression vs note across all four planes
# --------------------------------------------------------------------------
def _surface(total=10, by_module=None, by_kind=None, extraction=None,
             admit=None, slow=None, patches=None):
    return {"crate": "t", "planes": {
        "fstar": {"total": total, "scanned_files": 1,
                  "by_kind": by_kind or {"admit": total},
                  "by_module": by_module or {"M.A": total}},
        "extraction": {"modules": extraction or ["M.A", "M.B"]},
        "makefile": {"admit_modules": admit or [], "slow_modules": slow or []},
        "patches": patches or [],
    }}


def test_reconcile():
    base = _surface()

    r, n = tl.reconcile(base, base)
    check(not r and not n, "identity: no regressions, no notes")

    r, n = tl.reconcile(_surface(total=11, by_module={"M.A": 11}), base)
    check(any("total obligations" in x for x in r), "plane1: +1 obligation is a regression")

    r, n = tl.reconcile(_surface(total=12, by_module={"M.A": 10, "M.New": 2}), base)
    check(any("NEW module" in x for x in r), "plane1: brand-new module with obligations is a regression")

    r, n = tl.reconcile(_surface(total=9, by_module={"M.A": 9}), base)
    check(not r and any("rebaseline" in x for x in n), "plane1: reduction is a NOTE, not a regression")

    r, n = tl.reconcile(_surface(by_kind={"assume": 10}, by_module={"M.A": 10}), base)
    check(any("new obligation kind" in x for x in r), "plane1: new obligation kind is a regression")

    r, n = tl.reconcile(_surface(extraction=["M.A"]), base)
    check(any("no longer extracted" in x for x in r), "plane2: dropped coverage is a regression")
    r, n = tl.reconcile(_surface(extraction=["M.A", "M.B", "M.C"]), base)
    check(not r and any("newly extracted" in x for x in n), "plane2: new coverage is a NOTE")

    r, n = tl.reconcile(_surface(admit=["M.X"]), base)
    check(any("ADMIT_MODULES grew" in x for x in r), "plane3: ADMIT growth is a regression (empty ratchet)")
    r, n = tl.reconcile(_surface(slow=["M.Y"]), base)
    check(any("SLOW_MODULES grew" in x for x in r), "plane3: SLOW growth is a regression")

    r, n = tl.reconcile(_surface(patches=[{"path": "p.patch", "sha256": "x"}]), base)
    check(any("new post-extraction patch" in x for x in r), "plane4: new patch is a regression")
    withpatch = _surface(patches=[{"path": "p.patch", "sha256": "x"}])
    r, n = tl.reconcile(_surface(patches=[{"path": "p.patch", "sha256": "y"}]), withpatch)
    check(not r and any("content changed" in x for x in n), "plane4: patch digest churn is a NOTE")


def main():
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        print("[tokenizer]")
        test_tokenizer(tmp)
        test_masking_preserves_lines(tmp)
    print("[reconcile]")
    test_reconcile()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s)")
        return 1
    print("all trust-ledger self-tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
