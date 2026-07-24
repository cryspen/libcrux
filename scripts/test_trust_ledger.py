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


# --------------------------------------------------------------------------
# Trust markers — Rust-source scanner + soundness (G1)
# --------------------------------------------------------------------------
_MARKER_SRC = r'''// masked: trusted_admit!("should not count") in a line comment
/// masked doc: proof!("admit ()") mention
mod m {
    #[libcrux_macros::trusted(inline-admit)]
    pub(crate) fn g<T>() {
        trusted_admit!("hax-limitation: simultaneous borrows");
    }
    fn h() {
        trusted_assume!(
            "pending-proof(E5): bridge \
             continued",
            r#"assume (${x}.f == ${y}.g)"#
        );
    }
    fn raw() {
        proof!("admit ()");
        proof!(r#"assume (true)"#);
    }
    fn badreason() {
        trusted_admit!("nocategory here");
    }
}
'''


def test_marker_scan(tmp):
    d = os.path.join(tmp, "scan")
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, "m.rs"), "w").write(_MARKER_SRC)
    mk = ts.scan_rust_trust_markers(d, d)
    check(len(mk["body"]) == 3, f"3 body markers (comment mentions masked): got {len(mk['body'])}")
    check(len(mk["labels"]) == 1, f"1 fn-level label: got {len(mk['labels'])}")
    check(len(mk["raw_admit"]) == 1, f"1 raw proof!(admit): got {len(mk['raw_admit'])}")
    check(len(mk["raw_assume"]) == 1, f"1 raw proof!(assume): got {len(mk['raw_assume'])}")
    by_fn = {b["fn"]: b for b in mk["body"]}
    check(by_fn.get("g", {}).get("kind") == "inline-admit", "g is inline-admit body")
    check(by_fn.get("h", {}).get("kind") == "inline-assume", "h is inline-assume body")
    check(by_fn.get("h", {}).get("reason", "").startswith("pending-proof(E5): bridge continued"),
          f"h reason collapses \\-continuation: {by_fn.get('h', {}).get('reason')!r}")
    check(mk["labels"][0]["fn"] == "g", "label attaches to following fn g")


_ATTR_SRC = r'''mod m {
    #[libcrux_macros::trusted(panic_free, "pending-proof(campaign): ensures admitted")]
    pub(crate) fn a() {}

    #[libcrux_macros::trusted(
        opaque,
        "trusted-extern: keccak state handle"
    )]
    pub(crate) struct S { x: u8 }

    #[cfg_attr(hax, hax_lib::trusted(lax, "bad reason no category"))]
    fn ignore_me_not_our_macro() {}

    #[libcrux_macros::trusted(exclude, "random: not a category")]
    fn b() {}

    #[libcrux_macros::trusted(opaque)]
    struct Missing {}
}
'''


def test_attr_markers(tmp):
    d = os.path.join(tmp, "attr")
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, "a.rs"), "w").write(_ATTR_SRC)
    mk = ts.scan_rust_trust_markers(d, d)
    kinds = sorted(a["kind"] for a in mk["attr"])
    check(kinds == ["exclude", "opaque", "opaque", "panic_free"],
          f"4 attr wrappers scanned (panic_free/opaque x2/exclude): got {kinds}")
    by_kind = {}
    for a in mk["attr"]:
        by_kind.setdefault(a["kind"], []).append(a)
    check(any(a["reason"].startswith("pending-proof(campaign)") for a in by_kind["panic_free"]),
          "panic_free reason captured")
    check(any(a["reason"].startswith("trusted-extern:") for a in by_kind["opaque"]),
          "multi-line opaque reason captured")
    # exclude wrapper has an invalid-category reason -> V2 should flag it.
    check(any(not ts.reason_ok(a["reason"]) for a in by_kind["exclude"]),
          "exclude bad-category reason flagged by reason_ok")
    # reason-less opaque wrapper -> reason "" -> flagged.
    check(any(a["reason"] == "" for a in by_kind["opaque"]),
          "reason-less opaque wrapper scans as empty reason")


def test_reason_format():
    for good in ["hax-limitation: x", "pending-proof(E5): y", "validated-axiom: z",
                 "  slow-proof: trimmed", "unprovable-termination: t", "trusted-extern: e"]:
        check(ts.reason_ok(good), f"reason_ok True: {good!r}")
    for bad in ["pending-proof: missing ref", "random: z", "hax-limitation no colon",
                "", "hax-limitation:no-space"]:
        check(not ts.reason_ok(bad), f"reason_ok False: {bad!r}")


def test_marker_soundness(tmp):
    d = os.path.join(tmp, "sound")
    os.makedirs(d, exist_ok=True)
    open(os.path.join(d, "m2.rs"), "w").write(_MARKER_SRC)
    mk = ts.scan_rust_trust_markers(d, d)
    missing, stale, raw = ts.marker_soundness(mk)
    miss_fns = {(fn, k) for _, fn, k in missing}
    check(("h", "inline-assume") in miss_fns, "h body without label -> missing")
    check(("badreason", "inline-admit") in miss_fns, "badreason body without label -> missing")
    check(("g", "inline-admit") not in miss_fns, "g has matching label -> not missing")
    check(not stale, f"no stale labels in this fixture: got {stale}")
    check(len(raw) == 2, f"2 raw bans (admit+assume): got {len(raw)}")


def test_rust_comment_masking():
    m = ts.mask_rust_comments('let s = "a // b /* c */ d"; // real\nlet t = 1;')
    check("a // b /* c */ d" in m, "string literal content preserved through masking")
    check("real" not in m, "line comment masked")
    check(m.count("\n") == 1, "newline count preserved")
    m2 = ts.mask_rust_comments('let r = r#"x /* y */ z"#;')
    check("x /* y */ z" in m2, "raw string content preserved")


def main():
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        print("[tokenizer]")
        test_tokenizer(tmp)
        test_masking_preserves_lines(tmp)
        print("[markers]")
        test_marker_scan(tmp)
        test_marker_soundness(tmp)
        test_attr_markers(tmp)
    print("[reason-format]")
    test_reason_format()
    print("[rust-comment-masking]")
    test_rust_comment_masking()
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
