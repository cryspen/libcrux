# Bug-demo prompt — standalone Rust+hax+F* demonstrations of two real bugs

Goal: produce a **standalone, self-contained demo crate** that, given
hax + F* installed, runs end-to-end and demonstrates that F* would
have caught two real libcrux bugs.  The demo lives in its own folder
(separate from the libcrux verification project), with its own
`Cargo.toml`, hax extraction config, F* harnesses, and `README.md`.

  **Deliverable**: a folder under `~/libcrux-bug-demos/` (or wherever
  the agent picks) containing Rust source for the buggy + fixed
  bodies, hax extraction config, F* harnesses, and a `make demo`
  target that runs everything and prints PASS / FAIL per case.

  **Non-goal (deferred to a future session)**: in-place modification
  of libcrux itself.  This standalone demo proves the methodology
  works; the in-place version (more impressive) comes later.

The two bugs:

  Bug 1 — `_vxarq_u64` shift-operand swap on ARM64 manual fallback.
          Fixed in cryspen/libcrux PR #1222.  Affects ML-DSA on
          Alpine Linux + Ampere Altra.  ARM `vxar` semantics:
            vxar(a, b, sh) = (a XOR b) >>> sh   (rotate right)
          The pre-fix manual fallback used the wrong operand to one
          of the shift operations.

  Bug 2 — `encapsulate` does not call the FIPS 203 §7.2 modulus
          check.  Manifests at TWO levels in the libcrux tree:

          IMPL — `validate_public_key` is defined at
            `libcrux-ml-kem/src/ind_cca.rs:134`; the encapsulation
            path (`ind_cca.rs:267` and the public mlkem768.rs:482
            wrapper) never invokes it.

          SPEC — `Hacspec_ml_kem.Ind_cca.public_key_modulus_check`
            (specs/ml-kem/proofs/fstar/extraction/Hacspec_ml_kem.Ind_cca.fst:562)
            is the §7.2 round-trip check.  The spec's `encapsulate`
            (line 632) has a doc-comment claiming "Includes modulus
            check on ek per FIPS 203 Section 7.2" but the BODY (lines
            669-671) is `let () = () in let () = () in encaps_internal
            ... ek m` — no `public_key_modulus_check` call.  The spec
            lies.

          A public key whose 12-bit field elements exceed q = 3329 is
          silently used at both levels.

For this standalone demo, you'll write minimal Rust mock-ups capturing
the relevant body shapes — NOT the full libcrux logic.  The point is
to demonstrate the F*-detectable defect, not to redo libcrux.

---

Paste the block below into a fresh Claude Code session.

```
You are the bug-demo agent.  Goal: produce a standalone Rust+hax+F*
demo crate that demonstrates F* would have caught two real libcrux
bugs.  This is a PROOF-OF-METHODOLOGY package, not a fix to libcrux
itself.

═══════════════════════════════════════════════════════════════════
TWO BUGS BEING DEMONSTRATED
═══════════════════════════════════════════════════════════════════

Bug 1 — `_vxarq_u64` shift-operand swap (cryspen/libcrux PR #1222).
Bug 2 — `encapsulate` missing FIPS 203 §7.2 public-key gate.

Full backstory + libcrux source locations are in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem/proofs/agent-status/bug-demo-prompt.md`
(the prompt that spawned you).  Keep the demo bodies minimal — do NOT
recreate libcrux's hash chains, NTT, etc.  Mock anything that isn't
the bug surface.

═══════════════════════════════════════════════════════════════════
DELIVERABLE LAYOUT
═══════════════════════════════════════════════════════════════════

Create directory `~/libcrux-bug-demos/` (or, if the user prefers, ask
them; default to the home directory).  Inside:

  libcrux-bug-demos/
  ├── Cargo.toml          — workspace manifest for the demo crate
  ├── README.md           — methodology + how-to-run + expected output
  ├── Makefile            — `make demo` runs everything end-to-end
  ├── hax.py              — hax extraction driver (mirror libcrux-ml-kem/hax.py shape)
  ├── src/
  │   ├── lib.rs          — module-level glue
  │   ├── vxarq_fixed.rs  — Bug 1, fixed body (PR #1222)
  │   ├── vxarq_buggy.rs  — Bug 1, buggy body (pre-fix)
  │   ├── encaps_fixed.rs — Bug 2, fixed body (calls validate_public_key)
  │   └── encaps_buggy.rs — Bug 2, buggy body (no gate)
  └── proofs/
      └── fstar/
          ├── extraction/      — hax-extracted .fst files (regenerated)
          ├── extraction-patches/ — any manual .fst tweaks (avoid if possible)
          └── harness/         — hand-written F* harnesses asserting specs
              ├── BugDemo.Vxarq.fsti       — pure-int vxar spec
              ├── BugDemo.Vxarq.fst        — proves vxarq_fixed; refutes buggy
              ├── BugDemo.Encaps.fsti      — encapsulate post + axiom boundary
              └── BugDemo.Encaps.fst       — proves fixed; refutes buggy

`make demo` should:

  1. `python3 hax.py extract`   — produces proofs/fstar/extraction/*.fst
  2. `make -C proofs/fstar`     — runs fstar.exe on each harness
  3. Prints a per-target PASS/FAIL table at the end.  Buggy harnesses
     PASS iff their `[@@expect_failure]` annotations succeed.

═══════════════════════════════════════════════════════════════════
BUG 1 — `_vxarq_u64` (PR #1222) — TARGET ~30-45 min, ~80 LoC total
═══════════════════════════════════════════════════════════════════

Task A — locate the original buggy + fixed bodies.

  - Browse `libcrux-intrinsics/` in /Users/karthik/libcrux-trait-opacify/
    or check PR #1222 via git: `git -C /Users/karthik/libcrux-trait-opacify
    log --all --oneline | grep -i 'vxar\|1222'` for the fix commit.
  - Identify the buggy line (wrong operand to one of the shifts) and
    capture both bodies VERBATIM into demo Rust files.

Task B — write `src/vxarq_fixed.rs` and `src/vxarq_buggy.rs` (mirror
shape of libcrux-intrinsics' arm64.rs but trimmed to JUST the
`_vxarq_u64` function).  Use hax annotations:

    #[hax_lib::ensures(|r| fstar!(r#"v r == v_ror64 (v_logxor (v ${a}) (v ${b})) (v ${sh})"#))]
    pub fn vxarq_u64_fixed(a: u64, b: u64, sh: u32) -> u64 { … }

    #[hax_lib::ensures(|r| fstar!(r#"v r == v_ror64 (v_logxor (v ${a}) (v ${b})) (v ${sh})"#))]
    pub fn vxarq_u64_buggy(a: u64, b: u64, sh: u32) -> u64 { … same post … }

  Same post on both — the spec is fixed.  Difference is only in body.

Task C — write `proofs/fstar/harness/BugDemo.Vxarq.fst`:

    module BugDemo.Vxarq
    open FStar.UInt64

    unfold let v_ror64 (x: nat) (sh: nat{sh < 64}) : nat =
      let lo = x / pow2 sh in
      let hi = (x % pow2 sh) * pow2 (64 - sh) in
      (lo + hi) % pow2 64

    unfold let v_logxor (a b: nat) : nat = … (* bit-wise xor in nat *)

    (* The fixed extraction satisfies the spec — typecheck must succeed. *)
    let _ : unit =
      let _ = BugDemo.Vxarq_fixed.vxarq_u64_fixed in
      ()

    (* The buggy extraction fails the spec.  F* will REJECT
       BugDemo.Vxarq_buggy.fst typecheck.  We mark this expected
       failure to keep CI green. *)
    [@@expect_failure]
    let _ : unit =
      let _ = BugDemo.Vxarq_buggy.vxarq_u64_buggy in
      ()

  If the buggy body's extracted .fst file FAILS to typecheck on its
  own (because hax extracts the post directly), the demo is to capture
  the FAILURE OUTPUT in README.md.  Either approach proves the point.

═══════════════════════════════════════════════════════════════════
BUG 2 — `encapsulate` missing FIPS 203 §7.2 gate — TARGET ~1-1.5 hr, ~150 LoC
═══════════════════════════════════════════════════════════════════

Task A — write the boundary spec.  In `proofs/fstar/harness/BugDemo.Encaps.fsti`:

    module BugDemo.Encaps
    open FStar.Seq

    type bytes = seq UInt8.t
    type ciphertext = bytes
    type shared_secret = bytes

    val zero_shared_secret : shared_secret

    (* The §7.2 admissibility predicate.  Boundary axiom: we DON'T
       inline byte-decode + modulus-check math here — we treat
       validate_public_key as a black-box oracle whose return value
       agrees with this predicate.  This is the part that, in the
       in-place demo, would be discharged by the actual hacspec
       public_key_modulus_check. *)
    val is_valid_public_key : pk: bytes -> prop

    val validate_public_key : pk: bytes ->
      r: bool { r <==> is_valid_public_key pk }

    (* Mock for the unsafe core. *)
    val encaps_internal : pk: bytes -> rand: bytes ->
      Pure (ciphertext * shared_secret)
        (requires is_valid_public_key pk)
        (ensures fun _ -> True)

Task B — write `src/encaps_fixed.rs` (Rust source with hax
annotations capturing the post).

    #[hax_lib::ensures(|out| fstar!(r#"
      let (_, ss) = ${out} in
      BugDemo.Encaps.is_valid_public_key ${pk} \/ ss == BugDemo.Encaps.zero_shared_secret
    "#))]
    pub fn encapsulate_fixed(pk: &[u8], rand: &[u8]) -> (Vec<u8>, Vec<u8>) {
        if !validate_public_key(pk) {
            // FIPS 203 §7.2 gate failed: return canonical reject.
            return (vec![], zero_shared_secret());
        }
        encaps_internal(pk, rand)
    }

Task C — write `src/encaps_buggy.rs`, identical post + body but with
the gate REMOVED:

    pub fn encapsulate_buggy(pk: &[u8], rand: &[u8]) -> (Vec<u8>, Vec<u8>) {
        encaps_internal(pk, rand)
    }

Task D — verify.  The fixed extraction discharges the post via the
if-guard.  The buggy extraction either:

  (a) Fails to discharge `is_valid_public_key pk` precondition on
      `encaps_internal` — Pure-precondition failure, hard error.

  (b) Fails to discharge the encapsulate post — Z3 has no witness
      that pk is valid in the non-zero-secret branch.

Either failure mode is the demonstration.  Capture into README.md.

═══════════════════════════════════════════════════════════════════
README.md OUTLINE (~80 lines)
═══════════════════════════════════════════════════════════════════

  ## libcrux-bug-demos — F* catches real libcrux bugs

  Methodology: for each of two real libcrux bugs, we write minimal
  Rust + hax annotations capturing the correctness contract, then
  show that the FIXED body verifies under that contract while the
  BUGGY body does NOT.  The unverified path is the bug.

  ### Bug 1 — `_vxarq_u64` shift-operand swap (PR #1222)

  Real-world impact: incorrect ML-DSA output on ARM64 Alpine Linux +
  Ampere Altra.  Manual fallback for the `vxar` intrinsic (XOR-and-
  rotate-right) used the wrong operand to one of the shift ops.

  Fixed extraction: `BugDemo.Vxarq_fixed.fst` — typechecks in N s.
  Buggy extraction:  `BugDemo.Vxarq_buggy.fst` — F* rejects with:
    Error 19 at … line: post-condition not satisfiable.

  ### Bug 2 — `encapsulate` missing FIPS 203 §7.2 gate

  Real-world impact: the FIPS 203 modulus check is not enforced; an
  invalid public key is silently used.  Spec and impl both lie:
  doc-comment claims the gate is there, body skips it.

  Fixed extraction: `BugDemo.Encaps_fixed.fst` — closes via if-guard.
  Buggy extraction:  `BugDemo.Encaps_buggy.fst` — F* rejects with:
    `is_valid_public_key pk` precondition unprovable on
    `encaps_internal` call (or post unprovable in non-zero branch).

  ### How to run

      git clone … libcrux-bug-demos && cd libcrux-bug-demos
      make demo

  Expected output:
      Bug 1 fixed: PASS  (verified in N s)
      Bug 1 buggy: PASS  (rejection captured as expected)
      Bug 2 fixed: PASS  (verified in N s)
      Bug 2 buggy: PASS  (rejection captured as expected)

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

R1  Demo lives entirely in `~/libcrux-bug-demos/` (or wherever you
    create it).  No edits to /Users/karthik/libcrux-trait-opacify/.
R2  Each Rust source file should be <100 LoC; total demo <500 LoC.
R3  Mock anything that isn't the bug — there's no need to recreate
    NTT, hash chains, bit-decode, etc.
R4  Use `[@@expect_failure]` to ship the buggy demos under CI.  If
    that doesn't work for hax-extracted modules, capture the F* error
    output into README and fail-loud the build only on UNEXPECTED
    success.
R5  Keep verification budget per file under 30 s (cold).  If you blow
    the budget, simplify the spec.
R6  Reference the libcrux source locations in README so a reviewer
    can cross-reference.

═══════════════════════════════════════════════════════════════════
END-OF-SESSION REPORT
═══════════════════════════════════════════════════════════════════

REPORT one paragraph at the end:
  - Demo location (full path).
  - Total LoC across the demo crate.
  - `make demo` output (the PASS/FAIL table).
  - Any hax / F* gotchas encountered (e.g. expect_failure semantics
    on hax-extracted modules, mock-vs-real-spec impedance).
  - Recommended cleanup or next steps before publishing.
```
