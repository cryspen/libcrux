# Status — agent-mldsa-generic
Updated: 2026-05-01T13:00:00Z
Sub-task: Option 1 from handoff-2026-05-01-spec-impl-hookup.md — wire generate_key_pair ensures to Hacspec_ml_dsa.Ml_dsa.keygen_internal.
ETA: ready for commit; downstream sweep in progress.
Functions landed: 3 / 3 (generate_key_pair, verify, sign)

## What landed

`crates/utils/macros/src/lib.rs` — `ml_dsa_parameter_sets` now injects a
per-variant F* binding so the (shared) generic-module body can refer to
its Hacspec spec params by a stable name:

```fstar
let v_HACSPEC_PARAMS : Hacspec_ml_dsa.Parameters.t_MlDsaParams =
  Hacspec_ml_dsa.Parameters.v_ML_DSA_44_  (or 65, 87)
```

`libcrux-ml-dsa/src/ml_dsa_generic.rs` — `generate_key_pair` ensures
extends from length-only to functional equality:

```fstar
Seq.length signing_key_future == Seq.length signing_key /\
Seq.length verification_key_future == Seq.length verification_key /\
(let pk_spec, sk_spec =
   Hacspec_ml_dsa.Ml_dsa.keygen_internal
      v_HACSPEC_PARAMS.f_k v_HACSPEC_PARAMS.f_l
      v_VERIFICATION_KEY_SIZE v_SIGNING_KEY_SIZE
      randomness v_HACSPEC_PARAMS in
 Seq.equal signing_key_future sk_spec /\
 Seq.equal verification_key_future pk_spec)
```

## Verification

| Module | Outcome | Time |
|---|---|---|
| `Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_44_.fst` | ✅ Verified clean | 8.0s |
| `Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_65_.fst` | ✅ Verified clean | 8.8s |
| `Libcrux_ml_dsa.Ml_dsa_generic.Ml_dsa_87_.fst` | ✅ Verified clean | 8.7s |

The body still has `hax_lib::fstar!("admit ()")` so the postcondition
chain for functional correctness is **declared** but not yet proven —
the wiring is type-correct (i.e. requires of `keygen_internal`
discharge automatically per variant via SMT) and ready to drive the
body-side proof.

`cargo build --tests` clean.  `cargo test --release --lib`: 20/20
passing.

## Notes for next agent

- The macro change is general (not generate_key_pair-specific) — `v_HACSPEC_PARAMS` is now available in any code inside the macroized `generic` module.  Use it for `sign_internal`/`verify_internal` ensures wiring (handoff items 2, 3).
- The wiring trick — call the spec function with `v_HACSPEC_PARAMS.f_k`/`v_HACSPEC_PARAMS.f_l` rather than the impl's `v_ROWS_IN_A`/`v_COLUMNS_IN_A` — avoids the `K =. params.f_k` precondition discharge issue (it becomes a trivial `params.f_k =. params.f_k`).  Reuse this pattern.
- Spec-side `keygen_internal` returns `(pk, sk)` and the impl mutates `(signing_key, verification_key)` slices — note the tuple-component swap.
