# Held work — Phase 7c body proofs (B + B')

**Status**: HELD on branch `agent/phase-7c-serialize` (tip `1c2b0ee4f`).
NOT merged into `trait-opacify`.

**Reason**: agent B's bridge-axiom approach delivers no real verification
content (the 9 admitted SMTPat axioms are throwaway scaffolding,
discarded when `Spec.MLKEM.*` is deleted in Phase 7l).  Agent B'
analyzed the alternative — body proofs against `Hacspec_ml_kem.Serialize.*`
— and found each requires a 3-lemma chain (L1/L2/L3) of bit-vector
infrastructure that doesn't exist in the codebase.  Per-target
estimate: ~2 days; with a shared infra pass, ~2-3 days TOTAL for all
4 simple targets.

This document is the durable record of what's on the branch + the
launchpad for the eventual specialist agent that lands L1/L2/L3.

## What's on the branch

Branch tip `1c2b0ee4f` carries the following files (above the
`trait-opacify` baseline at branch-point `0f5175e8e`):

| File | Type | Lines | Content |
|---|---|---|---|
| `libcrux-ml-kem/proofs/fstar/spec/Libcrux_ml_kem.Serialize.HacspecBridge.fst` | NEW | 457 | 8 admitted-with-comment SMTPat bridge axioms + L1/L2/L3 architectural analysis + L1 stub `lemma_u16_shr_mask_eq_get_bit_nat` (admitted) |
| `libcrux-ml-kem/proofs/fstar/spec/Makefile` | EDITED | +7 | Include paths for hacspec extraction + libcrux-ml-kem + libcrux-intrinsics extraction (needed for HacspecBridge to type-check) |
| `libcrux-ml-kem/src/serialize.rs` | EDITED | ~68 | 9 brief-listed `Hacspec_ml_kem.Serialize.*` cites + 1 trivial-helper cite, all conjunctively added alongside existing `Spec.MLKEM.*` cites |

## L1 / L2 / L3 sub-lemma chain — analysis

Per agent B' (verbatim from `Libcrux_ml_kem.Serialize.HacspecBridge.fst`
inline comments):

**Spec.MLKEM.byte_encode d p**:
- Project polynomial → `t_Array nat 256` via `map_array`
- `bit_vec_of_nat_array arr d` → `bit_vec`, defined as
  `on (i) (fun i -> get_bit_nat (arr.[i/d]) (i%d))`
- `bits_to_bytes #(sz (32*d))` = `bit_vec_to_int_t_array 8 bv`

**Hacspec_ml_kem.Serialize.byte_encode v_D32 v_D256 p d**:
- Project to u16 array via `createi 256 (fun i -> p.[i].f_val)`
- `bitvector_from_bounded_ints 256 v_D256 p_raw d` =
  `createi v_Nd (fun i -> ((p_raw.[i/d] >>! (i%d)) &. mk_u16 1) =. mk_u16 1)`
- `bits_to_bytes v_D32 v_D256 bv` = `createi v_D32 (fun i ->` 8 explicit
  shifts/ORs of `bv.[8i+j]` cast to u8 `)`

Both compute FIPS-203 Algorithm 4, but at the F\* level the bit-extraction
primitives differ.  Equivalence requires three sub-lemmas:

- **L1** — `lemma_u16_shr_mask_eq_get_bit_nat`:
  `get_bit_nat n i == ((mk_u16 n >>! i) &. 1) =. 1` for `n < pow2 16`,
  `i < 16`.  **Stub committed on the branch** (admit-with-detailed-proof-skeleton).
- **L2** — bit-vector library identity:
  `bit_vec_of_int_t_array arr 8 i == get_bit (arr.[i/8]) (i%8)`.
  Likely already provable from F\*'s bitvec lib by definitional unfolding.
- **L3** — output-byte equivalence:
  for each output byte `k`, `bit_vec_to_int_t_array 8 bv k` (Spec.MLKEM
  form) equals the `createi`-with-8-shifts construction (Hacspec form).
  Plus the analogous chain for `byte_decode` (Spec uses
  `bit_vec_to_nat_array`, Hacspec uses `bitvector_to_bounded_ints`
  with `createi`-of-1-bit-ORs).

Note: no upstream uses of `bit_vec_of_nat_array` outside `Spec.MLKEM.Math.fst`,
no upstream uses of `bitvector_from_bounded_ints` outside
`Hacspec_ml_kem.Serialize.fst` — this is genuinely new infrastructure.

## What lands once L1/L2/L3 are proven

The 4 simpler bridge axioms (uncompressed serialize/deserialize +
message {de,}compress) become provable by chaining L1/L2/L3 + a final
`Seq.lemma_eq_intro` lift over the `createi` forms.  This promotes:

- `axiom_cite_serialize_uncompressed_ring_element`
- `axiom_cite_deserialize_to_uncompressed_ring_element`
- `axiom_cite_compress_then_serialize_message`
- `axiom_cite_deserialize_then_decompress_message`

…in one pass.  The 5 compress<D>-family bridges (compress_then_serialize_u/v,
deserialize_then_decompress_u/v, public-API wrapper) remain pending
Phase 7a's compress<D> chunk-commute infrastructure (a separate effort).

## Recommended specialist agent brief — when to launch

Launch when:
- Wave 2 (Phase 7a Polynomial) has landed.
- Wave 3 (Phase 7b NTT, 7d Matrix) has at least started.
- Or independently, any time — this work is orthogonal to other phases.

Brief outline:

> Specialist L1/L2/L3 — Serialize bit-vector bridge.
>
> Branch: branch off `agent/phase-7c-serialize` at tip `1c2b0ee4f`
> (DO NOT branch off trait-opacify; the agent's work depends on
> B's `HacspecBridge.fst` scaffolding).
>
> Mission: prove the 3 chained sub-lemmas L1, L2, L3 in
> `HacspecBridge.fst` (or factor them into a new
> `Libcrux_ml_kem.Serialize.BitVecBridge.fst`).  Once proven, replace
> the 4 admitted axioms (`axiom_cite_serialize_uncompressed_ring_element`,
> `axiom_cite_deserialize_to_uncompressed_ring_element`,
> `axiom_cite_compress_then_serialize_message`,
> `axiom_cite_deserialize_then_decompress_message`) with real proofs.
>
> Wall clock: ~3 days focused F\*.  Stop conditions: budget hit, or
> any of L1/L2/L3 turns out to require a model gap that's USER-lane.
>
> Useful pointers:
> - L1 stub already committed at `lemma_u16_shr_mask_eq_get_bit_nat`
>   in `HacspecBridge.fst` with a 4-step proof skeleton (calls to
>   `get_bit_shr`, `get_bit_and`, `get_bit_pow2_minus_one_u16`).
> - L2 should be ~1 hour from `BitVec.Bv` definitions.
> - L3 is the heavy lift; likely needs a generic
>   `bit_vec_to_byte_array_eq_createi_lift` lemma that's reusable
>   across both encode and decode directions.
>
> Final: replace 4 axioms with proofs, leave the 5 compress-family
> axioms in place, regression `make Libcrux_ml_kem.Serialize.fst.checked`,
> ensure no regressions to other modules.

## Branch preservation

`agent/phase-7c-serialize` MUST NOT be deleted.  The 7 commits between
`0f5175e8e` and `1c2b0ee4f` are the durable artifact.  When the
specialist work begins, branch off `1c2b0ee4f` directly.

If a future garbage-collection sweep targets unmerged agent branches,
this file is the warning to skip `agent/phase-7c-serialize`.

## File pointers

- Branch tip: `1c2b0ee4f` on `agent/phase-7c-serialize`
- Brief that produced agent B: `proofs/agent-status/agent-B-brief.md`
- Brief that produced agent B': `proofs/agent-status/agent-B-prime-brief.md`
- Agent B+B' log: `proofs/agent-status/agent-B.md` (on the branch)
- This document: `proofs/agent-status/held-work-Bprime-L123.md`
