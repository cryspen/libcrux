import Hax

/-! # Stubs for missing functions and instances

These fill gaps in the hax Lean backend extraction.
-/

/-! ## Bridge `core_models.ops.index.Index` → `GetElemResult`

The hax Lean backend emits `Index` instances for Rust `impl Index<I> for T`,
but translates indexing expressions `x[i]` to the `x[i]_?` syntax which
resolves via `GetElemResult`.  This generic instance bridges the two.
-/
instance instGetElemResultOfIndex
    (C : Type) (I : Type)
    [assoc : core_models.ops.index.Index.AssociatedTypes C I]
    [inst : core_models.ops.index.Index C I] :
    GetElemResult C I assoc.Output where
  getElemResult xs i := inst.index xs i

/-! ## `GetElemResult` instances for `RangeTo` and `RangeFrom`

The Hax prelude provides `GetElemResult` for `Range usize` but not for
`RangeTo` or `RangeFrom`.
-/
open core_models.ops.range in
instance RangeTo.instGetElemResultSeq {α : Type} :
    GetElemResult (rust_primitives.sequence.Seq α)
      (RangeTo usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk (0 : usize) i._end)

open core_models.ops.range in
instance RangeTo.instGetElemResultRustArray {α : Type} {n : usize} :
    GetElemResult (RustArray α n)
      (RangeTo usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk (0 : usize) i._end)

open core_models.ops.range in
instance RangeFrom.instGetElemResultSeq {α : Type} :
    GetElemResult (rust_primitives.sequence.Seq α)
      (RangeFrom usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk i.start (USize64.ofNat xs.val.size))

open core_models.ops.range in
instance RangeFrom.instGetElemResultRustArray {α : Type} {n : usize} :
    GetElemResult (RustArray α n)
      (RangeFrom usize)
      (rust_primitives.sequence.Seq α) where
  getElemResult xs i :=
    getElemResult xs (Range.mk i.start n)

/-! ## Coercion `RustArray α n` → `RustSlice α`

Hax often passes a `RustArray` where a `RustSlice` is expected (Rust does
this via auto-deref).  This coercion mirrors `array_as_slice`.
-/
attribute [local grind! .] USize64.toNat_lt_size

instance instCoeRustArraySeq {α : Type} {n : usize} :
    CoeOut (RustArray α n) (rust_primitives.sequence.Seq α) where
  coe a := ⟨a.toVec.toArray, by grind⟩

instance instCoeSeqRustArray {α : Type} {n : usize} (s : rust_primitives.sequence.Seq α) :
    CoeDep (rust_primitives.sequence.Seq α) s (RustArray α n) where
  coe := ⟨⟨s.val, sorry⟩⟩

/-! ## `core_models.num` stubs — u32 (`Impl_8`) and u64 (`Impl_9`) -/

namespace core_models.num

@[irreducible] def Impl_8.MAX : u32 := sorry

@[irreducible] def Impl_9.rotate_left (x : u64) (n : u32) : RustM u64 := sorry
@[irreducible] def Impl_9.from_le_bytes (b : RustArray u8 8) : RustM u64 := sorry
@[irreducible] def Impl_9.to_le_bytes (x : u64) : RustM (RustArray u8 8) := sorry

end core_models.num

/-! ## `rust_primitives.hax.monomorphized_update_at` — slice range update -/

namespace rust_primitives.hax.monomorphized_update_at

@[irreducible] def update_at_range {S : Type}
    (s : S) (r : core_models.ops.range.Range usize) (v : S) :
    RustM S := sorry

@[irreducible] def update_at_range_from {S : Type}
    (s : S) (r : core_models.ops.range.RangeFrom usize) (v : S) :
    RustM S := sorry

end rust_primitives.hax.monomorphized_update_at

/-! ## `hax_lib.int` — integer-from-string literal -/

namespace hax_lib.int

@[irreducible] def Impl_7._unsafe_from_str (s : String) : RustM hax_lib.int.Int := sorry

end hax_lib.int
