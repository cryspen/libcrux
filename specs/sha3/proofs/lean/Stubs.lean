import Hax
import Std.Do.Triple

/-! # Stubs for missing functions in the hacspec SHA-3 spec extraction -/

/-! ## Coercion `RustArray α n` ↔ `RustSlice α` -/

attribute [local grind! .] USize64.toNat_lt_size

instance instCoeRustArraySeq {α : Type} {n : usize} :
    CoeOut (RustArray α n) (rust_primitives.sequence.Seq α) where
  coe a := ⟨a.toVec.toArray, by grind⟩

instance instCoeSeqRustArray {α : Type} {n : usize} (s : rust_primitives.sequence.Seq α) :
    CoeDep (rust_primitives.sequence.Seq α) s (RustArray α n) where
  coe := ⟨⟨s.val, sorry⟩⟩

/-! ## `update_at_usize` for `RustSlice` (missing from Hax library) -/

-- The Hax library defines `update_at_usize` only for `RustArray α n`.
-- The extraction also calls it on `RustSlice α`. We provide a slice version
-- under a separate name; the extraction patch renames the slice calls.

attribute [local grind! .] rust_primitives.sequence.Seq.size_lt_usizeSize

@[spec]
def rust_primitives.hax.monomorphized_update_at.update_at_usize_slice {α}
    (s : RustSlice α) (i : usize) (v : α) : RustM (RustSlice α) :=
  if h : i.toNat < s.val.size then
    pure ⟨s.val.set (Fin.mk i.toNat h) v, by grind⟩
  else
    .fail .arrayOutOfBounds

/-! ## `core_models.num` stubs -/

namespace core_models.num

@[spec]
def Impl_9.rotate_left (x : u64) (n : u32) : RustM u64 :=
  pure (UInt64.ofBitVec (BitVec.rotateLeft x.toBitVec n.toNat))

@[spec]
def Impl_9.from_le_bytes (b : RustArray u8 8) : RustM u64 :=
  pure (b.toVec[0].toUInt64
  + (b.toVec[1].toUInt64 <<< 8)
  + (b.toVec[2].toUInt64 <<< 16)
  + (b.toVec[3].toUInt64 <<< 24)
  + (b.toVec[4].toUInt64 <<< 32)
  + (b.toVec[5].toUInt64 <<< 40)
  + (b.toVec[6].toUInt64 <<< 48)
  + (b.toVec[7].toUInt64 <<< 56))

@[spec]
def Impl_9.to_le_bytes (x : u64) : RustM (RustArray u8 8) :=
  pure (.ofVec #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
    (x >>> 32 % 256).toUInt8,
    (x >>> 40 % 256).toUInt8,
    (x >>> 48 % 256).toUInt8,
    (x >>> 56 % 256).toUInt8,
  ])

def Impl_8.MAX : u32 := (4294967295 : u32)

@[irreducible] def Impl_11.MAX : usize := sorry

end core_models.num

/-! ## `hacspec_sha3.createi` — array from_fn wrapper -/

namespace hacspec_sha3

@[irreducible] def createi (T : Type) (N : usize) (F : Type)
    [core_models.ops.function.Fn.AssociatedTypes F (rust_primitives.hax.Tuple1 usize)]
    [core_models.ops.function.Fn F (rust_primitives.hax.Tuple1 usize)]
    (f : F) : RustM (RustArray T N) := sorry

open Std.Do in
-- Triple-style spec for createi, usable by mvcgen via @[spec].
-- f_pure takes Nat (not Fin) to avoid proof-term construction in postconditions.
-- The bound i < N becomes a precondition VC that mvcgen generates automatically.
@[spec]
axiom createi.spec_triple (T : Type) (N : usize)
    (f : usize → RustM T) (f_pure : Nat → T)
    [inst1 : core_models.ops.function.Fn.AssociatedTypes (usize → RustM T) (rust_primitives.hax.Tuple1 usize)]
    [inst2 : core_models.ops.function.Fn (usize → RustM T) (rust_primitives.hax.Tuple1 usize)]
    (hf : ∀ (i : usize),
      ⦃ ⌜ i.toNat < N.toNat ⌝ ⦄ f i ⦃ ⇓ r => ⌜ r = f_pure i.toNat ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    createi T N (usize → RustM T) f
    ⦃ ⇓ r => ⌜ r = ⟨Vector.ofFn (fun i => f_pure i.val)⟩ ⌝ ⦄

end hacspec_sha3

-- Note: fold_range_purifies and createi_purifies (equality-based) have been removed.
-- Use mvcgen with @[spec] triples instead.
