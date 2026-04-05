
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import LibcruxStubs
import extraction.libcrux_intrinsics
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace libcrux_sha3.simd.portable

def rotate_left (LEFT : i32) (RIGHT : i32) (x : u64) : RustM u64 := do
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← ((← (LEFT +? RIGHT)) ==? (64 : i32))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  (core_models.num.Impl_9.rotate_left
    x
    (← (rust_primitives.hax.cast_op LEFT : RustM u32)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def rotate_left.spec (LEFT : i32) (RIGHT : i32) (x : u64) :
    Spec
      (requires := do
        ((← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.add
              (← (rust_primitives.hax.int.from_machine LEFT))
              (← (rust_primitives.hax.int.from_machine RIGHT))))
            (← (rust_primitives.hax.int.from_machine (64 : i32)))))
          &&? (← (RIGHT >? (0 : i32)))))
      (ensures := fun _ => pure True)
      (rotate_left (LEFT : i32) (RIGHT : i32) (x : u64)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

@[spec]
def _veor5q_u64 (a : u64) (b : u64) (c : u64) (d : u64) (e : u64) :
    RustM u64 := do
  ((← ((← ((← (a ^^^? b)) ^^^? c)) ^^^? d)) ^^^? e)

@[spec]
def _vrax1q_u64 (a : u64) (b : u64) : RustM u64 := do
  (a ^^^? (← (rotate_left ((1 : i32)) ((63 : i32)) b)))

def _vxarq_u64 (LEFT : i32) (RIGHT : i32) (a : u64) (b : u64) : RustM u64 := do
  (rotate_left (LEFT) (RIGHT) (← (a ^^^? b)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def _vxarq_u64.spec (LEFT : i32) (RIGHT : i32) (a : u64) (b : u64) :
    Spec
      (requires := do
        ((← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.add
              (← (rust_primitives.hax.int.from_machine LEFT))
              (← (rust_primitives.hax.int.from_machine RIGHT))))
            (← (rust_primitives.hax.int.from_machine (64 : i32)))))
          &&? (← (RIGHT >? (0 : i32)))))
      (ensures := fun _ => pure True)
      (_vxarq_u64 (LEFT : i32) (RIGHT : i32) (a : u64) (b : u64)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

@[spec]
def _vbcaxq_u64 (a : u64) (b : u64) (c : u64) : RustM u64 := do
  (a ^^^? (← (b &&&? (← (~? c)))))

@[spec]
def _veorq_n_u64 (a : u64) (c : u64) : RustM u64 := do (a ^^^? c)

end libcrux_sha3.simd.portable


namespace libcrux_sha3.simd.arm64

abbrev uint64x2_t : Type := libcrux_intrinsics.arm64_extract._uint64x2_t

@[spec]
def _veor5q_u64
    (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (b : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (c : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (d : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (e : libcrux_intrinsics.arm64_extract._uint64x2_t) :
    RustM libcrux_intrinsics.arm64_extract._uint64x2_t := do
  (libcrux_intrinsics.arm64_extract._veor3q_u64
    (← (libcrux_intrinsics.arm64_extract._veor3q_u64 a b c))
    d
    e)

@[spec]
def _vrax1q_u64
    (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (b : libcrux_intrinsics.arm64_extract._uint64x2_t) :
    RustM libcrux_intrinsics.arm64_extract._uint64x2_t := do
  (libcrux_intrinsics.arm64_extract._vrax1q_u64 a b)

@[spec]
def _vxarq_u64 (LEFT : i32) (RIGHT : i32)
    (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (b : libcrux_intrinsics.arm64_extract._uint64x2_t) :
    RustM libcrux_intrinsics.arm64_extract._uint64x2_t := do
  (libcrux_intrinsics.arm64_extract._vxarq_u64 (LEFT) (RIGHT) a b)

@[spec]
def _vbcaxq_u64
    (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (b : libcrux_intrinsics.arm64_extract._uint64x2_t)
    (c : libcrux_intrinsics.arm64_extract._uint64x2_t) :
    RustM libcrux_intrinsics.arm64_extract._uint64x2_t := do
  (libcrux_intrinsics.arm64_extract._vbcaxq_u64 a b c)

@[spec]
def _veorq_n_u64 (a : libcrux_intrinsics.arm64_extract._uint64x2_t) (c : u64) :
    RustM libcrux_intrinsics.arm64_extract._uint64x2_t := do
  let c : libcrux_intrinsics.arm64_extract._uint64x2_t ←
    (libcrux_intrinsics.arm64_extract._vdupq_n_u64 c);
  (libcrux_intrinsics.arm64_extract._veorq_u64 a c)

end libcrux_sha3.simd.arm64


namespace libcrux_sha3.generic_keccak.xof

--  Note: This function exists to work around a hax bug where `core::array::from_fn`
--  is extracted with an incorrect explicit type parameter `#(usize -> t_Slice u8)`
--  instead of using the typeclass-based implicit parameter `#v_F` from
--  `Core_models.Array.from_fn`.
--  See: https://github.com/cryspen/hax/issues/1920
@[spec]
def buf_to_slices (PARALLEL_LANES : usize) (RATE : usize)
    (buf : (RustArray (RustArray u8 RATE) PARALLEL_LANES)) :
    RustM (RustArray (RustSlice u8) PARALLEL_LANES) := do
  (core_models.array.from_fn
    (RustSlice u8)
    (PARALLEL_LANES)
    (usize -> RustM (RustSlice u8))
    (fun i =>
      (do
      (core_models.array.Impl_23.as_slice u8 (RATE) (← buf[i]_?)) :
      RustM (RustSlice u8))))

end libcrux_sha3.generic_keccak.xof


namespace libcrux_sha3.generic_keccak.constants

def ROUNDCONSTANTS : (RustArray u64 24) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(1 : u64),
                                (32898 : u64),
                                (9223372036854808714 : u64),
                                (9223372039002292224 : u64),
                                (32907 : u64),
                                (2147483649 : u64),
                                (9223372039002292353 : u64),
                                (9223372036854808585 : u64),
                                (138 : u64),
                                (136 : u64),
                                (2147516425 : u64),
                                (2147483658 : u64),
                                (2147516555 : u64),
                                (9223372036854775947 : u64),
                                (9223372036854808713 : u64),
                                (9223372036854808579 : u64),
                                (9223372036854808578 : u64),
                                (9223372036854775936 : u64),
                                (32778 : u64),
                                (9223372039002259466 : u64),
                                (9223372039002292353 : u64),
                                (9223372036854808704 : u64),
                                (2147483649 : u64),
                                (9223372039002292232 : u64)])))
    (by rfl)

end libcrux_sha3.generic_keccak.constants


namespace libcrux_sha3.traits

--  A Keccak Item for multiplexing arithmetic implementations.
class KeccakItem.AssociatedTypes (Self : Type) (N : usize) where
  [trait_constr_KeccakItem_i0 : core_models.clone.Clone.AssociatedTypes Self]
  [trait_constr_KeccakItem_i1 : core_models.marker.Copy.AssociatedTypes Self]

attribute [instance_reducible, instance]
  KeccakItem.AssociatedTypes.trait_constr_KeccakItem_i0

attribute [instance_reducible, instance]
  KeccakItem.AssociatedTypes.trait_constr_KeccakItem_i1

class KeccakItem (Self : Type) (N : usize)
  [associatedTypes : outParam (KeccakItem.AssociatedTypes (Self : Type) (N :
      usize))]
  where
  [trait_constr_KeccakItem_i0 : core_models.clone.Clone Self]
  [trait_constr_KeccakItem_i1 : core_models.marker.Copy Self]
  zero (Self) (N) : (rust_primitives.hax.Tuple0 -> RustM Self)
  xor5 (Self) (N) : (Self -> Self -> Self -> Self -> Self -> RustM Self)
  rotate_left1_and_xor (Self) (N) : (Self -> Self -> RustM Self)
  xor_and_rotate (Self) (N) (LEFT : i32) (RIGHT : i32) :
    (Self -> Self -> RustM Self)
  and_not_xor (Self) (N) : (Self -> Self -> Self -> RustM Self)
  xor_constant (Self) (N) : (Self -> u64 -> RustM Self)
  xor (Self) (N) : (Self -> Self -> RustM Self)

attribute [instance_reducible, instance] KeccakItem.trait_constr_KeccakItem_i0

attribute [instance_reducible, instance] KeccakItem.trait_constr_KeccakItem_i1

end libcrux_sha3.traits


namespace libcrux_sha3.simd.portable

@[reducible] instance Impl.AssociatedTypes :
  libcrux_sha3.traits.KeccakItem.AssociatedTypes u64 ((1 : usize))
  where

instance Impl : libcrux_sha3.traits.KeccakItem u64 ((1 : usize)) where
  zero := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u64))
  xor5 := fun (a : u64) (b : u64) (c : u64) (d : u64) (e : u64) => do
    (_veor5q_u64 a b c d e)
  rotate_left1_and_xor := fun (a : u64) (b : u64) => do (_vrax1q_u64 a b)
  xor_and_rotate := fun (LEFT : i32) (RIGHT : i32) (a : u64) (b : u64) => do
    (_vxarq_u64 (LEFT) (RIGHT) a b)
  and_not_xor := fun (a : u64) (b : u64) (c : u64) => do (_vbcaxq_u64 a b c)
  xor_constant := fun (a : u64) (c : u64) => do (_veorq_n_u64 a c)
  xor := fun (a : u64) (b : u64) => do (a ^^^? b)

end libcrux_sha3.simd.portable


namespace libcrux_sha3.simd.arm64

@[reducible] instance Impl.AssociatedTypes :
  libcrux_sha3.traits.KeccakItem.AssociatedTypes
  libcrux_intrinsics.arm64_extract._uint64x2_t
  ((2 : usize))
  where

instance Impl :
  libcrux_sha3.traits.KeccakItem
  libcrux_intrinsics.arm64_extract._uint64x2_t
  ((2 : usize))
  where
  zero := fun (_ : rust_primitives.hax.Tuple0) => do
    (libcrux_intrinsics.arm64_extract._vdupq_n_u64 (0 : u64))
  xor5 :=
    fun
      (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (b : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (c : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (d : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (e : libcrux_intrinsics.arm64_extract._uint64x2_t) => do
    (_veor5q_u64 a b c d e)
  rotate_left1_and_xor :=
    fun
      (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (b : libcrux_intrinsics.arm64_extract._uint64x2_t) => do
    (_vrax1q_u64 a b)
  xor_and_rotate :=
    fun (LEFT : i32) (RIGHT : i32)
      (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (b : libcrux_intrinsics.arm64_extract._uint64x2_t) => do
    (_vxarq_u64 (LEFT) (RIGHT) a b)
  and_not_xor :=
    fun
      (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (b : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (c : libcrux_intrinsics.arm64_extract._uint64x2_t) => do
    (_vbcaxq_u64 a b c)
  xor_constant :=
    fun (a : libcrux_intrinsics.arm64_extract._uint64x2_t) (c : u64) => do
    (_veorq_n_u64 a c)
  xor :=
    fun
      (a : libcrux_intrinsics.arm64_extract._uint64x2_t)
      (b : libcrux_intrinsics.arm64_extract._uint64x2_t) => do
    (libcrux_intrinsics.arm64_extract._veorq_u64 a b)

end libcrux_sha3.simd.arm64


namespace libcrux_sha3.generic_keccak.xof

--  An all zero block
@[spec]
def Impl.zero_block
    (PARALLEL_LANES : usize)
    (RATE : usize)
    (STATE : Type)
    [trait_constr_zero_block_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      STATE
      (PARALLEL_LANES)]
    [trait_constr_zero_block_i0 : libcrux_sha3.traits.KeccakItem
      STATE
      (PARALLEL_LANES)
      ]
    (_ : rust_primitives.hax.Tuple0) :
    RustM (RustArray u8 RATE) := do
  (rust_primitives.hax.repeat (0 : u8) RATE)

end libcrux_sha3.generic_keccak.xof


namespace libcrux_sha3.generic_keccak

structure KeccakState
  (N : usize)
  (T : Type)
  [trait_constr_KeccakState_associated_type_i0 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    T
    (N)]
  [trait_constr_KeccakState_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
  where
  st : (RustArray T 25)

end libcrux_sha3.generic_keccak


namespace libcrux_sha3.generic_keccak.xof

--  The internal keccak state that can also buffer inputs to absorb.
--  This is used in the general xof APIs.
structure KeccakXofState
  (PARALLEL_LANES : usize)
  (RATE : usize)
  (STATE : Type)
  [trait_constr_KeccakXofState_associated_type_i0 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    STATE
    (PARALLEL_LANES)]
  [trait_constr_KeccakXofState_i0 : libcrux_sha3.traits.KeccakItem
    STATE
    (PARALLEL_LANES)
    ]
  where
  inner : (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
  buf : (RustArray (RustArray u8 RATE) PARALLEL_LANES)
  buf_len : usize
  sponge : Bool

end libcrux_sha3.generic_keccak.xof


namespace libcrux_sha3.generic_keccak

@[instance] opaque Impl_1.AssociatedTypes
  (N : usize)
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : core_models.clone.Clone T ]
  [trait_constr_Impl_1_associated_type_i1 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    T
    (N)]
  [trait_constr_Impl_1_i1 : libcrux_sha3.traits.KeccakItem T (N) ] :
  core_models.clone.Clone.AssociatedTypes (KeccakState (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (N : usize)
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : core_models.clone.Clone T ]
  [trait_constr_Impl_1_associated_type_i1 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    T
    (N)]
  [trait_constr_Impl_1_i1 : libcrux_sha3.traits.KeccakItem T (N) ] :
  core_models.clone.Clone (KeccakState (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl.AssociatedTypes
  (N : usize)
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : core_models.marker.Copy T ]
  [trait_constr_Impl_associated_type_i1 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    T
    (N)]
  [trait_constr_Impl_i1 : libcrux_sha3.traits.KeccakItem T (N) ] :
  core_models.marker.Copy.AssociatedTypes (KeccakState (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl
  (N : usize)
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : core_models.marker.Copy T ]
  [trait_constr_Impl_associated_type_i1 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    T
    (N)]
  [trait_constr_Impl_i1 : libcrux_sha3.traits.KeccakItem T (N) ] :
  core_models.marker.Copy (KeccakState (N) T) :=
  by constructor <;> exact Inhabited.default

--  Create a new Shake128 x4 state.
@[spec]
def Impl_2.new
    (N : usize)
    (T : Type)
    [trait_constr_new_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_new_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (_ : rust_primitives.hax.Tuple0) :
    RustM (KeccakState (N) T) := do
  (pure (KeccakState.mk
    (st := (← (rust_primitives.hax.repeat
      (← (libcrux_sha3.traits.KeccakItem.zero
        T
        (N) rust_primitives.hax.Tuple0.mk))
      (25 : usize))))))

end libcrux_sha3.generic_keccak


namespace libcrux_sha3.traits

def get_ij
    (N : usize)
    (T : Type)
    [trait_constr_get_ij_associated_type_i0 : KeccakItem.AssociatedTypes T (N)]
    [trait_constr_get_ij_i0 : KeccakItem T (N) ]
    (arr : (RustArray T 25))
    (i : usize)
    (j : usize) :
    RustM T := do
  arr[(← ((← ((5 : usize) *? j)) +? i))]_?

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      get_ij.spec
      (N : usize)
      (T : Type)
      [trait_constr_get_ij_associated_type_i0 : KeccakItem.AssociatedTypes
        T
        (N)]
      [trait_constr_get_ij_i0 : KeccakItem T (N) ]
      (arr : (RustArray T 25))
      (i : usize)
      (j : usize) :
    Spec
      (requires := do ((← (i <? (5 : usize))) &&? (← (j <? (5 : usize)))))
      (ensures := fun _ => pure True)
      (get_ij
        (N : usize)
        (T : Type)
        (arr : (RustArray T 25))
        (i : usize)
        (j : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.traits


namespace libcrux_sha3.simd.arm64

@[spec]
def store_block (RATE : usize)
    (s : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25))
    (out0 : (RustSlice u8))
    (out1 : (RustSlice u8))
    (start : usize)
    (len : usize) :
    RustM (rust_primitives.hax.Tuple2 (RustSlice u8) (RustSlice u8)) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← ((← (len <=? RATE))
              &&? (← ((← (start +? len))
                <=? (← (core_models.slice.Impl.len u8 out0))))))
            &&? (← ((← (core_models.slice.Impl.len u8 out0))
              ==? (← (core_models.slice.Impl.len u8 out1)))))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let ⟨out0, out1⟩ ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (len /? (16 : usize)))
      (fun ⟨out0, out1⟩ _ => (do (pure true) : RustM Bool))
      (rust_primitives.hax.Tuple2.mk out0 out1)
      (fun ⟨out0, out1⟩ i =>
        (do
        let i0 : usize ← ((← ((2 : usize) *? i)) /? (5 : usize));
        let j0 : usize ← ((← ((2 : usize) *? i)) %? (5 : usize));
        let i1 : usize ←
          ((← ((← ((2 : usize) *? i)) +? (1 : usize))) /? (5 : usize));
        let j1 : usize ←
          ((← ((← ((2 : usize) *? i)) +? (1 : usize))) %? (5 : usize));
        let v0 : libcrux_intrinsics.arm64_extract._uint64x2_t ←
          (libcrux_intrinsics.arm64_extract._vtrn1q_u64
            (← (libcrux_sha3.traits.get_ij
              ((2 : usize))
              libcrux_intrinsics.arm64_extract._uint64x2_t s i0 j0))
            (← (libcrux_sha3.traits.get_ij
              ((2 : usize))
              libcrux_intrinsics.arm64_extract._uint64x2_t s i1 j1)));
        let v1 : libcrux_intrinsics.arm64_extract._uint64x2_t ←
          (libcrux_intrinsics.arm64_extract._vtrn2q_u64
            (← (libcrux_sha3.traits.get_ij
              ((2 : usize))
              libcrux_intrinsics.arm64_extract._uint64x2_t s i0 j0))
            (← (libcrux_sha3.traits.get_ij
              ((2 : usize))
              libcrux_intrinsics.arm64_extract._uint64x2_t s i1 j1)));
        let out0 : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out0
            (core_models.ops.range.Range.mk
              (start := (← (start +? (← ((16 : usize) *? i)))))
              (_end := (← (start
                +? (← ((16 : usize) *? (← (i +? (1 : usize)))))))))
            (← (libcrux_intrinsics.arm64_extract._vst1q_bytes_u64
              (← out0[
                (core_models.ops.range.Range.mk
                  (start := (← (start +? (← ((16 : usize) *? i)))))
                  (_end := (← (start
                    +? (← ((16 : usize) *? (← (i +? (1 : usize)))))))))
                ]_?)
              v0)));
        let out1 : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out1
            (core_models.ops.range.Range.mk
              (start := (← (start +? (← ((16 : usize) *? i)))))
              (_end := (← (start
                +? (← ((16 : usize) *? (← (i +? (1 : usize)))))))))
            (← (libcrux_intrinsics.arm64_extract._vst1q_bytes_u64
              (← out1[
                (core_models.ops.range.Range.mk
                  (start := (← (start +? (← ((16 : usize) *? i)))))
                  (_end := (← (start
                    +? (← ((16 : usize) *? (← (i +? (1 : usize)))))))))
                ]_?)
              v1)));
        (pure (rust_primitives.hax.Tuple2.mk out0 out1)) :
        RustM (rust_primitives.hax.Tuple2 (RustSlice u8) (RustSlice u8)))));
  let remaining : usize ← (len %? (16 : usize));
  let ⟨out0, out1⟩ ←
    if (← (remaining >? (8 : usize))) then do
      let out0_tmp : (RustArray u8 16) ←
        (rust_primitives.hax.repeat (0 : u8) (16 : usize));
      let out1_tmp : (RustArray u8 16) ←
        (rust_primitives.hax.repeat (0 : u8) (16 : usize));
      let i : usize ← ((2 : usize) *? (← (len /? (16 : usize))));
      let i0 : usize ← (i /? (5 : usize));
      let j0 : usize ← (i %? (5 : usize));
      let i1 : usize ← ((← (i +? (1 : usize))) /? (5 : usize));
      let j1 : usize ← ((← (i +? (1 : usize))) %? (5 : usize));
      let v0 : libcrux_intrinsics.arm64_extract._uint64x2_t ←
        (libcrux_intrinsics.arm64_extract._vtrn1q_u64
          (← (libcrux_sha3.traits.get_ij
            ((2 : usize))
            libcrux_intrinsics.arm64_extract._uint64x2_t s i0 j0))
          (← (libcrux_sha3.traits.get_ij
            ((2 : usize))
            libcrux_intrinsics.arm64_extract._uint64x2_t s i1 j1)));
      let v1 : libcrux_intrinsics.arm64_extract._uint64x2_t ←
        (libcrux_intrinsics.arm64_extract._vtrn2q_u64
          (← (libcrux_sha3.traits.get_ij
            ((2 : usize))
            libcrux_intrinsics.arm64_extract._uint64x2_t s i0 j0))
          (← (libcrux_sha3.traits.get_ij
            ((2 : usize))
            libcrux_intrinsics.arm64_extract._uint64x2_t s i1 j1)));
      let out0_tmp : (RustArray u8 16) ←
        (libcrux_intrinsics.arm64_extract._vst1q_bytes_u64 out0_tmp v0);
      let out1_tmp : (RustArray u8 16) ←
        (libcrux_intrinsics.arm64_extract._vst1q_bytes_u64 out1_tmp v1);
      let out0 : (RustSlice u8) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          out0
          (core_models.ops.range.Range.mk
            (start := (← ((← (start +? len)) -? remaining)))
            (_end := (← (start +? len))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← out0[
              (core_models.ops.range.Range.mk
                (start := (← ((← (start +? len)) -? remaining)))
                (_end := (← (start +? len))))
              ]_?)
            (← out0_tmp[
              (core_models.ops.range.Range.mk
                (start := (0 : usize))
                (_end := remaining))
              ]_?))));
      let out1 : (RustSlice u8) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          out1
          (core_models.ops.range.Range.mk
            (start := (← ((← (start +? len)) -? remaining)))
            (_end := (← (start +? len))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← out1[
              (core_models.ops.range.Range.mk
                (start := (← ((← (start +? len)) -? remaining)))
                (_end := (← (start +? len))))
              ]_?)
            (← out1_tmp[
              (core_models.ops.range.Range.mk
                (start := (0 : usize))
                (_end := remaining))
              ]_?))));
      (pure (rust_primitives.hax.Tuple2.mk out0 out1))
    else do
      if (← (remaining >? (0 : usize))) then do
        let out01 : (RustArray u8 16) ←
          (rust_primitives.hax.repeat (0 : u8) (16 : usize));
        let i : usize ← ((2 : usize) *? (← (len /? (16 : usize))));
        let out01 : (RustArray u8 16) ←
          (libcrux_intrinsics.arm64_extract._vst1q_bytes_u64
            out01
            (← (libcrux_sha3.traits.get_ij
              ((2 : usize))
              libcrux_intrinsics.arm64_extract._uint64x2_t
              s
              (← (i /? (5 : usize)))
              (← (i %? (5 : usize))))));
        let out0 : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out0
            (core_models.ops.range.Range.mk
              (start := (← ((← (start +? len)) -? remaining)))
              (_end := (← (start +? len))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out0[
                (core_models.ops.range.Range.mk
                  (start := (← ((← (start +? len)) -? remaining)))
                  (_end := (← (start +? len))))
                ]_?)
              (← out01[
                (core_models.ops.range.Range.mk
                  (start := (0 : usize))
                  (_end := remaining))
                ]_?))));
        let out1 : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out1
            (core_models.ops.range.Range.mk
              (start := (← ((← (start +? len)) -? remaining)))
              (_end := (← (start +? len))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out1[
                (core_models.ops.range.Range.mk
                  (start := (← ((← (start +? len)) -? remaining)))
                  (_end := (← (start +? len))))
                ]_?)
              (← out01[
                (core_models.ops.range.Range.mk
                  (start := (8 : usize))
                  (_end := (← ((8 : usize) +? remaining))))
                ]_?))));
        (pure (rust_primitives.hax.Tuple2.mk out0 out1))
      else do
        (pure (rust_primitives.hax.Tuple2.mk out0 out1));
  (pure (rust_primitives.hax.Tuple2.mk out0 out1))

end libcrux_sha3.simd.arm64


namespace libcrux_sha3.generic_keccak

@[reducible] instance Impl_3.AssociatedTypes
  (N : usize)
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    T
    (N)]
  [trait_constr_Impl_3_i0 : libcrux_sha3.traits.KeccakItem T (N) ] :
  core_models.ops.index.Index.AssociatedTypes
  (KeccakState (N) T)
  (rust_primitives.hax.Tuple2 usize usize)
  where
  Output := T

instance Impl_3
  (N : usize)
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    libcrux_sha3.traits.KeccakItem.AssociatedTypes
    T
    (N)]
  [trait_constr_Impl_3_i0 : libcrux_sha3.traits.KeccakItem T (N) ] :
  core_models.ops.index.Index
  (KeccakState (N) T)
  (rust_primitives.hax.Tuple2 usize usize)
  where
  index :=
    fun
      (self : (KeccakState (N) T))
      (index : (rust_primitives.hax.Tuple2 usize usize)) => do
    (libcrux_sha3.traits.get_ij (N) T
      (KeccakState.st self)
      (rust_primitives.hax.Tuple2._0 index)
      (rust_primitives.hax.Tuple2._1 index))

@[spec]
def Impl_2.theta
    (N : usize)
    (T : Type)
    [trait_constr_theta_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_theta_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T)) :
    RustM (rust_primitives.hax.Tuple2 (KeccakState (N) T) (RustArray T 5)) := do
  let c : (RustArray T 5) :=
    (RustArray.ofVec #v[(← (libcrux_sha3.traits.KeccakItem.xor5
                            T
                            (N)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (0 : usize)
                                (0 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (1 : usize)
                                (0 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (2 : usize)
                                (0 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (3 : usize)
                                (0 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (4 : usize)
                                (0 : usize))
                              ]_?))),
                          (← (libcrux_sha3.traits.KeccakItem.xor5
                            T
                            (N)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (0 : usize)
                                (1 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (1 : usize)
                                (1 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (2 : usize)
                                (1 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (3 : usize)
                                (1 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (4 : usize)
                                (1 : usize))
                              ]_?))),
                          (← (libcrux_sha3.traits.KeccakItem.xor5
                            T
                            (N)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (0 : usize)
                                (2 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (1 : usize)
                                (2 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (2 : usize)
                                (2 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (3 : usize)
                                (2 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (4 : usize)
                                (2 : usize))
                              ]_?))),
                          (← (libcrux_sha3.traits.KeccakItem.xor5
                            T
                            (N)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (0 : usize)
                                (3 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (1 : usize)
                                (3 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (2 : usize)
                                (3 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (3 : usize)
                                (3 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (4 : usize)
                                (3 : usize))
                              ]_?))),
                          (← (libcrux_sha3.traits.KeccakItem.xor5
                            T
                            (N)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (0 : usize)
                                (4 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (1 : usize)
                                (4 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (2 : usize)
                                (4 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (3 : usize)
                                (4 : usize))
                              ]_?)
                            (← self[
                              (rust_primitives.hax.Tuple2.mk
                                (4 : usize)
                                (4 : usize))
                              ]_?)))]);
  let hax_temp_output : (RustArray T 5) :=
    (RustArray.ofVec #v[(← (libcrux_sha3.traits.KeccakItem.rotate_left1_and_xor
                            T
                            (N)
                            (← c[
                              (← ((← ((0 : usize) +? (4 : usize)))
                                %? (5 : usize)))
                              ]_?)
                            (← c[
                              (← ((← ((0 : usize) +? (1 : usize)))
                                %? (5 : usize)))
                              ]_?))),
                          (←
                          (libcrux_sha3.traits.KeccakItem.rotate_left1_and_xor
                            T
                            (N)
                            (← c[
                              (← ((← ((1 : usize) +? (4 : usize)))
                                %? (5 : usize)))
                              ]_?)
                            (← c[
                              (← ((← ((1 : usize) +? (1 : usize)))
                                %? (5 : usize)))
                              ]_?))),
                          (←
                          (libcrux_sha3.traits.KeccakItem.rotate_left1_and_xor
                            T
                            (N)
                            (← c[
                              (← ((← ((2 : usize) +? (4 : usize)))
                                %? (5 : usize)))
                              ]_?)
                            (← c[
                              (← ((← ((2 : usize) +? (1 : usize)))
                                %? (5 : usize)))
                              ]_?))),
                          (←
                          (libcrux_sha3.traits.KeccakItem.rotate_left1_and_xor
                            T
                            (N)
                            (← c[
                              (← ((← ((3 : usize) +? (4 : usize)))
                                %? (5 : usize)))
                              ]_?)
                            (← c[
                              (← ((← ((3 : usize) +? (1 : usize)))
                                %? (5 : usize)))
                              ]_?))),
                          (←
                          (libcrux_sha3.traits.KeccakItem.rotate_left1_and_xor
                            T
                            (N)
                            (← c[
                              (← ((← ((4 : usize) +? (4 : usize)))
                                %? (5 : usize)))
                              ]_?)
                            (← c[
                              (← ((← ((4 : usize) +? (1 : usize)))
                                %? (5 : usize)))
                              ]_?)))]);
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end libcrux_sha3.generic_keccak


namespace libcrux_sha3.traits

def set_ij
    (N : usize)
    (T : Type)
    [trait_constr_set_ij_associated_type_i0 : KeccakItem.AssociatedTypes T (N)]
    [trait_constr_set_ij_i0 : KeccakItem T (N) ]
    (arr : (RustArray T 25))
    (i : usize)
    (j : usize)
    (value : T) :
    RustM (RustArray T 25) := do
  let arr : (RustArray T 25) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      arr
      (← ((← ((5 : usize) *? j)) +? i))
      value);
  (pure arr)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      set_ij.spec
      (N : usize)
      (T : Type)
      [trait_constr_set_ij_associated_type_i0 : KeccakItem.AssociatedTypes
        T
        (N)]
      [trait_constr_set_ij_i0 : KeccakItem T (N) ]
      (arr : (RustArray T 25))
      (i : usize)
      (j : usize)
      (value : T) :
    Spec
      (requires := do ((← (i <? (5 : usize))) &&? (← (j <? (5 : usize)))))
      (ensures := fun _ => pure True)
      (set_ij
        (N : usize)
        (T : Type)
        (arr : (RustArray T 25))
        (i : usize)
        (j : usize)
        (value : T)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.traits


namespace libcrux_sha3.simd.arm64

@[spec]
def load_block (RATE : usize)
    (s : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25))
    (blocks : (RustArray (RustSlice u8) 2))
    (offset : usize) :
    RustM (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← ((← (RATE
                <=? (← (core_models.slice.Impl.len u8
                  (← blocks[(0 : usize)]_?)))))
              &&? (← ((← (RATE %? (8 : usize))) ==? (0 : usize)))))
            &&? (← ((← (core_models.slice.Impl.len u8
                (← blocks[(0 : usize)]_?)))
              ==? (← (core_models.slice.Impl.len u8
                (← blocks[(1 : usize)]_?))))))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let s : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (RATE /? (16 : usize)))
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s i =>
        (do
        let start : usize ← (offset +? (← ((16 : usize) *? i)));
        let v0 : libcrux_intrinsics.arm64_extract._uint64x2_t ←
          (libcrux_intrinsics.arm64_extract._vld1q_bytes_u64
            (← (← blocks[(0 : usize)]_?)[
              (core_models.ops.range.Range.mk
                (start := start)
                (_end := (← (start +? (16 : usize)))))
              ]_?));
        let v1 : libcrux_intrinsics.arm64_extract._uint64x2_t ←
          (libcrux_intrinsics.arm64_extract._vld1q_bytes_u64
            (← (← blocks[(1 : usize)]_?)[
              (core_models.ops.range.Range.mk
                (start := start)
                (_end := (← (start +? (16 : usize)))))
              ]_?));
        let i0 : usize ← ((← ((2 : usize) *? i)) /? (5 : usize));
        let j0 : usize ← ((← ((2 : usize) *? i)) %? (5 : usize));
        let i1 : usize ←
          ((← ((← ((2 : usize) *? i)) +? (1 : usize))) /? (5 : usize));
        let j1 : usize ←
          ((← ((← ((2 : usize) *? i)) +? (1 : usize))) %? (5 : usize));
        let s : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) ←
          (libcrux_sha3.traits.set_ij
            ((2 : usize))
            libcrux_intrinsics.arm64_extract._uint64x2_t
            s
            i0
            j0
            (← (libcrux_intrinsics.arm64_extract._veorq_u64
              (← (libcrux_sha3.traits.get_ij
                ((2 : usize))
                libcrux_intrinsics.arm64_extract._uint64x2_t s i0 j0))
              (← (libcrux_intrinsics.arm64_extract._vtrn1q_u64 v0 v1)))));
        let s : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) ←
          (libcrux_sha3.traits.set_ij
            ((2 : usize))
            libcrux_intrinsics.arm64_extract._uint64x2_t
            s
            i1
            j1
            (← (libcrux_intrinsics.arm64_extract._veorq_u64
              (← (libcrux_sha3.traits.get_ij
                ((2 : usize))
                libcrux_intrinsics.arm64_extract._uint64x2_t s i1 j1))
              (← (libcrux_intrinsics.arm64_extract._vtrn2q_u64 v0 v1)))));
        (pure s) :
        RustM (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25))));
  let s : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) ←
    if (← ((← (RATE %? (16 : usize))) !=? (0 : usize))) then do
      let i : usize ← ((← (RATE /? (8 : usize))) -? (1 : usize));
      let u : (RustArray u64 2) ←
        (rust_primitives.hax.repeat (0 : u64) (2 : usize));
      let start : usize ← ((← (offset +? RATE)) -? (8 : usize));
      let u : (RustArray u64 2) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          u
          (0 : usize)
          (← (core_models.num.Impl_9.from_le_bytes
            (← (core_models.result.Impl.unwrap
              (RustArray u8 8)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 8)
                (← (← blocks[(0 : usize)]_?)[
                  (core_models.ops.range.Range.mk
                    (start := start)
                    (_end := (← (start +? (8 : usize)))))
                  ]_?))))))));
      let u : (RustArray u64 2) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          u
          (1 : usize)
          (← (core_models.num.Impl_9.from_le_bytes
            (← (core_models.result.Impl.unwrap
              (RustArray u8 8)
              core_models.array.TryFromSliceError
              (← (core_models.convert.TryInto.try_into
                (RustSlice u8)
                (RustArray u8 8)
                (← (← blocks[(1 : usize)]_?)[
                  (core_models.ops.range.Range.mk
                    (start := start)
                    (_end := (← (start +? (8 : usize)))))
                  ]_?))))))));
      let uvec : libcrux_intrinsics.arm64_extract._uint64x2_t ←
        (libcrux_intrinsics.arm64_extract._vld1q_u64
          (← (rust_primitives.unsize u)));
      let s : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) ←
        (libcrux_sha3.traits.set_ij
          ((2 : usize))
          libcrux_intrinsics.arm64_extract._uint64x2_t
          s
          (← (i /? (5 : usize)))
          (← (i %? (5 : usize)))
          (← (libcrux_intrinsics.arm64_extract._veorq_u64
            (← (libcrux_sha3.traits.get_ij
              ((2 : usize))
              libcrux_intrinsics.arm64_extract._uint64x2_t
              s
              (← (i /? (5 : usize)))
              (← (i %? (5 : usize)))))
            uvec)));
      (pure s)
    else do
      (pure s);
  (pure s)

@[spec]
def load_last (RATE : usize) (DELIMITER : u8)
    (state : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25))
    (blocks : (RustArray (RustSlice u8) 2))
    (offset : usize)
    (len : usize) :
    RustM (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← ((← (offset +? len))
              <=? (← (core_models.slice.Impl.len u8
                (← blocks[(0 : usize)]_?)))))
            &&? (← ((← (core_models.slice.Impl.len u8
                (← blocks[(0 : usize)]_?)))
              ==? (← (core_models.slice.Impl.len u8
                (← blocks[(1 : usize)]_?))))))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let buffer0 : (RustArray u8 RATE) ←
    (rust_primitives.hax.repeat (0 : u8) RATE);
  let buffer0 : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range
      buffer0
      (core_models.ops.range.Range.mk (start := (0 : usize)) (_end := len))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← buffer0[
          (core_models.ops.range.Range.mk (start := (0 : usize)) (_end := len))
          ]_?)
        (← (← blocks[(0 : usize)]_?)[
          (core_models.ops.range.Range.mk
            (start := offset)
            (_end := (← (offset +? len))))
          ]_?))));
  let buffer0 : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      buffer0
      len
      DELIMITER);
  let buffer0 : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      buffer0
      (← (RATE -? (1 : usize)))
      (← ((← buffer0[(← (RATE -? (1 : usize)))]_?) |||? (128 : u8))));
  let buffer1 : (RustArray u8 RATE) ←
    (rust_primitives.hax.repeat (0 : u8) RATE);
  let buffer1 : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range
      buffer1
      (core_models.ops.range.Range.mk (start := (0 : usize)) (_end := len))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← buffer1[
          (core_models.ops.range.Range.mk (start := (0 : usize)) (_end := len))
          ]_?)
        (← (← blocks[(1 : usize)]_?)[
          (core_models.ops.range.Range.mk
            (start := offset)
            (_end := (← (offset +? len))))
          ]_?))));
  let buffer1 : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      buffer1
      len
      DELIMITER);
  let buffer1 : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      buffer1
      (← (RATE -? (1 : usize)))
      (← ((← buffer1[(← (RATE -? (1 : usize)))]_?) |||? (128 : u8))));
  let state : (RustArray libcrux_intrinsics.arm64_extract._uint64x2_t 25) ←
    (load_block (RATE)
      state
      (RustArray.ofVec #v[(← (rust_primitives.unsize buffer0)),
                            (← (rust_primitives.unsize buffer1))])
      (0 : usize));
  (pure state)

end libcrux_sha3.simd.arm64


namespace libcrux_sha3.generic_keccak

--  Set element `[i, j] = v`.
def Impl_2.set
    (N : usize)
    (T : Type)
    [trait_constr_set_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_set_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (i : usize)
    (j : usize)
    (v : T) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) :=
    {self
    with st := (← (libcrux_sha3.traits.set_ij (N) T
      (KeccakState.st self)
      i
      j
      v))};
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_2.set.spec
      (N : usize)
      (T : Type)
      [trait_constr_set_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        T
        (N)]
      [trait_constr_set_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
      (self : (KeccakState (N) T))
      (i : usize)
      (j : usize)
      (v : T) :
    Spec
      (requires := do ((← (i <? (5 : usize))) &&? (← (j <? (5 : usize)))))
      (ensures := fun _ => pure True)
      (Impl_2.set
        (N : usize)
        (T : Type)
        (self : (KeccakState (N) T))
        (i : usize)
        (j : usize)
        (v : T)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

@[spec]
def Impl_2.rho_0
    (N : usize)
    (T : Type)
    [trait_constr_rho_0_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_rho_0_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (t : (RustArray T 5)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (0 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor
        T
        (N)
        (← self[(rust_primitives.hax.Tuple2.mk (0 : usize) (0 : usize))]_?)
        (← t[(0 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (0 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((36 : i32)) ((28 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (1 : usize) (0 : usize))]_?)
        (← t[(0 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (0 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((3 : i32)) ((61 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (2 : usize) (0 : usize))]_?)
        (← t[(0 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (0 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((41 : i32)) ((23 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (3 : usize) (0 : usize))]_?)
        (← t[(0 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (0 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((18 : i32)) ((46 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (4 : usize) (0 : usize))]_?)
        (← t[(0 : usize)]_?))));
  (pure self)

@[spec]
def Impl_2.rho_1
    (N : usize)
    (T : Type)
    [trait_constr_rho_1_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_rho_1_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (t : (RustArray T 5)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (1 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((1 : i32)) ((63 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (0 : usize) (1 : usize))]_?)
        (← t[(1 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (1 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((44 : i32)) ((20 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (1 : usize) (1 : usize))]_?)
        (← t[(1 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (1 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((10 : i32)) ((54 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (2 : usize) (1 : usize))]_?)
        (← t[(1 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (1 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((45 : i32)) ((19 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (3 : usize) (1 : usize))]_?)
        (← t[(1 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (1 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((2 : i32)) ((62 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (4 : usize) (1 : usize))]_?)
        (← t[(1 : usize)]_?))));
  (pure self)

@[spec]
def Impl_2.rho_2
    (N : usize)
    (T : Type)
    [trait_constr_rho_2_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_rho_2_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (t : (RustArray T 5)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (2 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((62 : i32)) ((2 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (0 : usize) (2 : usize))]_?)
        (← t[(2 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (2 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((6 : i32)) ((58 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (1 : usize) (2 : usize))]_?)
        (← t[(2 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (2 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((43 : i32)) ((21 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (2 : usize) (2 : usize))]_?)
        (← t[(2 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (2 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((15 : i32)) ((49 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (3 : usize) (2 : usize))]_?)
        (← t[(2 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (2 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((61 : i32)) ((3 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (4 : usize) (2 : usize))]_?)
        (← t[(2 : usize)]_?))));
  (pure self)

@[spec]
def Impl_2.rho_3
    (N : usize)
    (T : Type)
    [trait_constr_rho_3_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_rho_3_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (t : (RustArray T 5)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (3 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((28 : i32)) ((36 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (0 : usize) (3 : usize))]_?)
        (← t[(3 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (3 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((55 : i32)) ((9 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (1 : usize) (3 : usize))]_?)
        (← t[(3 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (3 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((25 : i32)) ((39 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (2 : usize) (3 : usize))]_?)
        (← t[(3 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (3 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((21 : i32)) ((43 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (3 : usize) (3 : usize))]_?)
        (← t[(3 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (3 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((56 : i32)) ((8 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (4 : usize) (3 : usize))]_?)
        (← t[(3 : usize)]_?))));
  (pure self)

@[spec]
def Impl_2.rho_4
    (N : usize)
    (T : Type)
    [trait_constr_rho_4_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_rho_4_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (t : (RustArray T 5)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (4 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((27 : i32)) ((37 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (0 : usize) (4 : usize))]_?)
        (← t[(4 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (4 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((20 : i32)) ((44 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (1 : usize) (4 : usize))]_?)
        (← t[(4 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (4 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((39 : i32)) ((25 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (2 : usize) (4 : usize))]_?)
        (← t[(4 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (4 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((8 : i32)) ((56 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (3 : usize) (4 : usize))]_?)
        (← t[(4 : usize)]_?))));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (4 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_and_rotate
        T
        (N) ((14 : i32)) ((50 : i32))
        (← self[(rust_primitives.hax.Tuple2.mk (4 : usize) (4 : usize))]_?)
        (← t[(4 : usize)]_?))));
  (pure self)

@[spec]
def Impl_2.rho
    (N : usize)
    (T : Type)
    [trait_constr_rho_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_rho_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (t : (RustArray T 5)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ← (Impl_2.rho_0 (N) T self t);
  let self : (KeccakState (N) T) ← (Impl_2.rho_1 (N) T self t);
  let self : (KeccakState (N) T) ← (Impl_2.rho_2 (N) T self t);
  let self : (KeccakState (N) T) ← (Impl_2.rho_3 (N) T self t);
  let self : (KeccakState (N) T) ← (Impl_2.rho_4 (N) T self t);
  (pure self)

@[spec]
def Impl_2.pi_0
    (N : usize)
    (T : Type)
    [trait_constr_pi_0_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_pi_0_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (old : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (0 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (0 : usize) (3 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (0 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (0 : usize) (1 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (0 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (0 : usize) (4 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (0 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (0 : usize) (2 : usize))]_?));
  (pure self)

@[spec]
def Impl_2.pi_1
    (N : usize)
    (T : Type)
    [trait_constr_pi_1_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_pi_1_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (old : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (1 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (1 : usize) (1 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (1 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (1 : usize) (4 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (1 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (1 : usize) (2 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (1 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (1 : usize) (0 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (1 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (1 : usize) (3 : usize))]_?));
  (pure self)

@[spec]
def Impl_2.pi_2
    (N : usize)
    (T : Type)
    [trait_constr_pi_2_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_pi_2_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (old : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (2 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (2 : usize) (2 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (2 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (2 : usize) (0 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (2 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (2 : usize) (3 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (2 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (2 : usize) (1 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (2 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (2 : usize) (4 : usize))]_?));
  (pure self)

@[spec]
def Impl_2.pi_3
    (N : usize)
    (T : Type)
    [trait_constr_pi_3_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_pi_3_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (old : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (3 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (3 : usize) (3 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (3 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (3 : usize) (1 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (3 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (3 : usize) (4 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (3 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (3 : usize) (2 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (3 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (3 : usize) (0 : usize))]_?));
  (pure self)

@[spec]
def Impl_2.pi_4
    (N : usize)
    (T : Type)
    [trait_constr_pi_4_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_pi_4_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (old : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (4 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (4 : usize) (4 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (1 : usize)
      (4 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (4 : usize) (2 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (2 : usize)
      (4 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (4 : usize) (0 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (3 : usize)
      (4 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (4 : usize) (3 : usize))]_?));
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (4 : usize)
      (4 : usize)
      (← old[(rust_primitives.hax.Tuple2.mk (4 : usize) (1 : usize))]_?));
  (pure self)

@[spec]
def Impl_2.pi
    (N : usize)
    (T : Type)
    [trait_constr_pi_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_pi_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let old : (KeccakState (N) T) := self;
  let self : (KeccakState (N) T) ← (Impl_2.pi_0 (N) T self old);
  let self : (KeccakState (N) T) ← (Impl_2.pi_1 (N) T self old);
  let self : (KeccakState (N) T) ← (Impl_2.pi_2 (N) T self old);
  let self : (KeccakState (N) T) ← (Impl_2.pi_3 (N) T self old);
  let self : (KeccakState (N) T) ← (Impl_2.pi_4 (N) T self old);
  (pure self)

@[spec]
def Impl_2.chi
    (N : usize)
    (T : Type)
    [trait_constr_chi_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_chi_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let old : (KeccakState (N) T) := self;
  let self : (KeccakState (N) T) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (5 : usize)
      (fun self _ => (do (pure true) : RustM Bool))
      self
      (fun self i =>
        (do
        (rust_primitives.hax.folds.fold_range
          (0 : usize)
          (5 : usize)
          (fun self _ => (do (pure true) : RustM Bool))
          self
          (fun self j =>
            (do
            (Impl_2.set (N) T
              self
              i
              j
              (← (libcrux_sha3.traits.KeccakItem.and_not_xor
                T
                (N)
                (← self[(rust_primitives.hax.Tuple2.mk i j)]_?)
                (← old[
                  (rust_primitives.hax.Tuple2.mk
                    i
                    (← ((← (j +? (2 : usize))) %? (5 : usize))))
                  ]_?)
                (← old[
                  (rust_primitives.hax.Tuple2.mk
                    i
                    (← ((← (j +? (1 : usize))) %? (5 : usize))))
                  ]_?)))) :
            RustM (KeccakState (N) T)))) :
        RustM (KeccakState (N) T))));
  (pure self)

def Impl_2.iota
    (N : usize)
    (T : Type)
    [trait_constr_iota_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_iota_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T))
    (i : usize) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (Impl_2.set (N) T
      self
      (0 : usize)
      (0 : usize)
      (← (libcrux_sha3.traits.KeccakItem.xor_constant
        T
        (N)
        (← self[(rust_primitives.hax.Tuple2.mk (0 : usize) (0 : usize))]_?)
        (← libcrux_sha3.generic_keccak.constants.ROUNDCONSTANTS[i]_?))));
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_2.iota.spec
      (N : usize)
      (T : Type)
      [trait_constr_iota_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        T
        (N)]
      [trait_constr_iota_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
      (self : (KeccakState (N) T))
      (i : usize) :
    Spec
      (requires := do
        (i
          <? (← (core_models.slice.Impl.len u64
            (← (rust_primitives.unsize
              libcrux_sha3.generic_keccak.constants.ROUNDCONSTANTS))))))
      (ensures := fun _ => pure True)
      (Impl_2.iota
        (N : usize)
        (T : Type)
        (self : (KeccakState (N) T))
        (i : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

@[spec]
def Impl_2.keccakf1600
    (N : usize)
    (T : Type)
    [trait_constr_keccakf1600_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_keccakf1600_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    (self : (KeccakState (N) T)) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (24 : usize)
      (fun self _ => (do (pure true) : RustM Bool))
      self
      (fun self i =>
        (do
        let ⟨tmp0, out⟩ ← (Impl_2.theta (N) T self);
        let self : (KeccakState (N) T) := tmp0;
        let t : (RustArray T 5) := out;
        let self : (KeccakState (N) T) ← (Impl_2.rho (N) T self t);
        let self : (KeccakState (N) T) ← (Impl_2.pi (N) T self);
        let self : (KeccakState (N) T) ← (Impl_2.chi (N) T self);
        let self : (KeccakState (N) T) ← (Impl_2.iota (N) T self i);
        (pure self) :
        RustM (KeccakState (N) T))));
  (pure self)

end libcrux_sha3.generic_keccak


namespace libcrux_sha3.traits

--  Trait to squeeze bytes out of the state.
-- 
--  Note that this is implemented for each platform (1, 2, 4) because hax can't
--  handle the mutability required for a generic implementation.
-- 
--  Store blocks `N = 2`
class Squeeze2.AssociatedTypes (Self : Type) (T : Type) where
  [trait_constr_Squeeze2_i0 : KeccakItem.AssociatedTypes T ((2 : usize))]

attribute [instance_reducible, instance]
  Squeeze2.AssociatedTypes.trait_constr_Squeeze2_i0

class Squeeze2 (Self : Type) (T : Type)
  [associatedTypes : outParam (Squeeze2.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  [trait_constr_Squeeze2_i0 : KeccakItem T ((2 : usize))]
  squeeze2 (Self) (T) (RATE : usize) :
    (Self ->
    (RustSlice u8) ->
    (RustSlice u8) ->
    usize ->
    usize ->
    RustM (rust_primitives.hax.Tuple2 (RustSlice u8) (RustSlice u8)))

attribute [instance_reducible, instance] Squeeze2.trait_constr_Squeeze2_i0

end libcrux_sha3.traits


namespace libcrux_sha3.simd.arm64

@[reducible] instance Impl_2.AssociatedTypes :
  libcrux_sha3.traits.Squeeze2.AssociatedTypes
  (libcrux_sha3.generic_keccak.KeccakState
    ((2 : usize))
    libcrux_intrinsics.arm64_extract._uint64x2_t)
  libcrux_intrinsics.arm64_extract._uint64x2_t
  where

instance Impl_2 :
  libcrux_sha3.traits.Squeeze2
  (libcrux_sha3.generic_keccak.KeccakState
    ((2 : usize))
    libcrux_intrinsics.arm64_extract._uint64x2_t)
  libcrux_intrinsics.arm64_extract._uint64x2_t
  where
  squeeze2 :=
    fun (RATE : usize)
      (self :
      (libcrux_sha3.generic_keccak.KeccakState
        ((2 : usize))
        libcrux_intrinsics.arm64_extract._uint64x2_t))
      (out0 : (RustSlice u8))
      (out1 : (RustSlice u8))
      (start : usize)
      (len : usize) => do
    let ⟨tmp0, tmp1⟩ ←
      (store_block (RATE)
        (libcrux_sha3.generic_keccak.KeccakState.st self)
        out0
        out1
        start
        len);
    let out0 : (RustSlice u8) := tmp0;
    let out1 : (RustSlice u8) := tmp1;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure (rust_primitives.hax.Tuple2.mk out0 out1))

end libcrux_sha3.simd.arm64


namespace libcrux_sha3

--  Size in bytes of a SHA3 224 digest.
def SHA3_224_DIGEST_SIZE : usize := (28 : usize)

--  Size in bytes of a SHA3 256 digest.
def SHA3_256_DIGEST_SIZE : usize := (32 : usize)

--  Size in bytes of a SHA3 2384 digest.
def SHA3_384_DIGEST_SIZE : usize := (48 : usize)

--  Size in bytes of a SHA3 512 digest.
def SHA3_512_DIGEST_SIZE : usize := (64 : usize)

end libcrux_sha3


namespace libcrux_sha3.proof_utils

--  Checks if all slices in an array have the same length.
@[spec]
def slices_same_len (N : usize) (slices : (RustArray (RustSlice u8) N)) :
    RustM hax_lib.prop.Prop :=
  pure (∀ (i j : Fin N.toNat), slices.toVec[i].val.size = slices.toVec[j].val.size)

@[spec]
def valid_rate (rate : usize) : RustM Bool := do
  ((← ((← ((← (rate !=? (0 : usize))) &&? (← (rate <=? (200 : usize)))))
      &&? (← ((← (rate %? (8 : usize))) ==? (0 : usize)))))
    &&? (← ((← ((← (rate %? (32 : usize))) ==? (8 : usize)))
      ||? (← ((← (rate %? (32 : usize))) ==? (16 : usize))))))

end libcrux_sha3.proof_utils


namespace libcrux_sha3.simd.portable

def load_block (RATE : usize)
    (state : (RustArray u64 25))
    (blocks : (RustSlice u8))
    (start : usize) :
    RustM (RustArray u64 25) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (start +? RATE))
            <=? (← (core_models.slice.Impl.len u8 blocks)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← ((← (RATE %? (8 : usize))) ==? (0 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ := rust_primitives.hax.Tuple0.mk;
  let state_flat : (RustArray u64 25) ←
    (rust_primitives.hax.repeat (0 : u64) (25 : usize));
  let state_flat : (RustArray u64 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (RATE /? (8 : usize)))
      (fun state_flat _ => (do (pure true) : RustM Bool))
      state_flat
      (fun state_flat i =>
        (do
        let offset : usize ← (start +? (← ((8 : usize) *? i)));
        let state_flat : (RustArray u64 25) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            state_flat
            i
            (← (core_models.num.Impl_9.from_le_bytes
              (← (core_models.result.Impl.unwrap
                (RustArray u8 8)
                core_models.array.TryFromSliceError
                (← (core_models.convert.TryInto.try_into
                  (RustSlice u8)
                  (RustArray u8 8)
                  (← blocks[
                    (core_models.ops.range.Range.mk
                      (start := offset)
                      (_end := (← (offset +? (8 : usize)))))
                    ]_?))))))));
        (pure state_flat) :
        RustM (RustArray u64 25))));
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (RATE /? (8 : usize)))
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (libcrux_sha3.traits.set_ij ((1 : usize)) u64
          state
          (← (i /? (5 : usize)))
          (← (i %? (5 : usize)))
          (← ((← (libcrux_sha3.traits.get_ij ((1 : usize)) u64
              state
              (← (i /? (5 : usize)))
              (← (i %? (5 : usize)))))
            ^^^? (← state_flat[i]_?)))) :
        RustM (RustArray u64 25))));
  (pure state)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      load_block.spec (RATE : usize)
      (state : (RustArray u64 25))
      (blocks : (RustSlice u8))
      (start : usize) :
    Spec
      (requires := do
        ((← (libcrux_sha3.proof_utils.valid_rate RATE))
          &&? (← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.add
              (← (rust_primitives.hax.int.from_machine start))
              (← (rust_primitives.hax.int.from_machine RATE))))
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 blocks))))))))
      (ensures := fun _ => pure True)
      (load_block
        (RATE : usize)
        (state : (RustArray u64 25))
        (blocks : (RustSlice u8))
        (start : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def load_last (RATE : usize) (DELIMITER : u8)
    (state : (RustArray u64 25))
    (blocks : (RustSlice u8))
    (start : usize)
    (len : usize) :
    RustM (RustArray u64 25) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (start +? len))
            <=? (← (core_models.slice.Impl.len u8 blocks)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let buffer : (RustArray u8 RATE) ← (rust_primitives.hax.repeat (0 : u8) RATE);
  let buffer : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_range
      buffer
      (core_models.ops.range.Range.mk (start := (0 : usize)) (_end := len))
      (← (core_models.slice.Impl.copy_from_slice u8
        (← buffer[
          (core_models.ops.range.Range.mk (start := (0 : usize)) (_end := len))
          ]_?)
        (← blocks[
          (core_models.ops.range.Range.mk
            (start := start)
            (_end := (← (start +? len))))
          ]_?))));
  let buffer : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      buffer
      len
      DELIMITER);
  let buffer : (RustArray u8 RATE) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      buffer
      (← (RATE -? (1 : usize)))
      (← ((← buffer[(← (RATE -? (1 : usize)))]_?) |||? (128 : u8))));
  let state : (RustArray u64 25) ←
    (load_block (RATE) state (← (rust_primitives.unsize buffer)) (0 : usize));
  (pure state)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      load_last.spec (RATE : usize) (DELIMITER : u8)
      (state : (RustArray u64 25))
      (blocks : (RustSlice u8))
      (start : usize)
      (len : usize) :
    Spec
      (requires := do
        ((← ((← (libcrux_sha3.proof_utils.valid_rate RATE))
            &&? (← (len <? RATE))))
          &&? (← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.add
              (← (rust_primitives.hax.int.from_machine start))
              (← (rust_primitives.hax.int.from_machine len))))
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 blocks))))))))
      (ensures := fun _ => pure True)
      (load_last
        (RATE : usize)
        (DELIMITER : u8)
        (state : (RustArray u64 25))
        (blocks : (RustSlice u8))
        (start : usize)
        (len : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def store_block (RATE : usize)
    (s : (RustArray u64 25))
    (out : (RustSlice u8))
    (start : usize)
    (len : usize) :
    RustM (RustSlice u8) := do
  let octets : usize ← (len /? (8 : usize));
  let out_len : usize ← (core_models.slice.Impl.len u8 out);
  let out : (RustSlice u8) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      octets
      (fun out i =>
        (do ((← (core_models.slice.Impl.len u8 out)) ==? out_len) : RustM Bool))
      out
      (fun out i =>
        (do
        let bytes : (RustArray u8 8) ←
          (core_models.num.Impl_9.to_le_bytes
            (← (libcrux_sha3.traits.get_ij ((1 : usize)) u64
              s
              (← (i /? (5 : usize)))
              (← (i %? (5 : usize))))));
        let out_pos : usize ← (start +? (← ((8 : usize) *? i)));
        let out : (RustSlice u8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range
            out
            (core_models.ops.range.Range.mk
              (start := out_pos)
              (_end := (← (out_pos +? (8 : usize)))))
            (← (core_models.slice.Impl.copy_from_slice u8
              (← out[
                (core_models.ops.range.Range.mk
                  (start := out_pos)
                  (_end := (← (out_pos +? (8 : usize)))))
                ]_?)
              (← (rust_primitives.unsize bytes)))));
        (pure out) :
        RustM (RustSlice u8))));
  let remaining : usize ← (len %? (8 : usize));
  let out : (RustSlice u8) ←
    if (← (remaining >? (0 : usize))) then do
      let bytes : (RustArray u8 8) ←
        (core_models.num.Impl_9.to_le_bytes
          (← (libcrux_sha3.traits.get_ij ((1 : usize)) u64
            s
            (← (octets /? (5 : usize)))
            (← (octets %? (5 : usize))))));
      let out_pos : usize ← ((← (start +? len)) -? remaining);
      let out : (RustSlice u8) ←
        (rust_primitives.hax.monomorphized_update_at.update_at_range
          out
          (core_models.ops.range.Range.mk
            (start := out_pos)
            (_end := (← (out_pos +? remaining))))
          (← (core_models.slice.Impl.copy_from_slice u8
            (← out[
              (core_models.ops.range.Range.mk
                (start := out_pos)
                (_end := (← (out_pos +? remaining))))
              ]_?)
            (← bytes[
              (core_models.ops.range.RangeTo.mk (_end := remaining))
              ]_?))));
      (pure out)
    else do
      (pure out);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      store_block.spec (RATE : usize)
      (s : (RustArray u64 25))
      (out : (RustSlice u8))
      (start : usize)
      (len : usize) :
    Spec
      (requires := do
        ((← ((← (libcrux_sha3.proof_utils.valid_rate RATE))
            &&? (← (len <=? RATE))))
          &&? (← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.add
              (← (rust_primitives.hax.int.from_machine start))
              (← (rust_primitives.hax.int.from_machine len))))
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 out))))))))
      (ensures := fun
          out_future => do
          ((← (core_models.slice.Impl.len u8 out_future))
            ==? (← (core_models.slice.Impl.len u8 out))))
      (store_block
        (RATE : usize)
        (s : (RustArray u64 25))
        (out : (RustSlice u8))
        (start : usize)
        (len : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.simd.portable


namespace libcrux_sha3.traits

--  Trait to load new bytes into the state.
class Absorb.AssociatedTypes (Self : Type) (N : usize) where

class Absorb (Self : Type) (N : usize)
  [associatedTypes : outParam (Absorb.AssociatedTypes (Self : Type) (N :
      usize))]
  where
  load_block (Self) (N) (RATE : usize) :
    (Self -> (RustArray (RustSlice u8) N) -> usize -> RustM Self)
  load_last (Self) (N) (RATE : usize) (DELIMITER : u8) :
    (Self -> (RustArray (RustSlice u8) N) -> usize -> usize -> RustM Self)

end libcrux_sha3.traits


namespace libcrux_sha3.simd.portable

@[reducible] instance Impl_1.AssociatedTypes :
  libcrux_sha3.traits.Absorb.AssociatedTypes
  (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
  ((1 : usize))
  where

instance Impl_1 :
  libcrux_sha3.traits.Absorb
  (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
  ((1 : usize))
  where
  load_block :=
    fun (RATE : usize)
      (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
      (input : (RustArray (RustSlice u8) 1))
      (start : usize) => do
    let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) :=
      {self
      with st := (← (load_block (RATE)
        (libcrux_sha3.generic_keccak.KeccakState.st self)
        (← input[(0 : usize)]_?)
        start))};
    (pure self)
  load_last :=
    fun (RATE : usize) (DELIMITER : u8)
      (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
      (input : (RustArray (RustSlice u8) 1))
      (start : usize)
      (len : usize) => do
    let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) :=
      {self
      with st := (← (load_last (RATE) (DELIMITER)
        (libcrux_sha3.generic_keccak.KeccakState.st self)
        (← input[(0 : usize)]_?)
        start
        len))};
    (pure self)

end libcrux_sha3.simd.portable


namespace libcrux_sha3.simd.arm64

@[reducible] instance Impl_1.AssociatedTypes :
  libcrux_sha3.traits.Absorb.AssociatedTypes
  (libcrux_sha3.generic_keccak.KeccakState
    ((2 : usize))
    libcrux_intrinsics.arm64_extract._uint64x2_t)
  ((2 : usize))
  where

instance Impl_1 :
  libcrux_sha3.traits.Absorb
  (libcrux_sha3.generic_keccak.KeccakState
    ((2 : usize))
    libcrux_intrinsics.arm64_extract._uint64x2_t)
  ((2 : usize))
  where
  load_block :=
    fun (RATE : usize)
      (self :
      (libcrux_sha3.generic_keccak.KeccakState
        ((2 : usize))
        libcrux_intrinsics.arm64_extract._uint64x2_t))
      (input : (RustArray (RustSlice u8) 2))
      (start : usize) => do
    let
      self : (libcrux_sha3.generic_keccak.KeccakState
        ((2 : usize))
        libcrux_intrinsics.arm64_extract._uint64x2_t) :=
      {self
      with st := (← (load_block (RATE)
        (libcrux_sha3.generic_keccak.KeccakState.st self)
        input
        start))};
    (pure self)
  load_last :=
    fun (RATE : usize) (DELIMITER : u8)
      (self :
      (libcrux_sha3.generic_keccak.KeccakState
        ((2 : usize))
        libcrux_intrinsics.arm64_extract._uint64x2_t))
      (input : (RustArray (RustSlice u8) 2))
      (start : usize)
      (len : usize) => do
    let
      self : (libcrux_sha3.generic_keccak.KeccakState
        ((2 : usize))
        libcrux_intrinsics.arm64_extract._uint64x2_t) :=
      {self
      with st := (← (load_last (RATE) (DELIMITER)
        (libcrux_sha3.generic_keccak.KeccakState.st self)
        input
        start
        len))};
    (pure self)

end libcrux_sha3.simd.arm64


namespace libcrux_sha3.generic_keccak

def Impl_2.absorb_block
    (N : usize)
    (T : Type)
    (RATE : usize)
    [trait_constr_absorb_block_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_absorb_block_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    [trait_constr_absorb_block_associated_type_i1 :
      libcrux_sha3.traits.Absorb.AssociatedTypes
      (KeccakState (N) T)
      (N)]
    [trait_constr_absorb_block_i1 : libcrux_sha3.traits.Absorb
      (KeccakState (N) T)
      (N)
      ]
    (self : (KeccakState (N) T))
    (input : (RustArray (RustSlice u8) N))
    (start : usize) :
    RustM (KeccakState (N) T) := do
  let self : (KeccakState (N) T) ←
    (libcrux_sha3.traits.Absorb.load_block
      (KeccakState (N) T)
      (N) (RATE) self input start);
  let self : (KeccakState (N) T) ← (Impl_2.keccakf1600 (N) T self);
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_2.absorb_block.spec
      (N : usize)
      (T : Type)
      (RATE : usize)
      [trait_constr_absorb_block_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        T
        (N)]
      [trait_constr_absorb_block_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
      [trait_constr_absorb_block_associated_type_i1 :
        libcrux_sha3.traits.Absorb.AssociatedTypes
        (KeccakState (N) T)
        (N)]
      [trait_constr_absorb_block_i1 : libcrux_sha3.traits.Absorb
        (KeccakState (N) T)
        (N)
        ]
      (self : (KeccakState (N) T))
      (input : (RustArray (RustSlice u8) N))
      (start : usize) :
    Spec
      (requires := do
        (hax_lib.prop.constructors.and
          (← (hax_lib.prop.constructors.from_bool
            (← ((← ((← (N !=? (0 : usize)))
                &&? (← (libcrux_sha3.proof_utils.valid_rate RATE))))
              &&? (← (rust_primitives.hax.int.le
                (← (rust_primitives.hax.int.add
                  (← (rust_primitives.hax.int.from_machine start))
                  (← (rust_primitives.hax.int.from_machine RATE))))
                (← (rust_primitives.hax.int.from_machine
                  (← (core_models.slice.Impl.len u8
                    (← input[(0 : usize)]_?)))))))))))
          (← (libcrux_sha3.proof_utils.slices_same_len (N) input))))
      (ensures := fun _ => pure True)
      (Impl_2.absorb_block
        (N : usize)
        (T : Type)
        (RATE : usize)
        (self : (KeccakState (N) T))
        (input : (RustArray (RustSlice u8) N))
        (start : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def Impl_2.absorb_final
    (N : usize)
    (T : Type)
    (RATE : usize)
    (DELIM : u8)
    [trait_constr_absorb_final_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      T
      (N)]
    [trait_constr_absorb_final_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
    [trait_constr_absorb_final_associated_type_i1 :
      libcrux_sha3.traits.Absorb.AssociatedTypes
      (KeccakState (N) T)
      (N)]
    [trait_constr_absorb_final_i1 : libcrux_sha3.traits.Absorb
      (KeccakState (N) T)
      (N)
      ]
    (self : (KeccakState (N) T))
    (input : (RustArray (RustSlice u8) N))
    (start : usize)
    (len : usize) :
    RustM (KeccakState (N) T) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert (← ((← (N >? (0 : usize))) &&? (← (len <? RATE)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let self : (KeccakState (N) T) ←
    (libcrux_sha3.traits.Absorb.load_last
      (KeccakState (N) T)
      (N) (RATE) (DELIM) self input start len);
  let self : (KeccakState (N) T) ← (Impl_2.keccakf1600 (N) T self);
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_2.absorb_final.spec
      (N : usize)
      (T : Type)
      (RATE : usize)
      (DELIM : u8)
      [trait_constr_absorb_final_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        T
        (N)]
      [trait_constr_absorb_final_i0 : libcrux_sha3.traits.KeccakItem T (N) ]
      [trait_constr_absorb_final_associated_type_i1 :
        libcrux_sha3.traits.Absorb.AssociatedTypes
        (KeccakState (N) T)
        (N)]
      [trait_constr_absorb_final_i1 : libcrux_sha3.traits.Absorb
        (KeccakState (N) T)
        (N)
        ]
      (self : (KeccakState (N) T))
      (input : (RustArray (RustSlice u8) N))
      (start : usize)
      (len : usize) :
    Spec
      (requires := do
        (hax_lib.prop.constructors.and
          (← (hax_lib.prop.constructors.from_bool
            (← ((← ((← ((← (N !=? (0 : usize)))
                  &&? (← (libcrux_sha3.proof_utils.valid_rate RATE))))
                &&? (← (len <? RATE))))
              &&? (← (rust_primitives.hax.int.le
                (← (rust_primitives.hax.int.add
                  (← (rust_primitives.hax.int.from_machine start))
                  (← (rust_primitives.hax.int.from_machine len))))
                (← (rust_primitives.hax.int.from_machine
                  (← (core_models.slice.Impl.len u8
                    (← input[(0 : usize)]_?)))))))))))
          (← (libcrux_sha3.proof_utils.slices_same_len (N) input))))
      (ensures := fun _ => pure True)
      (Impl_2.absorb_final
        (N : usize)
        (T : Type)
        (RATE : usize)
        (DELIM : u8)
        (self : (KeccakState (N) T))
        (input : (RustArray (RustSlice u8) N))
        (start : usize)
        (len : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.generic_keccak


namespace libcrux_sha3.traits

--  Trait to squeeze bytes out of the state.
-- 
--  Note that this is implemented for each platform (1, 2, 4) because hax can\'t
--  handle the mutability required for a generic implementation.
-- 
--  Store blocks `N = 1`
class Squeeze.AssociatedTypes (Self : Type) (T : Type) where
  [trait_constr_Squeeze_i0 : KeccakItem.AssociatedTypes T ((1 : usize))]

attribute [instance_reducible, instance]
  Squeeze.AssociatedTypes.trait_constr_Squeeze_i0

class Squeeze (Self : Type) (T : Type)
  [associatedTypes : outParam (Squeeze.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  [trait_constr_Squeeze_i0 : KeccakItem T ((1 : usize))]
  squeeze (Self) (T) (RATE : usize) :
    (Self -> (RustSlice u8) -> usize -> usize -> RustM (RustSlice u8))

attribute [instance_reducible, instance] Squeeze.trait_constr_Squeeze_i0

end libcrux_sha3.traits


namespace libcrux_sha3.simd.portable

@[reducible] instance Impl_2.AssociatedTypes :
  libcrux_sha3.traits.Squeeze.AssociatedTypes
  (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
  u64
  where

instance Impl_2 :
  libcrux_sha3.traits.Squeeze
  (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
  u64
  where
  squeeze :=
    fun (RATE : usize)
      (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
      (out : (RustSlice u8))
      (start : usize)
      (len : usize) => do
    let out : (RustSlice u8) ←
      (store_block (RATE)
        (libcrux_sha3.generic_keccak.KeccakState.st self)
        out
        start
        len);
    (pure out)

end libcrux_sha3.simd.portable


namespace libcrux_sha3.generic_keccak.portable

def Impl.squeeze_next_block (RATE : usize)
    (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
    (out : (RustSlice u8))
    (start : usize) :
    RustM
    (rust_primitives.hax.Tuple2
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      (RustSlice u8))
    := do
  let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 self);
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out start RATE);
  (pure (rust_primitives.hax.Tuple2.mk self out))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.squeeze_next_block.spec (RATE : usize)
      (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
      (out : (RustSlice u8))
      (start : usize) :
    Spec
      (requires := do
        ((← (libcrux_sha3.proof_utils.valid_rate RATE))
          &&? (← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.add
              (← (rust_primitives.hax.int.from_machine start))
              (← (rust_primitives.hax.int.from_machine RATE))))
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 out))))))))
      (ensures := fun
          ⟨self__future, out_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out_future))
            ==? (← (core_models.slice.Impl.len u8 out))))
      (Impl.squeeze_next_block
        (RATE : usize)
        (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
        (out : (RustSlice u8))
        (start : usize)) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def Impl.squeeze_first_block (RATE : usize)
    (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
    (out : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out (0 : usize) RATE);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.squeeze_first_block.spec (RATE : usize)
      (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
      (out : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (libcrux_sha3.proof_utils.valid_rate RATE))
          &&? (← (RATE <=? (← (core_models.slice.Impl.len u8 out))))))
      (ensures := fun
          out_future => do
          ((← (core_models.slice.Impl.len u8 out_future))
            ==? (← (core_models.slice.Impl.len u8 out))))
      (Impl.squeeze_first_block
        (RATE : usize)
        (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
        (out : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def Impl.squeeze_first_three_blocks (RATE : usize)
    (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      (RustSlice u8))
    := do
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out (0 : usize) RATE);
  let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 self);
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out RATE RATE);
  let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 self);
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out (← ((2 : usize) *? RATE)) RATE);
  (pure (rust_primitives.hax.Tuple2.mk self out))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.squeeze_first_three_blocks.spec (RATE : usize)
      (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
      (out : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (libcrux_sha3.proof_utils.valid_rate RATE))
          &&? (← ((← ((3 : usize) *? RATE))
            <=? (← (core_models.slice.Impl.len u8 out))))))
      (ensures := fun
          ⟨self__future, out_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out_future))
            ==? (← (core_models.slice.Impl.len u8 out))))
      (Impl.squeeze_first_three_blocks
        (RATE : usize)
        (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
        (out : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

def Impl.squeeze_first_five_blocks (RATE : usize)
    (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      (RustSlice u8))
    := do
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out (0 : usize) RATE);
  let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 self);
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out RATE RATE);
  let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 self);
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out (← ((2 : usize) *? RATE)) RATE);
  let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 self);
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out (← ((3 : usize) *? RATE)) RATE);
  let self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 self);
  let out : (RustSlice u8) ←
    (libcrux_sha3.traits.Squeeze.squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
      u64 (RATE) self out (← ((4 : usize) *? RATE)) RATE);
  (pure (rust_primitives.hax.Tuple2.mk self out))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.squeeze_first_five_blocks.spec (RATE : usize)
      (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
      (out : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (libcrux_sha3.proof_utils.valid_rate RATE))
          &&? (← ((← ((5 : usize) *? RATE))
            <=? (← (core_models.slice.Impl.len u8 out))))))
      (ensures := fun
          ⟨self__future, out_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out_future))
            ==? (← (core_models.slice.Impl.len u8 out))))
      (Impl.squeeze_first_five_blocks
        (RATE : usize)
        (self : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))
        (out : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.generic_keccak.portable


namespace libcrux_sha3.proof_utils

--  XOF state invariant: validates that buffer length and rate are valid.
@[spec]
def keccak_xof_state_inv (rate : usize) (buf_len : usize) : RustM Bool := do
  ((← (valid_rate rate)) &&? (← (buf_len <=? rate)))

end libcrux_sha3.proof_utils


namespace libcrux_sha3.generic_keccak.xof

--  Generate a new keccak xof state.
def Impl.new
    (PARALLEL_LANES : usize)
    (RATE : usize)
    (STATE : Type)
    [trait_constr_new_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      STATE
      (PARALLEL_LANES)]
    [trait_constr_new_i0 : libcrux_sha3.traits.KeccakItem
      STATE
      (PARALLEL_LANES)
      ]
    (_ : rust_primitives.hax.Tuple0) :
    RustM (KeccakXofState (PARALLEL_LANES) (RATE) STATE) := do
  (pure (KeccakXofState.mk
    (inner := (← (libcrux_sha3.generic_keccak.Impl_2.new (PARALLEL_LANES) STATE
      rust_primitives.hax.Tuple0.mk)))
    (buf := (← (rust_primitives.hax.repeat
      (← (Impl.zero_block (PARALLEL_LANES) (RATE) STATE
        rust_primitives.hax.Tuple0.mk))
      PARALLEL_LANES)))
    (buf_len := (0 : usize))
    (sponge := false)))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.new.spec
      (PARALLEL_LANES : usize)
      (RATE : usize)
      (STATE : Type)
      [trait_constr_new_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        STATE
        (PARALLEL_LANES)]
      [trait_constr_new_i0 : libcrux_sha3.traits.KeccakItem
        STATE
        (PARALLEL_LANES)
        ]
      (_ : rust_primitives.hax.Tuple0) :
    Spec
      (requires := do
        ((← (PARALLEL_LANES ==? (1 : usize)))
          &&? (← (libcrux_sha3.proof_utils.valid_rate RATE))))
      (ensures := fun
          result => do
          (libcrux_sha3.proof_utils.keccak_xof_state_inv
            RATE
            (KeccakXofState.buf_len result)))
      (Impl.new (PARALLEL_LANES : usize) (RATE : usize) (STATE : Type) ⟨⟩) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Try to complete the internal partial buffer by consuming the minimum required
--  number of bytes from the provided `inputs` so that `self.buf` becomes exactly
--  one full block of size `RATE`.
-- 
--  Behaviour:
--  - If `self.buf_len` is 0 (no buffered bytes) or already equal to `RATE`
--    (already a full block), or if the combined available bytes in `inputs` are
--    not enough to reach `RATE`, the function does nothing and returns 0.
--  - If `0 < self.buf_len < RATE` and `inputs[..]` contain at least
--    `RATE - self.buf_len` bytes, the function copies exactly
--    `consumed = RATE - self.buf_len` bytes from each lane `inputs[i]` into
--    `self.buf[i]` starting at the current `self.buf_len` offset, sets
--    `self.buf_len = RATE`, and returns `consumed`.
-- 
--  Returns the `consumed` bytes from `inputs` if there\'s enough buffered
--  content to consume, and `0` otherwise.
--  If `consumed > 0` is returned, `self.buf` contains a full block to be
--  loaded.
def Impl.fill_buffer
    (PARALLEL_LANES : usize)
    (RATE : usize)
    (STATE : Type)
    [trait_constr_fill_buffer_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      STATE
      (PARALLEL_LANES)]
    [trait_constr_fill_buffer_i0 : libcrux_sha3.traits.KeccakItem
      STATE
      (PARALLEL_LANES)
      ]
    (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
    (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    RustM
    (rust_primitives.hax.Tuple2
      (KeccakXofState (PARALLEL_LANES) (RATE) STATE)
      usize)
    := do
  let input_len : usize ←
    (core_models.slice.Impl.len u8 (← inputs[(0 : usize)]_?));
  let ⟨self, hax_temp_output⟩ ←
    if
    (← ((← ((KeccakXofState.buf_len self) !=? (0 : usize)))
      &&? (← (input_len >=? (← (RATE -? (KeccakXofState.buf_len self))))))) then
    do
      let consumed : usize ← (RATE -? (KeccakXofState.buf_len self));
      let self_buf_len : usize := (KeccakXofState.buf_len self);
      let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) ←
        (rust_primitives.hax.folds.fold_range
          (0 : usize)
          PARALLEL_LANES
          (fun self _ =>
            (do ((KeccakXofState.buf_len self) ==? self_buf_len) : RustM Bool))
          self
          (fun self i =>
            (do
            let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
              {self
              with buf := (←
              (rust_primitives.hax.monomorphized_update_at.update_at_usize
                (KeccakXofState.buf self)
                i
                (←
                (rust_primitives.hax.monomorphized_update_at.update_at_range_from
                  (← (KeccakXofState.buf self)[i]_?)
                  (core_models.ops.range.RangeFrom.mk
                    (start := (KeccakXofState.buf_len self)))
                  (← (core_models.slice.Impl.copy_from_slice u8
                    (← (← (KeccakXofState.buf self)[i]_?)[
                      (core_models.ops.range.RangeFrom.mk
                        (start := (KeccakXofState.buf_len self)))
                      ]_?)
                    (← (← inputs[i]_?)[
                      (core_models.ops.range.RangeTo.mk (_end := consumed))
                      ]_?)))))))};
            (pure self) :
            RustM (KeccakXofState (PARALLEL_LANES) (RATE) STATE))));
      let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
        {self with buf_len := RATE};
      (pure (rust_primitives.hax.Tuple2.mk self consumed))
    else do
      (pure (rust_primitives.hax.Tuple2.mk self (0 : usize)));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.fill_buffer.spec
      (PARALLEL_LANES : usize)
      (RATE : usize)
      (STATE : Type)
      [trait_constr_fill_buffer_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        STATE
        (PARALLEL_LANES)]
      [trait_constr_fill_buffer_i0 : libcrux_sha3.traits.KeccakItem
        STATE
        (PARALLEL_LANES)
        ]
      (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
      (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    Spec
      (requires := do
        ((← (PARALLEL_LANES ==? (1 : usize)))
          &&? (← (libcrux_sha3.proof_utils.keccak_xof_state_inv
            RATE
            (KeccakXofState.buf_len self)))))
      (ensures := fun
          ⟨self__future, consumed⟩ => do
          ((← (libcrux_sha3.proof_utils.keccak_xof_state_inv
              RATE
              (KeccakXofState.buf_len self__future)))
            &&? (← if (← (consumed ==? (0 : usize))) then do
              ((← ((KeccakXofState.buf_len self__future)
                  ==? (KeccakXofState.buf_len self)))
                &&? (← ((← ((← ((KeccakXofState.buf_len self) ==? (0 : usize)))
                    ||? (← ((KeccakXofState.buf_len self) ==? RATE))))
                  ||? (← (rust_primitives.hax.int.lt
                    (← (rust_primitives.hax.int.add
                      (← (rust_primitives.hax.int.from_machine
                        (KeccakXofState.buf_len self)))
                      (← (rust_primitives.hax.int.from_machine
                        (← (core_models.slice.Impl.len u8
                          (← inputs[(0 : usize)]_?)))))))
                    (← (rust_primitives.hax.int.from_machine RATE)))))))
            else do
              ((← ((KeccakXofState.buf_len self__future) ==? RATE))
                &&? (← (consumed
                  ==? (← (RATE -? (KeccakXofState.buf_len self)))))))))
      (Impl.fill_buffer
        (PARALLEL_LANES : usize)
        (RATE : usize)
        (STATE : Type)
        (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
        (inputs : (RustArray (RustSlice u8) PARALLEL_LANES))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.generic_keccak.xof


namespace libcrux_sha3.proof_utils.lemmas

--  Lemma proving the division-multiplication-modulo identity.
-- 
--  For any `a`, `b` with `b != 0`,
--  proves that `(a / b) * b + (a % b) = a`.
-- 
--  This is used in the `squeeze` function to verify correct buffer indexing
--  when squeezing multiple blocks.
@[spec]
def lemma_div_mul_mod (_a : usize) (_b : usize) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end libcrux_sha3.proof_utils.lemmas


namespace libcrux_sha3.generic_keccak.xof

--  Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
def Impl_1.squeeze
    (RATE : usize)
    (STATE : Type)
    [trait_constr_squeeze_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      STATE
      ((1 : usize))]
    [trait_constr_squeeze_i0 : libcrux_sha3.traits.KeccakItem
      STATE
      ((1 : usize))
      ]
    [trait_constr_squeeze_associated_type_i1 :
      libcrux_sha3.traits.Squeeze.AssociatedTypes
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) STATE)
      STATE]
    [trait_constr_squeeze_i1 : libcrux_sha3.traits.Squeeze
      (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) STATE)
      STATE
      ]
    (self : (KeccakXofState ((1 : usize)) (RATE) STATE))
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      (KeccakXofState ((1 : usize)) (RATE) STATE)
      (RustSlice u8))
    := do
  let out_len : usize ← (core_models.slice.Impl.len u8 out);
  if (← (out_len ==? (0 : usize))) then do
    (pure (rust_primitives.hax.Tuple2.mk self out))
  else do
    let self : (KeccakXofState ((1 : usize)) (RATE) STATE) ←
      if (KeccakXofState.sponge self) then do
        let self : (KeccakXofState ((1 : usize)) (RATE) STATE) :=
          {self
          with inner := (← (libcrux_sha3.generic_keccak.Impl_2.keccakf1600
            ((1 : usize))
            STATE (KeccakXofState.inner self)))};
        (pure self)
      else do
        (pure self);
    let ⟨out, self⟩ ←
      if (← (out_len >? (0 : usize))) then do
        let blocks : usize ← (out_len /? RATE);
        let last : usize ← (out_len -? (← (out_len %? RATE)));
        if (← (blocks ==? (0 : usize))) then do
          let out : (RustSlice u8) ←
            (libcrux_sha3.traits.Squeeze.squeeze
              (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) STATE)
              STATE (RATE) (KeccakXofState.inner self) out (0 : usize) out_len);
          (pure (rust_primitives.hax.Tuple2.mk out self))
        else do
          let out : (RustSlice u8) ←
            (libcrux_sha3.traits.Squeeze.squeeze
              (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) STATE)
              STATE (RATE) (KeccakXofState.inner self) out (0 : usize) RATE);
          let self_buf_len : usize := (KeccakXofState.buf_len self);
          let ⟨out, self⟩ ←
            (rust_primitives.hax.folds.fold_range
              (1 : usize)
              blocks
              (fun ⟨out, self⟩ _ =>
                (do
                ((← ((← (core_models.slice.Impl.len u8 out)) ==? out_len))
                  &&? (← (self_buf_len ==? (KeccakXofState.buf_len self)))) :
                RustM Bool))
              (rust_primitives.hax.Tuple2.mk out self)
              (fun ⟨out, self⟩ i =>
                (do
                let _ ←
                  (hax_lib.assert
                    (← (rust_primitives.hax.int.le
                      (← (rust_primitives.hax.int.mul
                        (← (rust_primitives.hax.int.from_machine i))
                        (← (rust_primitives.hax.int.from_machine RATE))))
                      (← (rust_primitives.hax.int.from_machine
                        (← (core_models.slice.Impl.len u8 out)))))));
                let self : (KeccakXofState ((1 : usize)) (RATE) STATE) :=
                  {self
                  with inner := (←
                  (libcrux_sha3.generic_keccak.Impl_2.keccakf1600
                    ((1 : usize))
                    STATE (KeccakXofState.inner self)))};
                let out : (RustSlice u8) ←
                  (libcrux_sha3.traits.Squeeze.squeeze
                    (libcrux_sha3.generic_keccak.KeccakState
                      ((1 : usize))
                      STATE)
                    STATE (RATE)
                    (KeccakXofState.inner self)
                    out
                    (← (i *? RATE))
                    RATE);
                (pure (rust_primitives.hax.Tuple2.mk out self)) :
                RustM
                (rust_primitives.hax.Tuple2
                  (RustSlice u8)
                  (KeccakXofState ((1 : usize)) (RATE) STATE)))));
          if (← (last <? out_len)) then do
            let _ ←
              (libcrux_sha3.proof_utils.lemmas.lemma_div_mul_mod out_len RATE);
            let self : (KeccakXofState ((1 : usize)) (RATE) STATE) :=
              {self
              with inner := (← (libcrux_sha3.generic_keccak.Impl_2.keccakf1600
                ((1 : usize))
                STATE (KeccakXofState.inner self)))};
            let out : (RustSlice u8) ←
              (libcrux_sha3.traits.Squeeze.squeeze
                (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) STATE)
                STATE (RATE)
                (KeccakXofState.inner self)
                out
                last
                (← (out_len -? last)));
            (pure (rust_primitives.hax.Tuple2.mk out self))
          else do
            (pure (rust_primitives.hax.Tuple2.mk out self))
      else do
        (pure (rust_primitives.hax.Tuple2.mk out self));
    let self : (KeccakXofState ((1 : usize)) (RATE) STATE) :=
      {self with sponge := true};
    (pure (rust_primitives.hax.Tuple2.mk self out))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_1.squeeze.spec
      (RATE : usize)
      (STATE : Type)
      [trait_constr_squeeze_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        STATE
        ((1 : usize))]
      [trait_constr_squeeze_i0 : libcrux_sha3.traits.KeccakItem
        STATE
        ((1 : usize))
        ]
      [trait_constr_squeeze_associated_type_i1 :
        libcrux_sha3.traits.Squeeze.AssociatedTypes
        (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) STATE)
        STATE]
      [trait_constr_squeeze_i1 : libcrux_sha3.traits.Squeeze
        (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) STATE)
        STATE
        ]
      (self : (KeccakXofState ((1 : usize)) (RATE) STATE))
      (out : (RustSlice u8)) :
    Spec
      (requires := do
        (libcrux_sha3.proof_utils.keccak_xof_state_inv
          RATE
          (KeccakXofState.buf_len self)))
      (ensures := fun
          ⟨self__future, out_future⟩ => do
          ((← (libcrux_sha3.proof_utils.keccak_xof_state_inv
              RATE
              (KeccakXofState.buf_len self__future)))
            &&? (← ((← (core_models.slice.Impl.len u8 out_future))
              ==? (← (core_models.slice.Impl.len u8 out))))))
      (Impl_1.squeeze
        (RATE : usize)
        (STATE : Type)
        (self : (KeccakXofState ((1 : usize)) (RATE) STATE))
        (out : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.generic_keccak.xof


namespace libcrux_sha3.proof_utils.lemmas

--  Lemma proving multiplication bounds for successive elements.
-- 
--  For any `k < n`,
--  proves that `k * d + d ≤ n * d`.
-- 
--  This is used in the `keccak` functions to verify that block iterations
--  stay within bounds.
@[spec]
def lemma_mul_succ_le (_k : usize) (_n : usize) (_d : usize) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end libcrux_sha3.proof_utils.lemmas


namespace libcrux_sha3.generic_keccak.xof

def Impl.absorb_full
    (PARALLEL_LANES : usize)
    (RATE : usize)
    (STATE : Type)
    [trait_constr_absorb_full_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      STATE
      (PARALLEL_LANES)]
    [trait_constr_absorb_full_i0 : libcrux_sha3.traits.KeccakItem
      STATE
      (PARALLEL_LANES)
      ]
    [trait_constr_absorb_full_associated_type_i1 :
      libcrux_sha3.traits.Absorb.AssociatedTypes
      (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
      (PARALLEL_LANES)]
    [trait_constr_absorb_full_i1 : libcrux_sha3.traits.Absorb
      (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
      (PARALLEL_LANES)
      ]
    (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
    (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    RustM
    (rust_primitives.hax.Tuple2
      (KeccakXofState (PARALLEL_LANES) (RATE) STATE)
      usize)
    := do
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← (PARALLEL_LANES >? (0 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← ((KeccakXofState.buf_len self) <=? RATE)));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let ⟨tmp0, out⟩ ←
    (Impl.fill_buffer (PARALLEL_LANES) (RATE) STATE self inputs);
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) := tmp0;
  let consumed : usize := out;
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) ←
    if (← ((KeccakXofState.buf_len self) ==? RATE)) then do
      let borrowed : (RustArray (RustSlice u8) PARALLEL_LANES) ←
        (buf_to_slices (PARALLEL_LANES) (RATE) (KeccakXofState.buf self));
      let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
        {self
        with inner := (← (libcrux_sha3.traits.Absorb.load_block
          (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
          (PARALLEL_LANES) (RATE)
          (KeccakXofState.inner self)
          borrowed
          (0 : usize)))};
      let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
        {self
        with inner := (← (libcrux_sha3.generic_keccak.Impl_2.keccakf1600
          (PARALLEL_LANES)
          STATE (KeccakXofState.inner self)))};
      let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
        {self with buf_len := (0 : usize)};
      (pure self)
    else do
      (pure self);
  let input_to_consume : usize ←
    ((← (core_models.slice.Impl.len u8 (← inputs[(0 : usize)]_?))) -? consumed);
  let num_blocks : usize ← (input_to_consume /? RATE);
  let remainder : usize ← (input_to_consume %? RATE);
  let _end : usize ← (consumed +? (← (num_blocks *? RATE)));
  let _ ←
    (hax_lib.assert
      (← (_end
        <=? (← (core_models.slice.Impl.len u8 (← inputs[(0 : usize)]_?))))));
  let ⟨self_buf_len, _end⟩ :=
    (rust_primitives.hax.Tuple2.mk (KeccakXofState.buf_len self) _end);
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      num_blocks
      (fun self _ =>
        (do ((KeccakXofState.buf_len self) ==? self_buf_len) : RustM Bool))
      self
      (fun self i =>
        (do
        let _ ←
          (libcrux_sha3.proof_utils.lemmas.lemma_mul_succ_le i num_blocks RATE);
        let start : usize ← ((← (i *? RATE)) +? consumed);
        let _ ← (hax_lib.assert (← ((← (start +? RATE)) <=? _end)));
        let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
          {self
          with inner := (← (libcrux_sha3.traits.Absorb.load_block
            (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
            (PARALLEL_LANES) (RATE) (KeccakXofState.inner self) inputs start))};
        let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
          {self
          with inner := (← (libcrux_sha3.generic_keccak.Impl_2.keccakf1600
            (PARALLEL_LANES)
            STATE (KeccakXofState.inner self)))};
        (pure self) :
        RustM (KeccakXofState (PARALLEL_LANES) (RATE) STATE))));
  let hax_temp_output : usize := remainder;
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.absorb_full.spec
      (PARALLEL_LANES : usize)
      (RATE : usize)
      (STATE : Type)
      [trait_constr_absorb_full_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        STATE
        (PARALLEL_LANES)]
      [trait_constr_absorb_full_i0 : libcrux_sha3.traits.KeccakItem
        STATE
        (PARALLEL_LANES)
        ]
      [trait_constr_absorb_full_associated_type_i1 :
        libcrux_sha3.traits.Absorb.AssociatedTypes
        (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
        (PARALLEL_LANES)]
      [trait_constr_absorb_full_i1 : libcrux_sha3.traits.Absorb
        (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
        (PARALLEL_LANES)
        ]
      (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
      (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    Spec
      (requires := do
        ((← (PARALLEL_LANES ==? (1 : usize)))
          &&? (← (libcrux_sha3.proof_utils.keccak_xof_state_inv
            RATE
            (KeccakXofState.buf_len self)))))
      (ensures := fun
          ⟨self__future, remainder⟩ => do
          ((← (libcrux_sha3.proof_utils.keccak_xof_state_inv
              RATE
              (KeccakXofState.buf_len self__future)))
            &&? (← (rust_primitives.hax.int.le
              (← (rust_primitives.hax.int.add
                (← (rust_primitives.hax.int.from_machine
                  (KeccakXofState.buf_len self__future)))
                (← (rust_primitives.hax.int.from_machine remainder))))
              (← (rust_primitives.hax.int.from_machine RATE))))))
      (Impl.absorb_full
        (PARALLEL_LANES : usize)
        (RATE : usize)
        (STATE : Type)
        (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
        (inputs : (RustArray (RustSlice u8) PARALLEL_LANES))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Absorb
-- 
--  This function takes any number of bytes to absorb and buffers if it\'s not enough.
--  The function assumes that all input slices in `inputs` have the same length.
-- 
--  Only a multiple of `RATE` blocks are absorbed.
--  For the remaining bytes [`absorb_final`] needs to be called.
-- 
--  This works best with relatively small `inputs`.
def Impl.absorb
    (PARALLEL_LANES : usize)
    (RATE : usize)
    (STATE : Type)
    [trait_constr_absorb_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      STATE
      (PARALLEL_LANES)]
    [trait_constr_absorb_i0 : libcrux_sha3.traits.KeccakItem
      STATE
      (PARALLEL_LANES)
      ]
    [trait_constr_absorb_associated_type_i1 :
      libcrux_sha3.traits.Absorb.AssociatedTypes
      (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
      (PARALLEL_LANES)]
    [trait_constr_absorb_i1 : libcrux_sha3.traits.Absorb
      (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
      (PARALLEL_LANES)
      ]
    (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
    (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    RustM (KeccakXofState (PARALLEL_LANES) (RATE) STATE) := do
  let ⟨tmp0, out⟩ ←
    (Impl.absorb_full (PARALLEL_LANES) (RATE) STATE self inputs);
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) := tmp0;
  let remainder : usize := out;
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) ←
    if (← (remainder >? (0 : usize))) then do
      let _ ←
        if true then do
          let _ ←
            (hax_lib.assert
              (← ((← ((KeccakXofState.buf_len self) ==? (0 : usize)))
                ||? (← ((← ((KeccakXofState.buf_len self) +? remainder))
                  <=? RATE)))));
          (pure rust_primitives.hax.Tuple0.mk)
        else do
          (pure rust_primitives.hax.Tuple0.mk);
      let _ ←
        (hax_lib.assert
          (← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.add
              (← (rust_primitives.hax.int.from_machine remainder))
              (← (rust_primitives.hax.int.from_machine
                (KeccakXofState.buf_len self)))))
            (← (rust_primitives.hax.int.from_machine RATE)))));
      let input_len : usize ←
        (core_models.slice.Impl.len u8 (← inputs[(0 : usize)]_?));
      let self_buf_len : usize := (KeccakXofState.buf_len self);
      let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) ←
        (rust_primitives.hax.folds.fold_range
          (0 : usize)
          PARALLEL_LANES
          (fun self _ =>
            (do ((KeccakXofState.buf_len self) ==? self_buf_len) : RustM Bool))
          self
          (fun self i =>
            (do
            let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
              {self
              with buf := (←
              (rust_primitives.hax.monomorphized_update_at.update_at_usize
                (KeccakXofState.buf self)
                i
                (← (rust_primitives.hax.monomorphized_update_at.update_at_range
                  (← (KeccakXofState.buf self)[i]_?)
                  (core_models.ops.range.Range.mk
                    (start := (KeccakXofState.buf_len self))
                    (_end := (← ((KeccakXofState.buf_len self) +? remainder))))
                  (← (core_models.slice.Impl.copy_from_slice u8
                    (← (← (KeccakXofState.buf self)[i]_?)[
                      (core_models.ops.range.Range.mk
                        (start := (KeccakXofState.buf_len self))
                        (_end := (← ((KeccakXofState.buf_len self)
                          +? remainder))))
                      ]_?)
                    (← (← inputs[i]_?)[
                      (core_models.ops.range.Range.mk
                        (start := (← (input_len -? remainder)))
                        (_end := input_len))
                      ]_?)))))))};
            (pure self) :
            RustM (KeccakXofState (PARALLEL_LANES) (RATE) STATE))));
      let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
        {self with buf_len := (← ((KeccakXofState.buf_len self) +? remainder))};
      (pure self)
    else do
      (pure self);
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.absorb.spec
      (PARALLEL_LANES : usize)
      (RATE : usize)
      (STATE : Type)
      [trait_constr_absorb_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        STATE
        (PARALLEL_LANES)]
      [trait_constr_absorb_i0 : libcrux_sha3.traits.KeccakItem
        STATE
        (PARALLEL_LANES)
        ]
      [trait_constr_absorb_associated_type_i1 :
        libcrux_sha3.traits.Absorb.AssociatedTypes
        (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
        (PARALLEL_LANES)]
      [trait_constr_absorb_i1 : libcrux_sha3.traits.Absorb
        (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
        (PARALLEL_LANES)
        ]
      (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
      (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    Spec
      (requires := do
        ((← (PARALLEL_LANES ==? (1 : usize)))
          &&? (← (libcrux_sha3.proof_utils.keccak_xof_state_inv
            RATE
            (KeccakXofState.buf_len self)))))
      (ensures := fun
          self__future => do
          (libcrux_sha3.proof_utils.keccak_xof_state_inv
            RATE
            (KeccakXofState.buf_len self__future)))
      (Impl.absorb
        (PARALLEL_LANES : usize)
        (RATE : usize)
        (STATE : Type)
        (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
        (inputs : (RustArray (RustSlice u8) PARALLEL_LANES))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Absorb a final block.
-- 
--  The `inputs` block may be empty. Everything in the `inputs` block beyond
--  `RATE` bytes is ignored.
def Impl.absorb_final
    (PARALLEL_LANES : usize)
    (RATE : usize)
    (STATE : Type)
    (DELIMITER : u8)
    [trait_constr_absorb_final_associated_type_i0 :
      libcrux_sha3.traits.KeccakItem.AssociatedTypes
      STATE
      (PARALLEL_LANES)]
    [trait_constr_absorb_final_i0 : libcrux_sha3.traits.KeccakItem
      STATE
      (PARALLEL_LANES)
      ]
    [trait_constr_absorb_final_associated_type_i1 :
      libcrux_sha3.traits.Absorb.AssociatedTypes
      (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
      (PARALLEL_LANES)]
    [trait_constr_absorb_final_i1 : libcrux_sha3.traits.Absorb
      (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
      (PARALLEL_LANES)
      ]
    (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
    (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    RustM (KeccakXofState (PARALLEL_LANES) (RATE) STATE) := do
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) ←
    (Impl.absorb (PARALLEL_LANES) (RATE) STATE self inputs);
  let borrowed : (RustArray (RustSlice u8) PARALLEL_LANES) ←
    (buf_to_slices (PARALLEL_LANES) (RATE) (KeccakXofState.buf self));
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
    {self
    with inner := (← (libcrux_sha3.traits.Absorb.load_last
      (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
      (PARALLEL_LANES) (RATE) (DELIMITER)
      (KeccakXofState.inner self)
      borrowed
      (0 : usize)
      (KeccakXofState.buf_len self)))};
  let self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE) :=
    {self
    with inner := (← (libcrux_sha3.generic_keccak.Impl_2.keccakf1600
      (PARALLEL_LANES)
      STATE (KeccakXofState.inner self)))};
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.absorb_final.spec
      (PARALLEL_LANES : usize)
      (RATE : usize)
      (STATE : Type)
      (DELIMITER : u8)
      [trait_constr_absorb_final_associated_type_i0 :
        libcrux_sha3.traits.KeccakItem.AssociatedTypes
        STATE
        (PARALLEL_LANES)]
      [trait_constr_absorb_final_i0 : libcrux_sha3.traits.KeccakItem
        STATE
        (PARALLEL_LANES)
        ]
      [trait_constr_absorb_final_associated_type_i1 :
        libcrux_sha3.traits.Absorb.AssociatedTypes
        (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
        (PARALLEL_LANES)]
      [trait_constr_absorb_final_i1 : libcrux_sha3.traits.Absorb
        (libcrux_sha3.generic_keccak.KeccakState (PARALLEL_LANES) STATE)
        (PARALLEL_LANES)
        ]
      (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
      (inputs : (RustArray (RustSlice u8) PARALLEL_LANES)) :
    Spec
      (requires := do
        ((← (PARALLEL_LANES ==? (1 : usize)))
          &&? (← (libcrux_sha3.proof_utils.keccak_xof_state_inv
            RATE
            (KeccakXofState.buf_len self)))))
      (ensures := fun
          self__future => do
          (libcrux_sha3.proof_utils.keccak_xof_state_inv
            RATE
            (KeccakXofState.buf_len self__future)))
      (Impl.absorb_final
        (PARALLEL_LANES : usize)
        (RATE : usize)
        (STATE : Type)
        (DELIMITER : u8)
        (self : (KeccakXofState (PARALLEL_LANES) (RATE) STATE))
        (inputs : (RustArray (RustSlice u8) PARALLEL_LANES))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.generic_keccak.xof


namespace libcrux_sha3.generic_keccak.portable

def keccak1 (RATE : usize) (DELIM : u8)
    (input : (RustSlice u8))
    (output : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let s : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.new ((1 : usize)) u64
      rust_primitives.hax.Tuple0.mk);
  let input_len : usize ← (core_models.slice.Impl.len u8 input);
  let input_blocks : usize ← (input_len /? RATE);
  let input_rem : usize ← (input_len %? RATE);
  let s : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      input_blocks
      (fun s _ => (do (pure true) : RustM Bool))
      s
      (fun s i =>
        (do
        let _ ←
          (libcrux_sha3.proof_utils.lemmas.lemma_mul_succ_le
            i
            input_blocks
            RATE);
        let s : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
          (libcrux_sha3.generic_keccak.Impl_2.absorb_block
            ((1 : usize))
            u64
            (RATE) s (RustArray.ofVec #v[input]) (← (i *? RATE)));
        (pure s) :
        RustM (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64))));
  let s : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
    (libcrux_sha3.generic_keccak.Impl_2.absorb_final
      ((1 : usize))
      u64
      (RATE)
      (DELIM)
      s
      (RustArray.ofVec #v[input])
      (← (input_len -? input_rem))
      input_rem);
  let output_len : usize ← (core_models.slice.Impl.len u8 output);
  let output_blocks : usize ← (output_len /? RATE);
  let output_rem : usize ← (output_len %? RATE);
  let ⟨output, s⟩ ←
    if (← (output_blocks ==? (0 : usize))) then do
      let output : (RustSlice u8) ←
        (libcrux_sha3.traits.Squeeze.squeeze
          (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
          u64 (RATE) s output (0 : usize) output_len);
      (pure (rust_primitives.hax.Tuple2.mk output s))
    else do
      let output : (RustSlice u8) ←
        (libcrux_sha3.traits.Squeeze.squeeze
          (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
          u64 (RATE) s output (0 : usize) RATE);
      let ⟨output, s⟩ ←
        (rust_primitives.hax.folds.fold_range
          (1 : usize)
          output_blocks
          (fun ⟨output, s⟩ _ =>
            (do
            ((← (core_models.slice.Impl.len u8 output)) ==? output_len) :
            RustM Bool))
          (rust_primitives.hax.Tuple2.mk output s)
          (fun ⟨output, s⟩ i =>
            (do
            let _ ←
              (libcrux_sha3.proof_utils.lemmas.lemma_mul_succ_le
                i
                output_blocks
                RATE);
            let
              s : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
              (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64
                s);
            let output : (RustSlice u8) ←
              (libcrux_sha3.traits.Squeeze.squeeze
                (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
                u64 (RATE) s output (← (i *? RATE)) RATE);
            (pure (rust_primitives.hax.Tuple2.mk output s)) :
            RustM
            (rust_primitives.hax.Tuple2
              (RustSlice u8)
              (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)))));
      if (← (output_rem !=? (0 : usize))) then do
        let s : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64) ←
          (libcrux_sha3.generic_keccak.Impl_2.keccakf1600 ((1 : usize)) u64 s);
        let output : (RustSlice u8) ←
          (libcrux_sha3.traits.Squeeze.squeeze
            (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)
            u64 (RATE) s output (← (output_len -? output_rem)) output_rem);
        (pure (rust_primitives.hax.Tuple2.mk output s))
      else do
        (pure (rust_primitives.hax.Tuple2.mk output s));
  (pure output)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      keccak1.spec (RATE : usize) (DELIM : u8)
      (input : (RustSlice u8))
      (output : (RustSlice u8)) :
    Spec
      (requires := do (libcrux_sha3.proof_utils.valid_rate RATE))
      (ensures := fun
          output_future => do
          ((← (core_models.slice.Impl.len u8 output_future))
            ==? (← (core_models.slice.Impl.len u8 output))))
      (keccak1
        (RATE : usize)
        (DELIM : u8)
        (input : (RustSlice u8))
        (output : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.generic_keccak.portable


namespace libcrux_sha3

--  The Digest Algorithm.
inductive Algorithm : Type
| --  SHA3 224
    Sha224 : Algorithm
| --  SHA3 256
    Sha256 : Algorithm
| --  SHA3 384
    Sha384 : Algorithm
| --  SHA3 512
    Sha512 : Algorithm

def Algorithm.Sha224.AnonConst : u32 := (1 : u32)

def Algorithm.Sha256.AnonConst : u32 := (2 : u32)

def Algorithm.Sha384.AnonConst : u32 := (3 : u32)

def Algorithm.Sha512.AnonConst : u32 := (4 : u32)

@[spec]
def Algorithm_cast_to_repr (x : Algorithm) : RustM u32 := do
  match x with
    | (Algorithm.Sha224 ) => do (pure Algorithm.Sha224.AnonConst)
    | (Algorithm.Sha256 ) => do (pure Algorithm.Sha256.AnonConst)
    | (Algorithm.Sha384 ) => do (pure Algorithm.Sha384.AnonConst)
    | (Algorithm.Sha512 ) => do (pure Algorithm.Sha512.AnonConst)

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.clone.Clone Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.marker.Copy Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.fmt.Debug Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.marker.StructuralPartialEq Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes Algorithm Algorithm :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.cmp.PartialEq Algorithm Algorithm :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl.AssociatedTypes :
  core_models.convert.From.AssociatedTypes u32 Algorithm
  where

instance Impl : core_models.convert.From u32 Algorithm where
  _from := fun (v : Algorithm) => do
    match v with
      | (Algorithm.Sha224 ) => do (pure (1 : u32))
      | (Algorithm.Sha256 ) => do (pure (2 : u32))
      | (Algorithm.Sha384 ) => do (pure (3 : u32))
      | (Algorithm.Sha512 ) => do (pure (4 : u32))

--  Returns the output size of a digest.
@[spec]
def digest_size (mode : Algorithm) : RustM usize := do
  match mode with
    | (Algorithm.Sha224 ) => do (pure SHA3_224_DIGEST_SIZE)
    | (Algorithm.Sha256 ) => do (pure SHA3_256_DIGEST_SIZE)
    | (Algorithm.Sha384 ) => do (pure SHA3_384_DIGEST_SIZE)
    | (Algorithm.Sha512 ) => do (pure SHA3_512_DIGEST_SIZE)

end libcrux_sha3


namespace libcrux_sha3.portable

--  The Keccak state for the incremental API.
structure KeccakState where
  state : (libcrux_sha3.generic_keccak.KeccakState ((1 : usize)) u64)

@[instance] opaque Impl.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  core_models.clone.Clone KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes KeccakState :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.marker.Copy KeccakState :=
  by constructor <;> exact Inhabited.default

--  A portable SHA3 224 implementation.
@[spec]
def sha224 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (libcrux_sha3.generic_keccak.portable.keccak1 ((144 : usize)) ((6 : u8))
      data
      digest);
  (pure digest)

end libcrux_sha3.portable


namespace libcrux_sha3

--  SHA3 224
-- 
--  Preconditions:
--  - `digest.len() == 28`
def sha224_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (28 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ← (libcrux_sha3.portable.sha224 digest payload);
  (pure digest)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha224_ema.spec (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 payload))))
            (← (rust_primitives.hax.int.from_machine
              core_models.num.Impl_8.MAX))))
          &&? (← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 digest))))
            (← (hax_lib.int.Impl_7._unsafe_from_str "28"))))))
      (ensures := fun _ => pure True)
      (sha224_ema (digest : (RustSlice u8)) (payload : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  SHA3 224
def sha224 (data : (RustSlice u8)) : RustM (RustArray u8 28) := do
  let out : (RustArray u8 28) ←
    (rust_primitives.hax.repeat (0 : u8) (28 : usize));
  let out : (RustArray u8 28) ← (sha224_ema out data);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha224.spec (data : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 data))))
          (← (rust_primitives.hax.int.from_machine
            core_models.num.Impl_8.MAX))))
      (ensures := fun _ => pure True)
      (sha224 (data : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3


namespace libcrux_sha3.portable

--  A portable SHA3 256 implementation.
@[spec]
def sha256 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (libcrux_sha3.generic_keccak.portable.keccak1 ((136 : usize)) ((6 : u8))
      data
      digest);
  (pure digest)

end libcrux_sha3.portable


namespace libcrux_sha3

--  SHA3 256
def sha256_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (32 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ← (libcrux_sha3.portable.sha256 digest payload);
  (pure digest)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha256_ema.spec (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 payload))))
            (← (rust_primitives.hax.int.from_machine
              core_models.num.Impl_8.MAX))))
          &&? (← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 digest))))
            (← (hax_lib.int.Impl_7._unsafe_from_str "32"))))))
      (ensures := fun _ => pure True)
      (sha256_ema (digest : (RustSlice u8)) (payload : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  SHA3 256
def sha256 (data : (RustSlice u8)) : RustM (RustArray u8 32) := do
  let out : (RustArray u8 32) ←
    (rust_primitives.hax.repeat (0 : u8) (32 : usize));
  let out : (RustArray u8 32) ← (sha256_ema out data);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha256.spec (data : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 data))))
          (← (rust_primitives.hax.int.from_machine
            core_models.num.Impl_8.MAX))))
      (ensures := fun _ => pure True)
      (sha256 (data : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3


namespace libcrux_sha3.portable

--  A portable SHA3 384 implementation.
@[spec]
def sha384 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (libcrux_sha3.generic_keccak.portable.keccak1 ((104 : usize)) ((6 : u8))
      data
      digest);
  (pure digest)

end libcrux_sha3.portable


namespace libcrux_sha3

--  SHA3 384
def sha384_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (48 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ← (libcrux_sha3.portable.sha384 digest payload);
  (pure digest)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha384_ema.spec (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 payload))))
            (← (rust_primitives.hax.int.from_machine
              core_models.num.Impl_8.MAX))))
          &&? (← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 digest))))
            (← (hax_lib.int.Impl_7._unsafe_from_str "48"))))))
      (ensures := fun _ => pure True)
      (sha384_ema (digest : (RustSlice u8)) (payload : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  SHA3 384
def sha384 (data : (RustSlice u8)) : RustM (RustArray u8 48) := do
  let out : (RustArray u8 48) ←
    (rust_primitives.hax.repeat (0 : u8) (48 : usize));
  let out : (RustArray u8 48) ← (sha384_ema out data);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha384.spec (data : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 data))))
          (← (rust_primitives.hax.int.from_machine
            core_models.num.Impl_8.MAX))))
      (ensures := fun _ => pure True)
      (sha384 (data : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3


namespace libcrux_sha3.portable

--  A portable SHA3 512 implementation.
@[spec]
def sha512 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (libcrux_sha3.generic_keccak.portable.keccak1 ((72 : usize)) ((6 : u8))
      data
      digest);
  (pure digest)

end libcrux_sha3.portable


namespace libcrux_sha3

--  SHA3
def hash (LEN : usize) (algorithm : Algorithm) (payload : (RustSlice u8)) :
    RustM (RustArray u8 LEN) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let out : (RustArray u8 LEN) ← (rust_primitives.hax.repeat (0 : u8) LEN);
  let out : (RustArray u8 LEN) ←
    match algorithm with
      | (Algorithm.Sha224 ) => do (libcrux_sha3.portable.sha224 out payload)
      | (Algorithm.Sha256 ) => do (libcrux_sha3.portable.sha256 out payload)
      | (Algorithm.Sha384 ) => do (libcrux_sha3.portable.sha384 out payload)
      | (Algorithm.Sha512 ) => do (libcrux_sha3.portable.sha512 out payload);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def hash.spec (LEN : usize) (algorithm : Algorithm) (payload : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 payload))))
          (← (rust_primitives.hax.int.from_machine
            core_models.num.Impl_8.MAX))))
      (ensures := fun _ => pure True)
      (hash (LEN : usize) (algorithm : Algorithm) (payload : (RustSlice u8))) :=
{
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  SHA3 512
def sha512_ema (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 payload))
            <=? (← (rust_primitives.hax.cast_op
              core_models.num.Impl_8.MAX :
              RustM usize)))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 digest)) ==? (64 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let digest : (RustSlice u8) ← (libcrux_sha3.portable.sha512 digest payload);
  (pure digest)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha512_ema.spec (digest : (RustSlice u8)) (payload : (RustSlice u8)) :
    Spec
      (requires := do
        ((← (rust_primitives.hax.int.le
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 payload))))
            (← (rust_primitives.hax.int.from_machine
              core_models.num.Impl_8.MAX))))
          &&? (← (rust_primitives.hax.int.eq
            (← (rust_primitives.hax.int.from_machine
              (← (core_models.slice.Impl.len u8 digest))))
            (← (hax_lib.int.Impl_7._unsafe_from_str "64"))))))
      (ensures := fun _ => pure True)
      (sha512_ema (digest : (RustSlice u8)) (payload : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  SHA3 512
def sha512 (data : (RustSlice u8)) : RustM (RustArray u8 64) := do
  let out : (RustArray u8 64) ←
    (rust_primitives.hax.repeat (0 : u8) (64 : usize));
  let out : (RustArray u8 64) ← (sha512_ema out data);
  (pure out)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def sha512.spec (data : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 data))))
          (← (rust_primitives.hax.int.from_machine
            core_models.num.Impl_8.MAX))))
      (ensures := fun _ => pure True)
      (sha512 (data : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3


namespace libcrux_sha3.portable

--  A portable SHAKE128 implementation.
@[spec]
def shake128 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (libcrux_sha3.generic_keccak.portable.keccak1 ((168 : usize)) ((31 : u8))
      data
      digest);
  (pure digest)

end libcrux_sha3.portable


namespace libcrux_sha3

--  SHAKE 128
-- 
--  Note that the output length `BYTES` must fit into 32 bit. If it is longer,
--  the output will only return `u32::MAX` bytes.
@[spec]
def shake128 (BYTES : usize) (data : (RustSlice u8)) :
    RustM (RustArray u8 BYTES) := do
  let out : (RustArray u8 BYTES) ← (rust_primitives.hax.repeat (0 : u8) BYTES);
  let out : (RustArray u8 BYTES) ← (libcrux_sha3.portable.shake128 out data);
  (pure out)

--  SHAKE 128
-- 
--  Writes `out.len()` bytes.
@[spec]
def shake128_ema (out : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ← (libcrux_sha3.portable.shake128 out data);
  (pure out)

end libcrux_sha3


namespace libcrux_sha3.portable

--  A portable SHAKE256 implementation.
@[spec]
def shake256 (digest : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let digest : (RustSlice u8) ←
    (libcrux_sha3.generic_keccak.portable.keccak1 ((136 : usize)) ((31 : u8))
      data
      digest);
  (pure digest)

end libcrux_sha3.portable


namespace libcrux_sha3

--  SHAKE 256
-- 
--  Note that the output length `BYTES` must fit into 32 bit. If it is longer,
--  the output will only return `u32::MAX` bytes.
@[spec]
def shake256 (BYTES : usize) (data : (RustSlice u8)) :
    RustM (RustArray u8 BYTES) := do
  let out : (RustArray u8 BYTES) ← (rust_primitives.hax.repeat (0 : u8) BYTES);
  let out : (RustArray u8 BYTES) ← (libcrux_sha3.portable.shake256 out data);
  (pure out)

--  SHAKE 256
-- 
--  Writes `out.len()` bytes.
@[spec]
def shake256_ema (out : (RustSlice u8)) (data : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ← (libcrux_sha3.portable.shake256 out data);
  (pure out)

end libcrux_sha3


namespace libcrux_sha3.portable.incremental.private

class Sealed.AssociatedTypes (Self : Type) where

class Sealed (Self : Type)
  [associatedTypes : outParam (Sealed.AssociatedTypes (Self : Type))]
  where

end libcrux_sha3.portable.incremental.private


namespace libcrux_sha3.portable.incremental

--  SHAKE128 Xof state
structure Shake128Xof where
  state : (libcrux_sha3.generic_keccak.xof.KeccakXofState
      ((1 : usize))
      ((168 : usize))
      u64)

end libcrux_sha3.portable.incremental


namespace libcrux_sha3.portable.incremental.private

@[reducible] instance Impl.AssociatedTypes :
  Sealed.AssociatedTypes libcrux_sha3.portable.incremental.Shake128Xof
  where

instance Impl : Sealed libcrux_sha3.portable.incremental.Shake128Xof where

end libcrux_sha3.portable.incremental.private


namespace libcrux_sha3.portable.incremental

--  SHAKE256 Xof state
structure Shake256Xof where
  state : (libcrux_sha3.generic_keccak.xof.KeccakXofState
      ((1 : usize))
      ((136 : usize))
      u64)

end libcrux_sha3.portable.incremental


namespace libcrux_sha3.portable.incremental.private

@[reducible] instance Impl_1.AssociatedTypes :
  Sealed.AssociatedTypes libcrux_sha3.portable.incremental.Shake256Xof
  where

instance Impl_1 : Sealed libcrux_sha3.portable.incremental.Shake256Xof where

end libcrux_sha3.portable.incremental.private


namespace libcrux_sha3.portable.incremental

--  An XOF
class Xof.AssociatedTypes (Self : Type) (RATE : usize) where
  [trait_constr_Xof_i0 :
  libcrux_sha3.portable.incremental.private.Sealed.AssociatedTypes
  Self]

attribute [instance_reducible, instance] Xof.AssociatedTypes.trait_constr_Xof_i0

class Xof (Self : Type) (RATE : usize)
  [associatedTypes : outParam (Xof.AssociatedTypes (Self : Type) (RATE :
      usize))]
  where
  [trait_constr_Xof_i0 : libcrux_sha3.portable.incremental.private.Sealed Self]
  new (Self) (RATE) : (rust_primitives.hax.Tuple0 -> RustM Self)
  absorb (Self) (RATE) : (Self -> (RustSlice u8) -> RustM Self)
  absorb_final (Self) (RATE) : (Self -> (RustSlice u8) -> RustM Self)
  squeeze (Self) (RATE) :
    (Self ->
    (RustSlice u8) ->
    RustM (rust_primitives.hax.Tuple2 Self (RustSlice u8)))

attribute [instance_reducible, instance] Xof.trait_constr_Xof_i0

@[reducible] instance Impl.AssociatedTypes :
  Xof.AssociatedTypes Shake128Xof ((168 : usize))
  where

instance Impl : Xof Shake128Xof ((168 : usize)) where
  new := fun (_ : rust_primitives.hax.Tuple0) => do
    (pure (Shake128Xof.mk
      (state := (← (libcrux_sha3.generic_keccak.xof.Impl.new
        ((1 : usize))
        ((168 : usize))
        u64 rust_primitives.hax.Tuple0.mk)))))
  absorb := fun (self : Shake128Xof) (input : (RustSlice u8)) => do
    let self : Shake128Xof :=
      {self
      with state := (← (libcrux_sha3.generic_keccak.xof.Impl.absorb
        ((1 : usize))
        ((168 : usize))
        u64 (Shake128Xof.state self) (RustArray.ofVec #v[input])))};
    (pure self)
  absorb_final := fun (self : Shake128Xof) (input : (RustSlice u8)) => do
    let self : Shake128Xof :=
      {self
      with state := (← (libcrux_sha3.generic_keccak.xof.Impl.absorb_final
        ((1 : usize))
        ((168 : usize))
        u64
        ((31 : u8)) (Shake128Xof.state self) (RustArray.ofVec #v[input])))};
    (pure self)
  squeeze := fun (self : Shake128Xof) (out : (RustSlice u8)) => do
    let ⟨tmp0, tmp1⟩ ←
      (libcrux_sha3.generic_keccak.xof.Impl_1.squeeze ((168 : usize)) u64
        (Shake128Xof.state self)
        out);
    let self : Shake128Xof := {self with state := tmp0};
    let out : (RustSlice u8) := tmp1;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure (rust_primitives.hax.Tuple2.mk self out))

--  Shake256 XOF in absorb state
@[reducible] instance Impl_1.AssociatedTypes :
  Xof.AssociatedTypes Shake256Xof ((136 : usize))
  where

instance Impl_1 : Xof Shake256Xof ((136 : usize)) where
  new := fun (_ : rust_primitives.hax.Tuple0) => do
    (pure (Shake256Xof.mk
      (state := (← (libcrux_sha3.generic_keccak.xof.Impl.new
        ((1 : usize))
        ((136 : usize))
        u64 rust_primitives.hax.Tuple0.mk)))))
  absorb := fun (self : Shake256Xof) (input : (RustSlice u8)) => do
    let self : Shake256Xof :=
      {self
      with state := (← (libcrux_sha3.generic_keccak.xof.Impl.absorb
        ((1 : usize))
        ((136 : usize))
        u64 (Shake256Xof.state self) (RustArray.ofVec #v[input])))};
    (pure self)
  absorb_final := fun (self : Shake256Xof) (input : (RustSlice u8)) => do
    let self : Shake256Xof :=
      {self
      with state := (← (libcrux_sha3.generic_keccak.xof.Impl.absorb_final
        ((1 : usize))
        ((136 : usize))
        u64
        ((31 : u8)) (Shake256Xof.state self) (RustArray.ofVec #v[input])))};
    (pure self)
  squeeze := fun (self : Shake256Xof) (out : (RustSlice u8)) => do
    let ⟨tmp0, tmp1⟩ ←
      (libcrux_sha3.generic_keccak.xof.Impl_1.squeeze ((136 : usize)) u64
        (Shake256Xof.state self)
        out);
    let self : Shake256Xof := {self with state := tmp0};
    let out : (RustSlice u8) := tmp1;
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure (rust_primitives.hax.Tuple2.mk self out))

--  Create a new SHAKE-128 state object.
@[spec]
def shake128_init (_ : rust_primitives.hax.Tuple0) :
    RustM libcrux_sha3.portable.KeccakState := do
  (pure (libcrux_sha3.portable.KeccakState.mk
    (state := (← (libcrux_sha3.generic_keccak.Impl_2.new ((1 : usize)) u64
      rust_primitives.hax.Tuple0.mk)))))

--  Absorb
def shake128_absorb_final
    (s : libcrux_sha3.portable.KeccakState)
    (data0 : (RustSlice u8)) :
    RustM libcrux_sha3.portable.KeccakState := do
  let s : libcrux_sha3.portable.KeccakState :=
    {s
    with state := (← (libcrux_sha3.generic_keccak.Impl_2.absorb_final
      ((1 : usize))
      u64
      ((168 : usize))
      ((31 : u8))
      (libcrux_sha3.portable.KeccakState.state s)
      (RustArray.ofVec #v[data0])
      (0 : usize)
      (← (core_models.slice.Impl.len u8 data0))))};
  (pure s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      shake128_absorb_final.spec
      (s : libcrux_sha3.portable.KeccakState)
      (data0 : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.lt
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 data0))))
          (← (hax_lib.int.Impl_7._unsafe_from_str "168"))))
      (ensures := fun _ => pure True)
      (shake128_absorb_final
        (s : libcrux_sha3.portable.KeccakState)
        (data0 : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Squeeze three blocks
def shake128_squeeze_first_three_blocks
    (s : libcrux_sha3.portable.KeccakState)
    (out0 : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_sha3.generic_keccak.portable.Impl.squeeze_first_three_blocks
      ((168 : usize)) (libcrux_sha3.portable.KeccakState.state s) out0);
  let s : libcrux_sha3.portable.KeccakState := {s with state := tmp0};
  let out0 : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out0))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      shake128_squeeze_first_three_blocks.spec
      (s : libcrux_sha3.portable.KeccakState)
      (out0 : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.ge
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 out0))))
          (← (hax_lib.int.Impl_7._unsafe_from_str "504"))))
      (ensures := fun
          ⟨s_future, out0_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out0_future))
            ==? (← (core_models.slice.Impl.len u8 out0))))
      (shake128_squeeze_first_three_blocks
        (s : libcrux_sha3.portable.KeccakState)
        (out0 : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Squeeze five blocks
def shake128_squeeze_first_five_blocks
    (s : libcrux_sha3.portable.KeccakState)
    (out0 : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_sha3.generic_keccak.portable.Impl.squeeze_first_five_blocks
      ((168 : usize)) (libcrux_sha3.portable.KeccakState.state s) out0);
  let s : libcrux_sha3.portable.KeccakState := {s with state := tmp0};
  let out0 : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out0))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      shake128_squeeze_first_five_blocks.spec
      (s : libcrux_sha3.portable.KeccakState)
      (out0 : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.ge
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 out0))))
          (← (hax_lib.int.Impl_7._unsafe_from_str "840"))))
      (ensures := fun
          ⟨s_future, out0_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out0_future))
            ==? (← (core_models.slice.Impl.len u8 out0))))
      (shake128_squeeze_first_five_blocks
        (s : libcrux_sha3.portable.KeccakState)
        (out0 : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Squeeze another block
def shake128_squeeze_next_block
    (s : libcrux_sha3.portable.KeccakState)
    (out0 : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_sha3.generic_keccak.portable.Impl.squeeze_next_block
      ((168 : usize))
      (libcrux_sha3.portable.KeccakState.state s)
      out0
      (0 : usize));
  let s : libcrux_sha3.portable.KeccakState := {s with state := tmp0};
  let out0 : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out0))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      shake128_squeeze_next_block.spec
      (s : libcrux_sha3.portable.KeccakState)
      (out0 : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.ge
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 out0))))
          (← (hax_lib.int.Impl_7._unsafe_from_str "168"))))
      (ensures := fun
          ⟨s_future, out0_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out0_future))
            ==? (← (core_models.slice.Impl.len u8 out0))))
      (shake128_squeeze_next_block
        (s : libcrux_sha3.portable.KeccakState)
        (out0 : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Create a new SHAKE-256 state object.
@[spec]
def shake256_init (_ : rust_primitives.hax.Tuple0) :
    RustM libcrux_sha3.portable.KeccakState := do
  (pure (libcrux_sha3.portable.KeccakState.mk
    (state := (← (libcrux_sha3.generic_keccak.Impl_2.new ((1 : usize)) u64
      rust_primitives.hax.Tuple0.mk)))))

--  Absorb some data for SHAKE-256 for the last time
def shake256_absorb_final
    (s : libcrux_sha3.portable.KeccakState)
    (data : (RustSlice u8)) :
    RustM libcrux_sha3.portable.KeccakState := do
  let s : libcrux_sha3.portable.KeccakState :=
    {s
    with state := (← (libcrux_sha3.generic_keccak.Impl_2.absorb_final
      ((1 : usize))
      u64
      ((136 : usize))
      ((31 : u8))
      (libcrux_sha3.portable.KeccakState.state s)
      (RustArray.ofVec #v[data])
      (0 : usize)
      (← (core_models.slice.Impl.len u8 data))))};
  (pure s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      shake256_absorb_final.spec
      (s : libcrux_sha3.portable.KeccakState)
      (data : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.lt
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 data))))
          (← (hax_lib.int.Impl_7._unsafe_from_str "136"))))
      (ensures := fun _ => pure True)
      (shake256_absorb_final
        (s : libcrux_sha3.portable.KeccakState)
        (data : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Squeeze the first SHAKE-256 block
def shake256_squeeze_first_block
    (s : libcrux_sha3.portable.KeccakState)
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let out : (RustSlice u8) ←
    (libcrux_sha3.generic_keccak.portable.Impl.squeeze_first_block
      ((136 : usize)) (libcrux_sha3.portable.KeccakState.state s) out);
  (pure (rust_primitives.hax.Tuple2.mk s out))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      shake256_squeeze_first_block.spec
      (s : libcrux_sha3.portable.KeccakState)
      (out : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.ge
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 out))))
          (← (hax_lib.int.Impl_7._unsafe_from_str "136"))))
      (ensures := fun
          ⟨s_future, out_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out_future))
            ==? (← (core_models.slice.Impl.len u8 out))))
      (shake256_squeeze_first_block
        (s : libcrux_sha3.portable.KeccakState)
        (out : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

--  Squeeze the next SHAKE-256 block
def shake256_squeeze_next_block
    (s : libcrux_sha3.portable.KeccakState)
    (out : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      libcrux_sha3.portable.KeccakState
      (RustSlice u8))
    := do
  let ⟨tmp0, tmp1⟩ ←
    (libcrux_sha3.generic_keccak.portable.Impl.squeeze_next_block
      ((136 : usize))
      (libcrux_sha3.portable.KeccakState.state s)
      out
      (0 : usize));
  let s : libcrux_sha3.portable.KeccakState := {s with state := tmp0};
  let out : (RustSlice u8) := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure (rust_primitives.hax.Tuple2.mk s out))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      shake256_squeeze_next_block.spec
      (s : libcrux_sha3.portable.KeccakState)
      (out : (RustSlice u8)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.ge
          (← (rust_primitives.hax.int.from_machine
            (← (core_models.slice.Impl.len u8 out))))
          (← (hax_lib.int.Impl_7._unsafe_from_str "136"))))
      (ensures := fun
          ⟨s_future, out_future⟩ => do
          ((← (core_models.slice.Impl.len u8 out_future))
            ==? (← (core_models.slice.Impl.len u8 out))))
      (shake256_squeeze_next_block
        (s : libcrux_sha3.portable.KeccakState)
        (out : (RustSlice u8))) := {
  pureRequires := by sorry
  pureEnsures := by sorry
  contract := by sorry
}

end libcrux_sha3.portable.incremental

