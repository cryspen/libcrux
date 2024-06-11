module Libcrux_ml_kem.Vector
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  ()

/// Values having this type hold a representative 'x' of the Kyber field.
/// We use 'fe' as a shorthand for this type.
unfold
let t_FieldElement = i16

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
unfold
let t_FieldElementTimesMontgomeryR = i16

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R^(-1) (mod FIELD_MODULUS).
/// We use 'mfe' as a shorthand for this type
unfold
let t_MontgomeryFieldElement = i16

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
let v_BARRETT_MULTIPLIER: i32 = Rust_primitives.Hax.dropped_body

let v_BARRETT_R: i32 = Rust_primitives.Hax.dropped_body

let v_BARRETT_SHIFT: i32 = Rust_primitives.Hax.dropped_body

let v_MONTGOMERY_R: i32 = Rust_primitives.Hax.dropped_body

let v_MONTGOMERY_SHIFT: u8 = Rust_primitives.Hax.dropped_body

/// Signed Barrett Reduction
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
val barrett_reduce_element (value: i16)
    : Prims.Pure i16
      (requires
        (Core.Convert.f_from #i32 #i16 value <: i32) >. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i32) &&
        (Core.Convert.f_from #i32 #i16 value <: i32) <. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i16 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) &&
          result <. Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS)

val compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i16
      (requires
        Rust_primitives.Hax.failure ""
          "{ Types.attributes = [];\n  contents =\n  Types.Literal {\n    lit =\n    { Types.node = Types.Err;\n      span =\n      { Types.filename =\n        (Types.Real (Types.LocalPath \"libcrux-ml-kem/src/lib.rs\"));\n        hi = { Types.col = \"0\"; line = \"1\" };\n        lo = { Types.col = \"0\"; line = \"1\" } }\n      };\n    neg = false};\n  hir_id = None;\n  span =\n  { Types.filename =\n    (Types.Real (Types.LocalPath \"libcrux-ml-kem/src/vector.rs\"));\n    hi = { Types.col = \"55\"; line = \"182\" };\n    lo = { Types.col = \"4\"; line = \"177\" } };\n  ty = Types.Never }"
        )
      (ensures
        fun result ->
          let result:i16 = result in
          result >=. 0s &&
          result <. (Core.Num.impl__i16__pow 2s (cast (coefficient_bits <: u8) <: u32) <: i16))

/// The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.5), which is defined as:
/// ```plaintext
/// Compress_d: ℤq -> ℤ_{2ᵈ}
/// Compress_d(x) = ⌈(2ᵈ/q)·x⌋
/// ```
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
/// ```plaintext
/// Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
///               = ⌊(2^{d+1}·x + q) / 2q⌋
/// ```
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val compress_message_coefficient (fe: u16)
    : Prims.Pure u8
      (requires
        Rust_primitives.Hax.failure ""
          "{ Types.attributes = [];\n  contents =\n  Types.Literal {\n    lit =\n    { Types.node = Types.Err;\n      span =\n      { Types.filename =\n        (Types.Real (Types.LocalPath \"libcrux-ml-kem/src/lib.rs\"));\n        hi = { Types.col = \"0\"; line = \"1\" };\n        lo = { Types.col = \"0\"; line = \"1\" } }\n      };\n    neg = false};\n  hir_id = None;\n  span =\n  { Types.filename =\n    (Types.Real (Types.LocalPath \"libcrux-ml-kem/src/vector.rs\"));\n    hi = { Types.col = \"80\"; line = \"146\" };\n    lo = { Types.col = \"16\"; line = \"146\" } };\n  ty = Types.Never }"
        )
      (ensures
        fun result ->
          let result:u8 = result in
          Hax_lib.implies ((833us <=. fe <: bool) && (fe <=. 2596us <: bool))
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 1uy <: bool) &&
          Hax_lib.implies (~.((833us <=. fe <: bool) && (fe <=. 2596us <: bool)) <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 0uy <: bool))

val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. v_MONTGOMERY_SHIFT)
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into #u8 #u32 n <: u32) <: u32))

/// If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
/// `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
/// `x · y`, as follows:
///    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`
/// `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a representative
/// `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod FIELD_MODULUS)`.
val montgomery_multiply_fe_by_fer (fe fer: i16)
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

/// Signed Montgomery Reduction
/// Given an input `value`, `montgomery_reduce` outputs a representative `o`
/// such that:
/// - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
/// - the absolute value of `o` is bound as follows:
/// `|result| ≤ (|value| / MONTGOMERY_R) + (FIELD_MODULUS / 2)
/// In particular, if `|value| ≤ FIELD_MODULUS * MONTGOMERY_R`, then `|o| < (3 · FIELD_MODULUS) / 2`.
val montgomery_reduce_element (value: i32)
    : Prims.Pure i16
      (requires
        Rust_primitives.Hax.failure ""
          "{ Types.attributes = [];\n  contents =\n  Types.Literal {\n    lit =\n    { Types.node = Types.Err;\n      span =\n      { Types.filename =\n        (Types.Real (Types.LocalPath \"libcrux-ml-kem/src/lib.rs\"));\n        hi = { Types.col = \"0\"; line = \"1\" };\n        lo = { Types.col = \"0\"; line = \"1\" } }\n      };\n    neg = false};\n  hir_id = None;\n  span =\n  { Types.filename =\n    (Types.Real (Types.LocalPath \"libcrux-ml-kem/src/vector.rs\"));\n    hi = { Types.col = \"114\"; line = \"80\" };\n    lo = { Types.col = \"16\"; line = \"80\" } };\n  ty = Types.Never }"
        )
      (ensures
        fun result ->
          let result:i16 = result in
          result >=.
          ((Core.Ops.Arith.Neg.neg (3s *! Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16)
              <:
              i16) /!
            2s
            <:
            i16) &&
          result <=. ((3s *! Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) /! 2s <: i16))

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val ntt_multiply_binomials: (i16 & i16) -> (i16 & i16) -> zeta: i16
  -> Prims.Pure (i16 & i16) Prims.l_True (fun _ -> Prims.l_True)

val rej_sample (a: t_Slice u8) (result: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize) Prims.l_True (fun _ -> Prims.l_True)

val add (lhs rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val barrett_reduce (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val bitwise_and_with_constant (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val compress (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val compress_1_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val cond_subtract_3329_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_1_ (v: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_10_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_11_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_12_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_4_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_5_ (bytes: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val from_i16_array (array: t_Slice i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_layer_2_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val inv_ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val montgomery_multiply_by_constant (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val multiply_by_constant (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_2_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_multiply
      (lhs rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 2)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_10_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 20)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_11_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 22)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 24)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_4_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 8)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)

val shift_right (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val sub (lhs rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)

val zero: Prims.unit
  -> Prims.Pure Libcrux_ml_kem.Vector.Portable.t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_kem.Vector.Traits.t_Operations Libcrux_ml_kem.Vector.Portable.t_PortableVector =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post
    =
    (fun (_: Prims.unit) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_ZERO = (fun (_: Prims.unit) -> zero ());
    f_from_i16_array_pre = (fun (array: t_Slice i16) -> true);
    f_from_i16_array_post
    =
    (fun (array: t_Slice i16) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_from_i16_array = (fun (array: t_Slice i16) -> from_i16_array array);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        add lhs rhs);
    f_sub_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_sub_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_sub
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        sub lhs rhs);
    f_multiply_by_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16) -> true);
    f_multiply_by_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (c: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_multiply_by_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16) -> multiply_by_constant v c);
    f_bitwise_and_with_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (c: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_bitwise_and_with_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16) ->
        bitwise_and_with_constant v c);
    f_shift_right_pre
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_shift_right_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_shift_right
    =
    (fun (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) ->
        shift_right v_SHIFT_BY v);
    f_cond_subtract_3329_pre = (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_cond_subtract_3329_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_cond_subtract_3329_
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> cond_subtract_3329_ v);
    f_barrett_reduce_pre = (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_barrett_reduce_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_barrett_reduce
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> barrett_reduce v);
    f_montgomery_multiply_by_constant_pre
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (r: i16) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (r: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_montgomery_multiply_by_constant
    =
    (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (r: i16) ->
        montgomery_multiply_by_constant v r);
    f_compress_1_pre = (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_compress_1_post
    =
    (fun
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_compress_1_ = (fun (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> compress_1_ v);
    f_compress_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_compress_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_compress
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) ->
        compress v_COEFFICIENT_BITS v);
    f_decompress_ciphertext_coefficient_pre
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_decompress_ciphertext_coefficient_post
    =
    (fun
        (v_COEFFICIENT_BITS: i32)
        (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_decompress_ciphertext_coefficient
    =
    (fun (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) ->
        decompress_ciphertext_coefficient v_COEFFICIENT_BITS v);
    f_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        true);
    f_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3);
    f_ntt_layer_2_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0: i16) (zeta1: i16) -> true);
    f_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_ntt_layer_2_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0: i16) (zeta1: i16) ->
        ntt_layer_2_step a zeta0 zeta1);
    f_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16) -> true);
    f_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_ntt_layer_3_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16) -> ntt_layer_3_step a zeta
    );
    f_inv_ntt_layer_1_step_pre
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        true);
    f_inv_ntt_layer_1_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_inv_ntt_layer_1_step
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        inv_ntt_layer_1_step a zeta0 zeta1 zeta2 zeta3);
    f_inv_ntt_layer_2_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0: i16) (zeta1: i16) -> true);
    f_inv_ntt_layer_2_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_inv_ntt_layer_2_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0: i16) (zeta1: i16) ->
        inv_ntt_layer_2_step a zeta0 zeta1);
    f_inv_ntt_layer_3_step_pre
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16) -> true);
    f_inv_ntt_layer_3_step_post
    =
    (fun
        (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_inv_ntt_layer_3_step
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16) ->
        inv_ntt_layer_3_step a zeta);
    f_ntt_multiply_pre
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        true);
    f_ntt_multiply_post
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        ->
        true);
    f_ntt_multiply
    =
    (fun
        (lhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
        (zeta0: i16)
        (zeta1: i16)
        (zeta2: i16)
        (zeta3: i16)
        ->
        ntt_multiply lhs rhs zeta0 zeta1 zeta2 zeta3);
    f_serialize_1_pre = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_serialize_1_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (out: t_Array u8 (sz 2)) -> true);
    f_serialize_1_ = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> serialize_1_ a);
    f_deserialize_1_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_1_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_deserialize_1_ = (fun (a: t_Slice u8) -> deserialize_1_ a);
    f_serialize_4_pre = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_serialize_4_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (out: t_Array u8 (sz 8)) -> true);
    f_serialize_4_ = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> serialize_4_ a);
    f_deserialize_4_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_4_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_deserialize_4_ = (fun (a: t_Slice u8) -> deserialize_4_ a);
    f_serialize_5_pre = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_serialize_5_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (out: t_Array u8 (sz 10)) -> true);
    f_serialize_5_ = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> serialize_5_ a);
    f_deserialize_5_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_5_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_deserialize_5_ = (fun (a: t_Slice u8) -> deserialize_5_ a);
    f_serialize_10_pre = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_serialize_10_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (out: t_Array u8 (sz 20)) -> true);
    f_serialize_10_ = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> serialize_10_ a);
    f_deserialize_10_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_10_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_deserialize_10_ = (fun (a: t_Slice u8) -> deserialize_10_ a);
    f_serialize_11_pre = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_serialize_11_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (out: t_Array u8 (sz 22)) -> true);
    f_serialize_11_ = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> serialize_11_ a);
    f_deserialize_11_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_11_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_deserialize_11_ = (fun (a: t_Slice u8) -> deserialize_11_ a);
    f_serialize_12_pre = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_serialize_12_post
    =
    (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (out: t_Array u8 (sz 24)) -> true);
    f_serialize_12_ = (fun (a: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> serialize_12_ a);
    f_deserialize_12_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_12_post
    =
    (fun (a: t_Slice u8) (out: Libcrux_ml_kem.Vector.Portable.t_PortableVector) -> true);
    f_deserialize_12_ = (fun (a: t_Slice u8) -> deserialize_12_ a);
    f_rej_sample_pre = (fun (a: t_Slice u8) (out: t_Slice i16) -> true);
    f_rej_sample_post
    =
    (fun (a: t_Slice u8) (out: t_Slice i16) (out2: (t_Slice i16 & usize)) -> true);
    f_rej_sample
    =
    fun (a: t_Slice u8) (out: t_Slice i16) ->
      let tmp0, out1:(t_Slice i16 & usize) = rej_sample a out in
      let out:t_Slice i16 = tmp0 in
      let hax_temp_output:usize = out1 in
      out, hax_temp_output <: (t_Slice i16 & usize)
  }
