module Libcrux_ml_kem.Vector.Portable.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

#push-options "--z3rlimit 200 --ext context_pruning"

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16) =
  let compressed:u64 = (cast (fe <: u16) <: u64) <<! coefficient_bits in
  let compressed:u64 = compressed +! mk_u64 1664 in
  let compressed:u64 = compressed *! mk_u64 10321340 in
  let compressed:u64 = compressed >>! mk_i32 35 in
  cast (Libcrux_ml_kem.Vector.Portable.Arithmetic.get_n_least_significant_bits coefficient_bits
        (cast (compressed <: u64) <: u32)
      <:
      u32)
  <:
  i16

#pop-options

#push-options "--z3rlimit 200 --ext context_pruning"

let compress_message_coefficient (fe: u16) =
  let (shifted: i16):i16 = mk_i16 1664 -! (cast (fe <: u16) <: i16) in
  let _:Prims.unit = assert (v shifted == 1664 - v fe) in
  let mask:i16 = shifted >>! mk_i32 15 in
  let _:Prims.unit =
    assert (v mask = v shifted / pow2 15);
    assert (if v shifted < 0 then mask = ones else mask = zero)
  in
  let shifted_to_positive:i16 = mask ^. shifted in
  let _:Prims.unit =
    logxor_lemma shifted mask;
    assert (v shifted < 0 ==> v shifted_to_positive = v (lognot shifted));
    neg_equiv_lemma shifted;
    assert (v (lognot shifted) = - (v shifted) - 1);
    assert (v shifted >= 0 ==> v shifted_to_positive = v (mask `logxor` shifted));
    assert (v shifted >= 0 ==> mask = zero);
    assert (v shifted >= 0 ==> mask ^. shifted = shifted);
    assert (v shifted >= 0 ==> v shifted_to_positive = v shifted);
    assert (shifted_to_positive >=. mk_i16 0)
  in
  let shifted_positive_in_range:i16 = shifted_to_positive -! mk_i16 832 in
  let _:Prims.unit =
    assert (1664 - v fe >= 0 ==> v shifted_positive_in_range == 832 - v fe);
    assert (1664 - v fe < 0 ==> v shifted_positive_in_range == - 2497 + v fe)
  in
  let r0:i16 = shifted_positive_in_range >>! mk_i32 15 in
  let (r1: i16):i16 = r0 &. mk_i16 1 in
  let res:u8 = cast (r1 <: i16) <: u8 in
  let _:Prims.unit =
    assert (v r0 = v shifted_positive_in_range / pow2 15);
    assert (if v shifted_positive_in_range < 0 then r0 = ones else r0 = zero);
    logand_lemma (mk_i16 1) r0;
    assert (if v shifted_positive_in_range < 0 then r1 = mk_i16 1 else r1 = mk_i16 0);
    assert ((v fe >= 833 && v fe <= 2496) ==> r1 = mk_i16 1);
    assert (v fe < 833 ==> r1 = mk_i16 0);
    assert (v fe > 2496 ==> r1 = mk_i16 0);
    assert (v res = v r1)
  in
  res

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 2000"

let compress
      (v_COEFFICIENT_BITS: i32)
      (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let _:Prims.unit =
    assert (v (cast (v_COEFFICIENT_BITS) <: u8) == v v_COEFFICIENT_BITS);
    assert (v (cast (v_COEFFICIENT_BITS) <: u32) == v v_COEFFICIENT_BITS);
    assert (v (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) <: u16) == 3329)
  in
  let _:Prims.unit =
    assert (forall (i: nat).
          i < 16 ==>
          (cast (a.f_elements.[ sz i ]) <: u16) <.
          (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) <: u16))
  in
  let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun a i ->
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          (v i < 16 ==>
            (forall (j: nat).
                (j >= v i /\ j < 16) ==>
                v (cast (a.f_elements.[ sz j ]) <: u16) <
                v (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) <: u16))) /\
          (forall (j: nat).
              j < v i ==>
              v (a.f_elements.[ sz j ] <: i16) >= 0 /\
              v (a.f_elements.[ sz j ] <: i16) < pow2 (v (cast (v_COEFFICIENT_BITS) <: u32))))
      a
      (fun a i ->
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              a with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (compress_ciphertext_coefficient (cast (v_COEFFICIENT_BITS <: i32) <: u8)
                    (cast (a.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                      <:
                      u16)
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          let _:Prims.unit =
            assert (v (a.f_elements.[ i ] <: i16) >= 0 /\
                v (a.f_elements.[ i ] <: i16) < pow2 (v (cast (v_COEFFICIENT_BITS) <: u32)))
          in
          a)
  in
  let _:Prims.unit =
    assert (forall (i: nat).
          i < 16 ==>
          v (a.f_elements.[ sz i ] <: i16) >= 0 /\
          v (a.f_elements.[ sz i ] <: i16) < pow2 (v v_COEFFICIENT_BITS))
  in
  a

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 2000"

let compress_message_coefficient_range_helper (fe: u16) : Lemma
  (requires fe <. (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) <: u16))
  (ensures v (cast (compress_message_coefficient fe) <: i16) >= 0 /\
    v (cast (compress_message_coefficient fe) <: i16) < 2) =
  assert (v (cast (compress_message_coefficient fe) <: i16) >= 0 /\
    v (cast (compress_message_coefficient fe) <: i16) < 2)

let compress_1_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let _:Prims.unit =
    assert (forall (i: nat).
          i < 16 ==>
          (cast (a.f_elements.[ sz i ]) <: u16) <.
          (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) <: u16))
  in
  let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun a i ->
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          (v i < 16 ==>
            (forall (j: nat).
                (j >= v i /\ j < 16) ==>
                v (cast (a.f_elements.[ sz j ]) <: u16) <
                v (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS) <: u16))) /\
          (forall (j: nat).
              j < v i ==>
              v (a.f_elements.[ sz j ] <: i16) >= 0 /\ v (a.f_elements.[ sz j ] <: i16) < 2))
      a
      (fun a i ->
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          let _:Prims.unit =
            compress_message_coefficient_range_helper (cast (a.f_elements.[ i ]) <: u16)
          in
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              a with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (cast (compress_message_coefficient (cast (a
                                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                              <:
                              i16)
                          <:
                          u16)
                      <:
                      u8)
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          let _:Prims.unit =
            assert (v (a.f_elements.[ i ] <: i16) >= 0 /\ v (a.f_elements.[ i ] <: i16) < 2)
          in
          a)
  in
  let _:Prims.unit =
    assert (forall (i: nat).
          i < 16 ==> v (a.f_elements.[ sz i ] <: i16) >= 0 /\ v (a.f_elements.[ sz i ] <: i16) < 2)
  in
  a

#pop-options

#push-options "--z3rlimit 300 --ext context_pruning"

let decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let _:Prims.unit =
    assert_norm (pow2 1 == 2);
    assert_norm (pow2 4 == 16);
    assert_norm (pow2 5 == 32);
    assert_norm (pow2 10 == 1024);
    assert_norm (pow2 11 == 2048)
  in
  let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun a i ->
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          (v i < 16 ==>
            (forall (j: nat).
                (j >= v i /\ j < 16) ==>
                v (Seq.index a.f_elements j) >= 0 /\
                v (Seq.index a.f_elements j) < pow2 (v v_COEFFICIENT_BITS))) /\
          (forall (j: nat).
              j < v i ==>
              v (Seq.index a.f_elements j) < v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS))
      a
      (fun a i ->
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = a in
          let i:usize = i in
          let _:Prims.unit =
            assert (v (a.f_elements.[ i ] <: i16) < pow2 11);
            assert (v (a.f_elements.[ i ] <: i16) == v (cast (a.f_elements.[ i ] <: i16) <: i32));
            assert (v (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) ==
                v (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32));
            assert (v ((cast (a.f_elements.[ i ] <: i16) <: i32) *!
                    (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32)) ==
                v (cast (a.f_elements.[ i ] <: i16) <: i32) *
                v (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32))
          in
          let decompressed:i32 =
            (cast (a.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: i32) *!
            (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32)
          in
          let _:Prims.unit =
            assert (v (decompressed <<! mk_i32 1) == v decompressed * 2);
            assert (v (mk_i32 1 <<! v_COEFFICIENT_BITS) == pow2 (v v_COEFFICIENT_BITS));
            assert (v ((decompressed <<! mk_i32 1) +! (mk_i32 1 <<! v_COEFFICIENT_BITS)) ==
                v (decompressed <<! mk_i32 1) + v (mk_i32 1 <<! v_COEFFICIENT_BITS))
          in
          let decompressed:i32 =
            (decompressed <<! mk_i32 1 <: i32) +! (mk_i32 1 <<! v_COEFFICIENT_BITS <: i32)
          in
          let _:Prims.unit =
            assert (v (v_COEFFICIENT_BITS +! mk_i32 1) == v v_COEFFICIENT_BITS + 1);
            assert (v (decompressed >>! (v_COEFFICIENT_BITS +! mk_i32 1 <: i32)) ==
                v decompressed / pow2 (v v_COEFFICIENT_BITS + 1))
          in
          let decompressed:i32 = decompressed >>! (v_COEFFICIENT_BITS +! mk_i32 1 <: i32) in
          let _:Prims.unit =
            assert (v decompressed < v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS);
            assert (v (cast decompressed <: i16) < v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS)
          in
          let a:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              a with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (cast (decompressed <: i32) <: i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          a)
  in
  a

#pop-options
