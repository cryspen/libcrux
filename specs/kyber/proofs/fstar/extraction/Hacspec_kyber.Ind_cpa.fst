module Hacspec_kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_KeyPair = {
  f_sk:array u8 (sz 1152);
  f_pk:array u8 (sz 1184)
}

let impl__new (sk: array u8 (sz 1152)) (pk: array u8 (sz 1184)) : t_KeyPair =
  { f_sk = sk; f_pk = pk }

let impl__serialize_secret_key (self: t_KeyPair) (implicit_rejection_value: array u8 (sz 32))
    : array u8 (sz 2400) =
  Core.Convert.f_into (Hacspec_lib.f_push (Hacspec_lib.f_push (Hacspec_lib.f_push (Hacspec_lib.f_push
                    (Hacspec_lib.impl_6__new (Rust_primitives.Hax.repeat 0uy (sz 2400)
                          <:
                          array u8 (sz 2400))
                      <:
                      Hacspec_lib.t_UpdatableArray (sz 2400))
                    (Rust_primitives.unsize self.f_sk <: slice u8)
                  <:
                  Hacspec_lib.t_UpdatableArray (sz 2400))
                (Rust_primitives.unsize self.f_pk <: slice u8)
              <:
              Hacspec_lib.t_UpdatableArray (sz 2400))
            (Rust_primitives.unsize (Hacspec_kyber.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                        self.f_pk
                      <:
                      slice u8)
                  <:
                  array u8 (sz 32))
              <:
              slice u8)
          <:
          Hacspec_lib.t_UpdatableArray (sz 2400))
        (Rust_primitives.unsize implicit_rejection_value <: slice u8)
      <:
      Hacspec_lib.t_UpdatableArray (sz 2400))

let impl__pk (self: t_KeyPair) : array u8 (sz 1184) = self.f_pk

let generate_keypair (key_generation_seed: array u8 (sz 32))
    : Core.Result.t_Result t_KeyPair Hacspec_kyber.t_BadRejectionSamplingRandomnessError =
  let hashed:array u8 (sz 64) =
    Hacspec_kyber.Parameters.Hash_functions.v_G (Rust_primitives.unsize key_generation_seed
        <:
        slice u8)
  in
  let seed_for_A, seed_for_secret_and_error:(slice u8 & slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: slice u8) (sz 32)
  in
  let (domain_separator: u8):u8 = 0uy in
  let v_A_as_ntt:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
    (sz 3) =
    Rust_primitives.Hax.repeat Hacspec_lib.Vector.impl__ZERO (sz 3)
  in
  let (xof_input: array u8 (sz 34)):array u8 (sz 34) = Hacspec_lib.f_into_padded_array seed_for_A in
  let v_A_as_ntt, xof_input:(array
      (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
      (sz 3) &
    array u8 (sz 34)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_kyber.Parameters.v_RANK
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (v_A_as_ntt, xof_input)
      (fun (v_A_as_ntt, xof_input) i ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = Hacspec_kyber.Parameters.v_RANK
                  })
              <:
              (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
            (v_A_as_ntt, xof_input)
            (fun (v_A_as_ntt, xof_input) j ->
                let xof_input:array u8 (sz 34) =
                  Rust_primitives.Hax.update_at xof_input (sz 32) (Hacspec_lib.f_as_u8 i <: u8)
                in
                let xof_input:array u8 (sz 34) =
                  Rust_primitives.Hax.update_at xof_input (sz 33) (Hacspec_lib.f_as_u8 j <: u8)
                in
                let (xof_bytes: array u8 (sz 840)):array u8 (sz 840) =
                  Hacspec_kyber.Parameters.Hash_functions.v_XOF (Rust_primitives.unsize xof_input
                      <:
                      slice u8)
                in
                let* hoist2:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                  match
                    Core.Ops.Try_trait.f_branch (Hacspec_kyber.Sampling.sample_ntt xof_bytes
                        <:
                        Core.Result.t_Result
                          (Hacspec_lib.Ring.t_PolynomialRingElement
                              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
                          Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
                  with
                  | Core.Ops.Control_flow.ControlFlow_Break residual ->
                    let* hoist1:Rust_primitives.Hax.t_Never =
                      Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                          <:
                          Core.Result.t_Result t_KeyPair
                            Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
                    in
                    Core.Ops.Control_flow.ControlFlow_Continue
                    (Rust_primitives.Hax.never_to_any hoist1)
                  | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                    Core.Ops.Control_flow.ControlFlow_Continue v_val
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (let hoist3:Hacspec_lib.Vector.t_Vector
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
                    Rust_primitives.Hax.update_at (v_A_as_ntt.[ i ]
                        <:
                        Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                          (sz 256)
                          (sz 3))
                      j
                      hoist2
                  in
                  let hoist4:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        (sz 256)
                        (sz 3)) (sz 3) =
                    Rust_primitives.Hax.update_at v_A_as_ntt i hoist3
                  in
                  let v_A_as_ntt:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        (sz 256)
                        (sz 3)) (sz 3) =
                    hoist4
                  in
                  v_A_as_ntt, xof_input))
          <:
          (array
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                  (sz 256)
                  (sz 3)) (sz 3) &
            array u8 (sz 34)))
  in
  let secret:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let (prf_input: array u8 (sz 33)):array u8 (sz 33) =
    Hacspec_lib.f_into_padded_array seed_for_secret_and_error
  in
  let domain_separator, prf_input, secret:(u8 & array u8 (sz 33) &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_lib.Vector.impl__len secret <: usize
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, prf_input, secret)
      (fun (domain_separator, prf_input, secret) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 (sz 128)):array u8 (sz 128) =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let secret:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256)
            (sz 3) =
            Rust_primitives.Hax.update_at secret
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd (sz 2)
                  (prf_output.[ Core.Ops.Range.RangeFull ] <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          in
          domain_separator, prf_input, secret)
  in
  let error:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let domain_separator, error, prf_input:(u8 &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) &
    array u8 (sz 33)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_lib.Vector.impl__len error <: usize
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, error, prf_input)
      (fun (domain_separator, error, prf_input) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 (sz 128)):array u8 (sz 128) =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let error:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256)
            (sz 3) =
            Rust_primitives.Hax.update_at error
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd (sz 2)
                  (prf_output.[ Core.Ops.Range.RangeFull ] <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          in
          domain_separator, error, prf_input)
  in
  let secret_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_kyber.Ntt.vector_ntt secret
  in
  let error_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_kyber.Ntt.vector_ntt error
  in
  let tt_as_ntt =
    (Hacspec_kyber.Matrix.multiply_matrix_by_column v_A_as_ntt secret_as_ntt
      <:
      Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)) +!
    error_as_ntt
  in
  let public_key_serialized:array u8 (sz 1184) =
    Hacspec_lib.impl_6__array (Hacspec_lib.f_push (Hacspec_lib.f_push (Hacspec_lib.impl_6__new (Rust_primitives.Hax.repeat
                      0uy
                      (sz 1184)
                    <:
                    array u8 (sz 1184))
                <:
                Hacspec_lib.t_UpdatableArray (sz 1184))
              (Rust_primitives.unsize (Hacspec_kyber.Serialize.vector_encode_12_ tt_as_ntt
                    <:
                    array u8 (sz 1152))
                <:
                slice u8)
            <:
            Hacspec_lib.t_UpdatableArray (sz 1184))
          seed_for_A
        <:
        Hacspec_lib.t_UpdatableArray (sz 1184))
  in
  let secret_key_serialized:array u8 (sz 1152) =
    Hacspec_kyber.Serialize.vector_encode_12_ secret_as_ntt
  in
  Core.Result.Result_Ok
  (impl__new (Hacspec_lib.f_into_array (Rust_primitives.unsize secret_key_serialized <: slice u8)
        <:
        array u8 (sz 1152))
      (Hacspec_lib.f_into_array (Rust_primitives.unsize public_key_serialized <: slice u8)
        <:
        array u8 (sz 1184)))

let encode_and_compress_u
      (input:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
        )
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new in
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Hacspec_lib.Vector.impl__into_iter
              input
            <:
            Core.Array.Iter.t_IntoIter
              (Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Array.Iter.t_IntoIter
              (Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3)))
          .f_IntoIter)
      out
      (fun out re ->
          Alloc.Vec.impl_2__extend_from_slice out
            (Core.Ops.Deref.f_deref (Hacspec_kyber.Serialize.byte_encode Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                    (Hacspec_kyber.Compress.compress re
                        Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                      <:
                      Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  in
  out

let encrypt (public_key: array u8 (sz 1184)) (message randomness: array u8 (sz 32))
    : Core.Result.t_Result (array u8 (sz 1088)) Hacspec_kyber.t_BadRejectionSamplingRandomnessError =
  let (domain_separator: u8):u8 = 0uy in
  let tt_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let tt_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks (public_key.[ {
                        Core.Ops.Range.f_end = Hacspec_kyber.Parameters.v_T_AS_NTT_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8)))
          .f_IntoIter)
      tt_as_ntt
      (fun tt_as_ntt (i, tt_as_ntt_bytes) ->
          Rust_primitives.Hax.update_at tt_as_ntt
            i
            (Hacspec_kyber.Serialize.byte_decode (sz 12) tt_as_ntt_bytes
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
      )
  in
  let seed_for_A:slice u8 =
    public_key.[ { Core.Ops.Range.f_start = Hacspec_kyber.Parameters.v_T_AS_NTT_ENCODED_SIZE } ]
  in
  let v_A_as_ntt:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
    (sz 3) =
    Rust_primitives.Hax.repeat Hacspec_lib.Vector.impl__ZERO (sz 3)
  in
  let (xof_input: array u8 (sz 34)):array u8 (sz 34) = Hacspec_lib.f_into_padded_array seed_for_A in
  let v_A_as_ntt, xof_input:(array
      (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
      (sz 3) &
    array u8 (sz 34)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_kyber.Parameters.v_RANK
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (v_A_as_ntt, xof_input)
      (fun (v_A_as_ntt, xof_input) i ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = Hacspec_kyber.Parameters.v_RANK
                  })
              <:
              (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
            (v_A_as_ntt, xof_input)
            (fun (v_A_as_ntt, xof_input) j ->
                let xof_input:array u8 (sz 34) =
                  Rust_primitives.Hax.update_at xof_input (sz 32) (Hacspec_lib.f_as_u8 i <: u8)
                in
                let xof_input:array u8 (sz 34) =
                  Rust_primitives.Hax.update_at xof_input (sz 33) (Hacspec_lib.f_as_u8 j <: u8)
                in
                let (xof_bytes: array u8 (sz 840)):array u8 (sz 840) =
                  Hacspec_kyber.Parameters.Hash_functions.v_XOF (Rust_primitives.unsize xof_input
                      <:
                      slice u8)
                in
                let* hoist6:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                  match
                    Core.Ops.Try_trait.f_branch (Hacspec_kyber.Sampling.sample_ntt xof_bytes
                        <:
                        Core.Result.t_Result
                          (Hacspec_lib.Ring.t_PolynomialRingElement
                              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
                          Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
                  with
                  | Core.Ops.Control_flow.ControlFlow_Break residual ->
                    let* hoist5:Rust_primitives.Hax.t_Never =
                      Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                          <:
                          Core.Result.t_Result (array u8 (sz 1088))
                            Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
                    in
                    Core.Ops.Control_flow.ControlFlow_Continue
                    (Rust_primitives.Hax.never_to_any hoist5)
                  | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                    Core.Ops.Control_flow.ControlFlow_Continue v_val
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (let hoist7:Hacspec_lib.Vector.t_Vector
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
                    Rust_primitives.Hax.update_at (v_A_as_ntt.[ i ]
                        <:
                        Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                          (sz 256)
                          (sz 3))
                      j
                      hoist6
                  in
                  let hoist8:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        (sz 256)
                        (sz 3)) (sz 3) =
                    Rust_primitives.Hax.update_at v_A_as_ntt i hoist7
                  in
                  let v_A_as_ntt:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        (sz 256)
                        (sz 3)) (sz 3) =
                    hoist8
                  in
                  v_A_as_ntt, xof_input))
          <:
          (array
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                  (sz 256)
                  (sz 3)) (sz 3) &
            array u8 (sz 34)))
  in
  let r:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let (prf_input: array u8 (sz 33)):array u8 (sz 33) = Hacspec_lib.f_into_padded_array randomness in
  let domain_separator, prf_input, r:(u8 & array u8 (sz 33) &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_lib.Vector.impl__len r <: usize
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, prf_input, r)
      (fun (domain_separator, prf_input, r) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 (sz 128)):array u8 (sz 128) =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let r:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256)
            (sz 3) =
            Rust_primitives.Hax.update_at r
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd (sz 2)
                  (Rust_primitives.unsize prf_output <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          in
          domain_separator, prf_input, r)
  in
  let error_1_:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let domain_separator, error_1_, prf_input:(u8 &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) &
    array u8 (sz 33)) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_lib.Vector.impl__len error_1_ <: usize
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (domain_separator, error_1_, prf_input)
      (fun (domain_separator, error_1_, prf_input) i ->
          let prf_input:array u8 (sz 33) =
            Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          let (prf_output: array u8 (sz 128)):array u8 (sz 128) =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let error_1_:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256)
            (sz 3) =
            Rust_primitives.Hax.update_at error_1_
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd (sz 2)
                  (Rust_primitives.unsize prf_output <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          in
          domain_separator, error_1_, prf_input)
  in
  let prf_input:array u8 (sz 33) =
    Rust_primitives.Hax.update_at prf_input (sz 32) domain_separator
  in
  let (prf_output: array u8 (sz 128)):array u8 (sz 128) =
    Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
  in
  let error_2_:Hacspec_lib.Ring.t_PolynomialRingElement
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
    Hacspec_kyber.Sampling.sample_poly_cbd (sz 2) (Rust_primitives.unsize prf_output <: slice u8)
  in
  let r_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_kyber.Ntt.vector_ntt r
  in
  let v_A_as_ntt_transpose:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
    (sz 3) =
    Hacspec_kyber.Matrix.transpose v_A_as_ntt
  in
  let u =
    (Hacspec_kyber.Ntt.vector_inverse_ntt (Hacspec_kyber.Matrix.multiply_matrix_by_column v_A_as_ntt_transpose
            r_as_ntt
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
        )
      <:
      Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)) +!
    error_1_
  in
  let message_as_ring_element:Hacspec_lib.Ring.t_PolynomialRingElement
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
    Hacspec_kyber.Compress.decompress (Hacspec_kyber.Serialize.byte_decode (sz 1)
          (Rust_primitives.unsize message <: slice u8)
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          (sz 256))
      (sz 1)
  in
  let v =
    ((Hacspec_kyber.Ntt.ntt_inverse (Hacspec_kyber.Matrix.multiply_column_by_row tt_as_ntt r_as_ntt
            <:
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256))
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          (sz 256)) +!
      error_2_
      <:
      (Hacspec_lib.Ring.impl_6 (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)).f_Output) +!
    message_as_ring_element
  in
  let c1:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = encode_and_compress_u u in
  let c2:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Hacspec_kyber.Serialize.byte_encode Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
      (Hacspec_kyber.Compress.compress v Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          (sz 256))
  in
  let (ciphertext: array u8 (sz 1088)):array u8 (sz 1088) = Hacspec_lib.f_into_padded_array c1 in
  let ciphertext:array u8 (sz 1088) =
    Rust_primitives.Hax.update_at ciphertext
      ({ Core.Ops.Range.f_start = Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE })
      (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut ciphertext
              ({ Core.Ops.Range.f_start = Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE })
            <:
            slice u8)
          (Alloc.Vec.impl_1__as_slice c2 <: slice u8)
        <:
        slice u8)
  in
  Core.Result.Result_Ok ciphertext

let decrypt (secret_key: array u8 (sz 1152)) (ciphertext: array u8 (sz 1088)) : array u8 (sz 32) =
  let u:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let u:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks (ciphertext.[ {
                        Core.Ops.Range.f_end = Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  ((Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT *!
                      Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                      <:
                      usize) /!
                    sz 8
                    <:
                    usize)
                <:
                Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8)))
          .f_IntoIter)
      u
      (fun u (i, u_bytes) ->
          Rust_primitives.Hax.update_at u
            i
            (Hacspec_kyber.Compress.decompress (Hacspec_kyber.Serialize.byte_decode Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                    u_bytes
                  <:
                  Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
                Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
      )
  in
  let v:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    Hacspec_kyber.Compress.decompress (Hacspec_kyber.Serialize.byte_decode Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
          (ciphertext.[ {
                Core.Ops.Range.f_start = Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE
              } ]
            <:
            slice u8)
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          (sz 256))
      Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
  in
  let secret_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let secret_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize secret_key <: slice u8)
                  Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8)))
          .f_IntoIter)
      secret_as_ntt
      (fun secret_as_ntt (i, secret_bytes) ->
          Rust_primitives.Hax.update_at secret_as_ntt
            i
            (Hacspec_kyber.Serialize.byte_decode (sz 12) secret_bytes
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
      )
  in
  let u_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_kyber.Ntt.vector_ntt u
  in
  let message =
    v -!
    (Hacspec_kyber.Ntt.ntt_inverse (Hacspec_kyber.Matrix.multiply_column_by_row secret_as_ntt
            u_as_ntt
          <:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
      <:
      Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
        (sz 256))
  in
  Hacspec_lib.f_as_array (Hacspec_kyber.Serialize.byte_encode (sz 1)
        (Hacspec_kyber.Compress.compress message (sz 1)
          <:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)