module Hacspec_kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_CiphertextCpa = array u8 1088sz

type t_KeyPair = {
  f_sk:array u8 1152sz;
  f_pk:array u8 1184sz
}

let new_under_impl (sk: array u8 1152sz) (pk: array u8 1184sz) : t_KeyPair =
  { Hacspec_kyber.Ind_cpa.KeyPair.f_sk = sk; Hacspec_kyber.Ind_cpa.KeyPair.f_pk = pk }

let serialize_secret_key_under_impl (self: t_KeyPair) (implicit_rejection_value: array u8 32sz)
    : array u8 2400sz =
  Core.Convert.Into.into (Hacspec_lib.UpdatingArray.push (Hacspec_lib.UpdatingArray.push (Hacspec_lib.UpdatingArray.push
                (Hacspec_lib.UpdatingArray.push (Hacspec_lib.new_under_impl_6 (Rust_primitives.Hax.repeat
                            0uy
                            2400sz
                          <:
                          array u8 2400sz)
                      <:
                      Hacspec_lib.t_UpdatableArray 2400sz)
                    (Rust_primitives.unsize self.Hacspec_kyber.Ind_cpa.KeyPair.f_sk <: slice u8)
                  <:
                  Hacspec_lib.t_UpdatableArray 2400sz)
                (Rust_primitives.unsize self.Hacspec_kyber.Ind_cpa.KeyPair.f_pk <: slice u8)
              <:
              Hacspec_lib.t_UpdatableArray 2400sz)
            (Rust_primitives.unsize (Hacspec_kyber.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                        self.Hacspec_kyber.Ind_cpa.KeyPair.f_pk
                      <:
                      slice u8)
                  <:
                  array u8 32sz)
              <:
              slice u8)
          <:
          Hacspec_lib.t_UpdatableArray 2400sz)
        (Rust_primitives.unsize implicit_rejection_value <: slice u8)
      <:
      Hacspec_lib.t_UpdatableArray 2400sz)

let pk_under_impl (self: t_KeyPair) : array u8 1184sz = self.Hacspec_kyber.Ind_cpa.KeyPair.f_pk

let generate_keypair (key_generation_seed: array u8 32sz)
    : Core.Result.t_Result t_KeyPair Hacspec_kyber.t_BadRejectionSamplingRandomnessError =
  let hashed:array u8 64sz =
    Hacspec_kyber.Parameters.Hash_functions.v_G (Rust_primitives.unsize key_generation_seed
        <:
        slice u8)
  in
  let seed_for_A, seed_for_secret_and_error:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let (domain_separator: u8):u8 = 0uy in
  let v_A_as_ntt:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz =
    Rust_primitives.Hax.repeat Hacspec_lib.Vector.v_ZERO_under_impl 3sz
  in
  let (xof_input: array u8 34sz):array u8 34sz =
    Hacspec_lib.ArrayConversion.into_padded_array seed_for_A
  in
  let v_A_as_ntt, xof_input:(array
      (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz &
    array u8 34sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_kyber.Parameters.v_RANK
            })
        <:
        _)
      (v_A_as_ntt, xof_input)
      (fun (v_A_as_ntt, xof_input) i ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = Hacspec_kyber.Parameters.v_RANK
                  })
              <:
              _)
            (v_A_as_ntt, xof_input)
            (fun (v_A_as_ntt, xof_input) j ->
                let xof_input:array u8 34sz =
                  Rust_primitives.Hax.update_at xof_input
                    32sz
                    (Hacspec_lib.PanickingIntegerCasts.as_u8 i <: u8)
                in
                let xof_input:array u8 34sz =
                  Rust_primitives.Hax.update_at xof_input
                    33sz
                    (Hacspec_lib.PanickingIntegerCasts.as_u8 j <: u8)
                in
                let (xof_bytes: array u8 840sz):array u8 840sz =
                  Hacspec_kyber.Parameters.Hash_functions.v_XOF (Rust_primitives.unsize xof_input
                      <:
                      slice u8)
                in
                let* hoist2:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                  match
                    Core.Ops.Try_trait.Try.branch (Hacspec_kyber.Sampling.sample_ntt xof_bytes
                        <:
                        Core.Result.t_Result
                          (Hacspec_lib.Ring.t_PolynomialRingElement
                              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
                          Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
                  with
                  | Core.Ops.Control_flow.ControlFlow_Break residual ->
                    let* hoist1:Rust_primitives.Hax.t_Never =
                      Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                            residual
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
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
                    Rust_primitives.Hax.update_at (v_A_as_ntt.[ i ]
                        <:
                        Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                          256sz
                          3sz)
                      j
                      hoist2
                  in
                  let hoist4:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        256sz
                        3sz) 3sz =
                    Rust_primitives.Hax.update_at v_A_as_ntt i hoist3
                  in
                  let v_A_as_ntt:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        256sz
                        3sz) 3sz =
                    hoist4
                  in
                  v_A_as_ntt, xof_input))
          <:
          (array
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
              3sz &
            array u8 34sz))
  in
  let secret:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let (prf_input: array u8 33sz):array u8 33sz =
    Hacspec_lib.ArrayConversion.into_padded_array seed_for_secret_and_error
  in
  let domain_separator, prf_input, secret:(Prims.unit & array u8 33sz &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Vector.len_under_impl secret <: usize
            })
        <:
        _)
      (domain_separator, prf_input, secret)
      (fun (domain_separator, prf_input, secret) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let secret:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz
            3sz =
            Rust_primitives.Hax.update_at secret
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd 2sz
                  (prf_output.[ Core.Ops.Range.RangeFull ] <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          in
          domain_separator, prf_input, secret)
  in
  let error:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let domain_separator, error, prf_input:(Prims.unit &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz &
    array u8 33sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Vector.len_under_impl error <: usize
            })
        <:
        _)
      (domain_separator, error, prf_input)
      (fun (domain_separator, error, prf_input) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let error:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz
            3sz =
            Rust_primitives.Hax.update_at error
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd 2sz
                  (prf_output.[ Core.Ops.Range.RangeFull ] <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          in
          domain_separator, error, prf_input)
  in
  let secret_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz
    3sz =
    Hacspec_kyber.Ntt.vector_ntt secret
  in
  let error_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz
    3sz =
    Hacspec_kyber.Ntt.vector_ntt error
  in
  let t__as_ntt =
    (Hacspec_kyber.Matrix.multiply_matrix_by_column v_A_as_ntt secret_as_ntt
      <:
      Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) +.
    error_as_ntt
  in
  let public_key_serialized:array u8 1184sz =
    Hacspec_lib.array_under_impl_6 (Hacspec_lib.UpdatingArray.push (Hacspec_lib.UpdatingArray.push (Hacspec_lib.new_under_impl_6
                  (Rust_primitives.Hax.repeat 0uy 1184sz <: array u8 1184sz)
                <:
                Hacspec_lib.t_UpdatableArray 1184sz)
              (Rust_primitives.unsize (Hacspec_kyber.Serialize.vector_encode_12_ t__as_ntt
                    <:
                    array u8 1152sz)
                <:
                slice u8)
            <:
            Hacspec_lib.t_UpdatableArray 1184sz)
          seed_for_A
        <:
        Hacspec_lib.t_UpdatableArray 1184sz)
  in
  let secret_key_serialized:array u8 1152sz =
    Hacspec_kyber.Serialize.vector_encode_12_ secret_as_ntt
  in
  Core.Result.Result_Ok
  (new_under_impl (Hacspec_lib.ArrayConversion.into_array (Rust_primitives.unsize secret_key_serialized

            <:
            slice u8)
        <:
        array u8 1152sz)
      (Hacspec_lib.ArrayConversion.into_array (Rust_primitives.unsize public_key_serialized
            <:
            slice u8)
        <:
        array u8 1184sz))

let encode_and_compress_u
      (input: Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Hacspec_lib.Vector.into_iter_under_impl
              input
            <:
            Core.Array.Iter.t_IntoIter
              (Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) 3sz)
        <:
        _)
      out
      (fun out re ->
          Alloc.Vec.extend_from_slice_under_impl_2 out
            (Core.Ops.Deref.Deref.deref (Hacspec_kyber.Serialize.byte_encode Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                    (Hacspec_kyber.Compress.compress re
                        Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                      <:
                      Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
                  <:
                  Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              <:
              slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  in
  out

let encrypt (public_key: array u8 1184sz) (message randomness: array u8 32sz)
    : Core.Result.t_Result (array u8 1088sz) Hacspec_kyber.t_BadRejectionSamplingRandomnessError =
  let (domain_separator: u8):u8 = 0uy in
  let t__as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz
  =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let t__as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz
  =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_under_impl (public_key.[ {
                        Core.Ops.Range.RangeTo.f_end
                        =
                        Hacspec_kyber.Parameters.v_T_AS_NTT_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        _)
      t__as_ntt
      (fun t__as_ntt (i, t__as_ntt_bytes) ->
          Rust_primitives.Hax.update_at t__as_ntt
            i
            (Hacspec_kyber.Serialize.byte_decode 12sz t__as_ntt_bytes
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
  in
  let seed_for_A:slice u8 =
    public_key.[ {
        Core.Ops.Range.RangeFrom.f_start = Hacspec_kyber.Parameters.v_T_AS_NTT_ENCODED_SIZE
      } ]
  in
  let v_A_as_ntt:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz =
    Rust_primitives.Hax.repeat Hacspec_lib.Vector.v_ZERO_under_impl 3sz
  in
  let (xof_input: array u8 34sz):array u8 34sz =
    Hacspec_lib.ArrayConversion.into_padded_array seed_for_A
  in
  let v_A_as_ntt, xof_input:(array
      (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz &
    array u8 34sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_kyber.Parameters.v_RANK
            })
        <:
        _)
      (v_A_as_ntt, xof_input)
      (fun (v_A_as_ntt, xof_input) i ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = Hacspec_kyber.Parameters.v_RANK
                  })
              <:
              _)
            (v_A_as_ntt, xof_input)
            (fun (v_A_as_ntt, xof_input) j ->
                let xof_input:array u8 34sz =
                  Rust_primitives.Hax.update_at xof_input
                    32sz
                    (Hacspec_lib.PanickingIntegerCasts.as_u8 i <: u8)
                in
                let xof_input:array u8 34sz =
                  Rust_primitives.Hax.update_at xof_input
                    33sz
                    (Hacspec_lib.PanickingIntegerCasts.as_u8 j <: u8)
                in
                let (xof_bytes: array u8 840sz):array u8 840sz =
                  Hacspec_kyber.Parameters.Hash_functions.v_XOF (Rust_primitives.unsize xof_input
                      <:
                      slice u8)
                in
                let* hoist6:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                  match
                    Core.Ops.Try_trait.Try.branch (Hacspec_kyber.Sampling.sample_ntt xof_bytes
                        <:
                        Core.Result.t_Result
                          (Hacspec_lib.Ring.t_PolynomialRingElement
                              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
                          Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
                  with
                  | Core.Ops.Control_flow.ControlFlow_Break residual ->
                    let* hoist5:Rust_primitives.Hax.t_Never =
                      Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.FromResidual.from_residual
                            residual
                          <:
                          Core.Result.t_Result (array u8 1088sz)
                            Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
                    in
                    Core.Ops.Control_flow.ControlFlow_Continue
                    (Rust_primitives.Hax.never_to_any hoist5)
                  | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                    Core.Ops.Control_flow.ControlFlow_Continue v_val
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (let hoist7:Hacspec_lib.Vector.t_Vector
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
                    Rust_primitives.Hax.update_at (v_A_as_ntt.[ i ]
                        <:
                        Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                          256sz
                          3sz)
                      j
                      hoist6
                  in
                  let hoist8:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        256sz
                        3sz) 3sz =
                    Rust_primitives.Hax.update_at v_A_as_ntt i hoist7
                  in
                  let v_A_as_ntt:array
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        256sz
                        3sz) 3sz =
                    hoist8
                  in
                  v_A_as_ntt, xof_input))
          <:
          (array
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
              3sz &
            array u8 34sz))
  in
  let r:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let (prf_input: array u8 33sz):array u8 33sz =
    Hacspec_lib.ArrayPadding.into_padded_array randomness
  in
  let domain_separator, prf_input, r:(Prims.unit & array u8 33sz &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Vector.len_under_impl r <: usize
            })
        <:
        _)
      (domain_separator, prf_input, r)
      (fun (domain_separator, prf_input, r) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let r:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz
          =
            Rust_primitives.Hax.update_at r
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd 2sz
                  (Rust_primitives.unsize prf_output <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          in
          domain_separator, prf_input, r)
  in
  let error_1_:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz
  =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let domain_separator, error_1_, prf_input:(Prims.unit &
    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz &
    array u8 33sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Vector.len_under_impl error_1_ <: usize
            })
        <:
        _)
      (domain_separator, error_1_, prf_input)
      (fun (domain_separator, error_1_, prf_input) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let error_1_:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz
            3sz =
            Rust_primitives.Hax.update_at error_1_
              i
              (Hacspec_kyber.Sampling.sample_poly_cbd 2sz
                  (Rust_primitives.unsize prf_output <: slice u8)
                <:
                Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          in
          domain_separator, error_1_, prf_input)
  in
  let prf_input:array u8 33sz = Rust_primitives.Hax.update_at prf_input 32sz domain_separator in
  let (prf_output: array u8 128sz):array u8 128sz =
    Hacspec_kyber.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input <: slice u8)
  in
  let error_2_:Hacspec_lib.Ring.t_PolynomialRingElement
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
    Hacspec_kyber.Sampling.sample_poly_cbd 2sz (Rust_primitives.unsize prf_output <: slice u8)
  in
  let r_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz
  =
    Hacspec_kyber.Ntt.vector_ntt r
  in
  let v_A_as_ntt_transpose:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz =
    Hacspec_kyber.Matrix.transpose v_A_as_ntt
  in
  let u =
    (Hacspec_kyber.Ntt.vector_inverse_ntt (Hacspec_kyber.Matrix.multiply_matrix_by_column v_A_as_ntt_transpose
            r_as_ntt
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
      <:
      Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) +.
    error_1_
  in
  let message_as_ring_element:Hacspec_lib.Ring.t_PolynomialRingElement
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
    Hacspec_kyber.Compress.decompress (Hacspec_kyber.Serialize.byte_decode 1sz
          (Rust_primitives.unsize message <: slice u8)
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          256sz)
      1sz
  in
  let v =
    ((Hacspec_kyber.Ntt.ntt_inverse (Hacspec_kyber.Matrix.multiply_column_by_row t__as_ntt r_as_ntt
            <:
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              256sz)
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          256sz) +.
      error_2_
      <:
      _) +.
    message_as_ring_element
  in
  let c1:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = encode_and_compress_u u in
  let c2:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Hacspec_kyber.Serialize.byte_encode Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
      (Hacspec_kyber.Compress.compress v Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          256sz)
  in
  let (ciphertext: array u8 1088sz):array u8 1088sz =
    Hacspec_lib.ArrayConversion.into_padded_array c1
  in
  let ciphertext:array u8 1088sz =
    Rust_primitives.Hax.update_at ciphertext
      ({ Core.Ops.Range.RangeFrom.f_start = Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut ciphertext
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE
                })
            <:
            slice u8)
          (Alloc.Vec.as_slice_under_impl_1 c2 <: slice u8)
        <:
        slice u8)
  in
  Core.Result.Result_Ok ciphertext

let decrypt (secret_key: array u8 1152sz) (ciphertext: array u8 1088sz) : array u8 32sz =
  let u:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let u:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_under_impl (ciphertext.[ {
                        Core.Ops.Range.RangeTo.f_end
                        =
                        Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  ((Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT *.
                      Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                      <:
                      usize) /.
                    8sz
                    <:
                    usize)
                <:
                Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        _)
      u
      (fun u (i, u_bytes) ->
          Rust_primitives.Hax.update_at u
            i
            (Hacspec_kyber.Compress.decompress (Hacspec_kyber.Serialize.byte_decode Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                    u_bytes
                  <:
                  Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
                Hacspec_kyber.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
  in
  let v:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    Hacspec_kyber.Compress.decompress (Hacspec_kyber.Serialize.byte_decode Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
          (ciphertext.[ {
                Core.Ops.Range.RangeFrom.f_start = Hacspec_kyber.Parameters.v_VECTOR_U_ENCODED_SIZE
              } ]
            <:
            slice u8)
        <:
        Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          256sz)
      Hacspec_kyber.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
  in
  let secret_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz
    3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let secret_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz
    3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize secret_key <: slice u8)
                  Hacspec_kyber.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      secret_as_ntt
      (fun secret_as_ntt (i, secret_bytes) ->
          Rust_primitives.Hax.update_at secret_as_ntt
            i
            (Hacspec_kyber.Serialize.byte_decode 12sz secret_bytes
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
  in
  let u_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz
  =
    Hacspec_kyber.Ntt.vector_ntt u
  in
  let message =
    v -.
    (Hacspec_kyber.Ntt.ntt_inverse (Hacspec_kyber.Matrix.multiply_column_by_row secret_as_ntt
            u_as_ntt
          <:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
      <:
      Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
  in
  Hacspec_lib.ArrayConversion.as_array (Hacspec_kyber.Serialize.byte_encode 1sz
        (Hacspec_kyber.Compress.compress message 1sz
          <:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)