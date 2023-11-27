module Libcrux.Kem.Kyber.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let serialize_secret_key
      (v_SERIALIZED_KEY_LEN: usize)
      (private_key public_key implicit_rejection_value: t_Slice u8)
    : FStar.HyperStack.ST.St (t_Array u8 v_SERIALIZED_KEY_LEN) =
  Libcrux.Kem.Kyber.Conversions.impl__array v_SERIALIZED_KEY_LEN
    (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.f_push
                (Libcrux.Kem.Kyber.Conversions.f_push (Libcrux.Kem.Kyber.Conversions.impl__new v_SERIALIZED_KEY_LEN
                        (Rust_primitives.Hax.repeat 0uy v_SERIALIZED_KEY_LEN
                          <:
                          t_Array u8 v_SERIALIZED_KEY_LEN)
                      <:
                      Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
                    private_key
                  <:
                  Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
                public_key
              <:
              Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
            (Rust_primitives.unsize (Libcrux.Kem.Kyber.Hash_functions.v_H public_key
                  <:
                  t_Array u8 (sz 32))
              <:
              t_Slice u8)
          <:
          Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)
        implicit_rejection_value
      <:
      Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_SERIALIZED_KEY_LEN)

let cbd (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize) (prf_input: t_Array u8 (sz 33))
    : FStar.HyperStack.ST.St
    (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K & u8) =
  let domain_separator:u8 = 0uy in
  let re_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let domain_separator:u8 =
    Rust_primitives.Hax.failure ""
      "{\n        (for i in (0)..(K) {\n            |domain_separator| {\n                let _: tuple0 = {\n                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                        prf_input,\n                        32,\n                        domain_separator,\n                    )\n                };\n                {\n                    let domain_separator: int = { core::ops::arith::Add::add(domain_separator, 1) };\n                    {\n                        let pat_ascription!(prf_output as [int; ETA_RANDOMNESS_SIZE]): [int;\n                            ETA_RANDOMNESS_SIZE] = {\n                            libcrux::kem::kyber::hash_functions::v_PRF::<generic_value!(todo)>(\n                                rust_primitives::unsize(prf_input),\n                            )\n                        };\n                        {\n                            let r: libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement = {\n                                libcrux::kem::kyber::sampling::sample_from_binomial_distribution::<\n                                    generic_value!(todo),\n                                >(rust_primitives::unsize(\n                                    prf_output,\n                                ))\n                            };\n                            {\n                                let _: tuple0 = {\n                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(re_as_ntt,i,libcrux::kem::kyber::ntt::ntt_binomially_sampled_ring_element(r))\n                                };\n                                domain_separator\n                            }\n                        }\n                    }\n                }\n            }\n        })(domain_separator)\n    }"

  in
  re_as_ntt, domain_separator
  <:
  (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K & u8)

let sample_matrix_A (v_K: usize) (seed: t_Array u8 (sz 34)) (transpose: bool)
    : FStar.HyperStack.ST.St
    (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let
  (v_A_transpose:
    t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K):t_Array
    (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "explicit panic"
        <:
        Rust_primitives.Hax.t_Never)
  in
  let sampling_A_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
    Core.Option.Option_None <: Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error
  in
  let sampling_A_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
    Rust_primitives.Hax.failure ""
      "{\n        (for i in (0)..(K) {\n            |sampling_A_error| {\n                let seeds: [[int; 34]; K] = { rust_primitives::hax::repeat(seed, K) };\n                {\n                    let _: tuple0 = {\n                        {\n                            for j in (0)..(K) {\n                                {\n                                    let _: tuple0 = {\n                                        rust_primitives::hax::monomorphized_update_at::update_array_at_usize(core::ops::index::Index::index(seeds,j),32,cast(i))\n                                    };\n                                    {\n                                        let _: tuple0 = {\n                                            rust_primitives::hax::monomorphized_update_at::update_array_at_usize(core::ops::index::Index::index(seeds,j),33,cast(j))\n                                        };\n                                        Tuple0\n                                    }\n                                }\n                            }\n                        }\n                    };\n                    {\n                        let xof_bytes: [[int; 840]; K] = {\n                            libcrux::kem::kyber::hash_functions::v_XOFx4::<\n                                generic_value!(todo),\n                                generic_value!(todo),\n                            >(seeds)\n                        };\n                        {\n                            (for j in (0)..(K) {\n                                |sampling_A_error| {\n                                    let Tuple2(sampled, error): tuple2<libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement, core::option::t_Option<libcrux::kem::kyber::types::t_Error>> = {libcrux::kem::kyber::sampling::sample_from_uniform_distribution::<generic_value!(todo)>(core::ops::index::Index::index(xof_bytes,j))};\n                                    {\n                                        let sampling_A_error: core::option::t_Option<\n                                            libcrux::kem::kyber::types::t_Error,\n                                        > = {\n                                            (if core::option::impl__is_some::<\n                                                libcrux::kem::kyber::types::t_Error,\n                                            >(error)\n                                            {\n                                                {\n                                                    let sampling_A_error: core::option::t_Option<\n                                                        libcrux::kem::kyber::types::t_Error,\n                                                    > = { error };\n                                                    sampling_A_error\n                                                }\n                                            } else {\n                                                sampling_A_error\n                                            })\n                                        };\n                                        (if transpose {\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(core::ops::index::Index::index(A_transpose,j),i,sampled)\n                                                };\n                                                sampling_A_error\n                                            }\n                                        } else {\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(core::ops::index::Index::index(A_transpose,i),j,sampled)\n                                                };\n                                                sampling_A_error\n                                            }\n                                        })\n                                    }\n                                }\n                            })(sampling_A_error)\n                        }\n                    }\n                }\n            }\n        })(sampling_A_error)\n    }"

  in
  v_A_transpose, sampling_A_error
  <:
  (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)

let compress_then_encode_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (input: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array u8 v_OUT_LEN) =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "{\n        for Tuple2(i, re) in (core::iter::traits::collect::f_into_iter::<\n            core::iter::adapters::enumerate::t_Enumerate<\n                core::array::iter::t_IntoIter<\n                    libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                    generic_value!(todo),\n                >,\n            >,\n        >(core::iter::traits::iterator::f_enumerate::<\n            core::array::iter::t_IntoIter<\n                libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                generic_value!(todo),\n            >,\n        >(core::iter::traits::collect::f_into_iter::<\n            [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n        >(input))))\n        {\n            core::slice::impl__copy_from_slice::<int>(\n                core::ops::index::f_index_mut::<[int; OUT_LEN], core::ops::range::t_Range<int>>(\n                    out,\n                    core::ops::range::Range {\n                        f_start: core::ops::arith::Mul::mul(\n                            i,\n                            core::ops::arith::Div::div(OUT_LEN, K),\n                        ),\n                        f_end: core::ops::arith::Mul::mul(\n                            core::ops::arith::Add::add(i, 1),\n                            core::ops::arith::Div::div(OUT_LEN, K),\n                        ),\n                    },\n                ),\n                rust_primitives::unsize(\n                    libcrux::kem::kyber::serialize::compress_then_serialize_ring_element_u::<\n                        generic_value!(todo),\n                        generic_value!(todo),\n                    >(re),\n                ),\n            )\n        }\n    }"

  in
  out

let serialize_key
      (v_K v_OUT_LEN: usize)
      (key: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array u8 v_OUT_LEN) =
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat 0uy v_OUT_LEN in
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "{\n        for Tuple2(i, re) in (core::iter::traits::collect::f_into_iter::<\n            core::iter::adapters::enumerate::t_Enumerate<\n                core::array::iter::t_IntoIter<\n                    libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                    generic_value!(todo),\n                >,\n            >,\n        >(core::iter::traits::iterator::f_enumerate::<\n            core::array::iter::t_IntoIter<\n                libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                generic_value!(todo),\n            >,\n        >(core::iter::traits::collect::f_into_iter::<\n            [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n        >(key))))\n        {\n            core::slice::impl__copy_from_slice::<int>(\n                core::ops::index::f_index_mut::<[int; OUT_LEN], core::ops::range::t_Range<int>>(\n                    out,\n                    core::ops::range::Range {\n                        f_start: core::ops::arith::Mul::mul(\n                            i,\n                            libcrux::kem::kyber::constants::v_BYTES_PER_RING_ELEMENT,\n                        ),\n                        f_end: core::ops::arith::Mul::mul(\n                            core::ops::arith::Add::add(i, 1),\n                            libcrux::kem::kyber::constants::v_BYTES_PER_RING_ELEMENT,\n                        ),\n                    },\n                ),\n                rust_primitives::unsize(\n                    libcrux::kem::kyber::serialize::serialize_uncompressed_ring_element(re),\n                ),\n            )\n        }\n    }"

  in
  out

let decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (secret_key: t_Slice u8)
      (ciphertext: Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE)
    : FStar.HyperStack.ST.St (t_Array u8 (sz 32)) =
  let u_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "{\n        for Tuple2(i, u_bytes) in (core::iter::traits::collect::f_into_iter::<\n            core::iter::adapters::enumerate::t_Enumerate<core::slice::iter::t_ChunksExact<int>>,\n        >(core::iter::traits::iterator::f_enumerate::<\n            core::slice::iter::t_ChunksExact<int>,\n        >(core::slice::impl__chunks_exact::<int>(\n            core::ops::index::f_index::<[int; CIPHERTEXT_SIZE], core::ops::range::t_RangeTo<int>>(\n                proj_libcrux::kem::kyber::types::f_value(ciphertext),\n                core::ops::range::RangeTo {\n                    f_end: VECTOR_U_ENCODED_SIZE,\n                },\n            ),\n            core::ops::arith::Div::div(\n                core::ops::arith::Mul::mul(\n                    libcrux::kem::kyber::constants::v_COEFFICIENTS_IN_RING_ELEMENT,\n                    U_COMPRESSION_FACTOR,\n                ),\n                8,\n            ),\n        )))) {\n            {\n                let u: libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement = {\n                    libcrux::kem::kyber::serialize::deserialize_then_decompress_ring_element_u::<\n                        generic_value!(todo),\n                    >(u_bytes)\n                };\n                {\n                    let _: tuple0 = {\n                        rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                            u_as_ntt,\n                            i,\n                            libcrux::kem::kyber::ntt::ntt_vector_u::<generic_value!(todo)>(u),\n                        )\n                    };\n                    Tuple0\n                }\n            }\n        }\n    }"

  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_ring_element_v v_V_COMPRESSION_FACTOR
      (ciphertext.Libcrux.Kem.Kyber.Types.f_value.[ {
            Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE
          }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "{\n        for Tuple2(i, secret_bytes) in\n            (core::iter::traits::collect::f_into_iter::<\n                core::iter::adapters::enumerate::t_Enumerate<core::slice::iter::t_ChunksExact<int>>,\n            >(core::iter::traits::iterator::f_enumerate::<\n                core::slice::iter::t_ChunksExact<int>,\n            >(core::slice::impl__chunks_exact::<int>(\n                secret_key,\n                libcrux::kem::kyber::constants::v_BYTES_PER_RING_ELEMENT,\n            ))))\n        {\n            rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                secret_as_ntt,\n                i,\n                libcrux::kem::kyber::serialize::deserialize_to_uncompressed_ring_element(\n                    secret_bytes,\n                ),\n            )\n        }\n    }"

  in
  let message:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Ntt.compute_message v_K v secret_as_ntt u_as_ntt
  in
  Libcrux.Kem.Kyber.Serialize.compress_then_serialize_message message

let encrypt
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
    : FStar.HyperStack.ST.St
    (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure ""
      "{\n        for Tuple2(i, t_as_ntt_bytes) in\n            (core::iter::traits::collect::f_into_iter::<\n                core::iter::adapters::enumerate::t_Enumerate<core::slice::iter::t_ChunksExact<int>>,\n            >(core::iter::traits::iterator::f_enumerate::<\n                core::slice::iter::t_ChunksExact<int>,\n            >(core::slice::impl__chunks_exact::<int>(\n                core::ops::index::f_index::<[int], core::ops::range::t_RangeTo<int>>(\n                    public_key,\n                    core::ops::range::RangeTo {\n                        f_end: T_AS_NTT_ENCODED_SIZE,\n                    },\n                ),\n                libcrux::kem::kyber::constants::v_BYTES_PER_RING_ELEMENT,\n            ))))\n        {\n            rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                t_as_ntt,\n                i,\n                libcrux::kem::kyber::serialize::deserialize_to_uncompressed_ring_element(\n                    t_as_ntt_bytes,\n                ),\n            )\n        }\n    }"

  in
  let seed:t_Slice u8 =
    public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let v_A_transpose, sampling_A_error:(t_Array
      (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    sample_matrix_A v_K
      (Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 34) seed <: t_Array u8 (sz 34))
      false
  in
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) =
    Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 33) randomness
  in
  let r_as_ntt, domain_separator:(t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
      v_K &
    u8) =
    cbd v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE prf_input
  in
  let error_1_:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let domain_separator:u8 =
    Rust_primitives.Hax.failure ""
      "{\n        (for i in (0)..(K) {\n            |domain_separator| {\n                let _: tuple0 = {\n                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                        prf_input,\n                        32,\n                        domain_separator,\n                    )\n                };\n                {\n                    let domain_separator: int = { core::ops::arith::Add::add(domain_separator, 1) };\n                    {\n                        let pat_ascription!(prf_output as [int; ETA2_RANDOMNESS_SIZE]): [int;\n                            ETA2_RANDOMNESS_SIZE] = {\n                            libcrux::kem::kyber::hash_functions::v_PRF::<generic_value!(todo)>(\n                                rust_primitives::unsize(prf_input),\n                            )\n                        };\n                        {\n                            let _: tuple0 = {\n                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(error_1,i,libcrux::kem::kyber::sampling::sample_from_binomial_distribution::<generic_value!(todo)>(rust_primitives::unsize(prf_output)))\n                            };\n                            domain_separator\n                        }\n                    }\n                }\n            }\n        })(domain_separator)\n    }"

  in
  let _:Prims.unit =
    Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize prf_input
      (sz 32)
      domain_separator
  in
  let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux.Kem.Kyber.Hash_functions.v_PRF v_ETA2_RANDOMNESS_SIZE
      (Rust_primitives.unsize prf_input <: t_Slice u8)
  in
  let error_2_:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Sampling.sample_from_binomial_distribution v_ETA2
      (Rust_primitives.unsize prf_output <: t_Slice u8)
  in
  let u:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.compute_vector_u v_K v_A_transpose r_as_ntt error_1_
  in
  let message_as_ring_element:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Serialize.deserialize_then_decompress_message message
  in
  let v:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Ntt.compute_ring_element_v v_K
      tt_as_ntt
      r_as_ntt
      error_2_
      message_as_ring_element
  in
  let c1:t_Array u8 v_C1_LEN =
    compress_then_encode_u v_K v_C1_LEN v_U_COMPRESSION_FACTOR v_BLOCK_LEN u
  in
  let c2:t_Array u8 v_C2_LEN =
    Libcrux.Kem.Kyber.Serialize.compress_then_serialize_ring_element_v v_V_COMPRESSION_FACTOR
      v_C2_LEN
      v
  in
  let (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE):t_Array u8 v_CIPHERTEXT_SIZE =
    Libcrux.Kem.Kyber.Conversions.into_padded_array v_CIPHERTEXT_SIZE
      (Rust_primitives.unsize c1 <: t_Slice u8)
  in
  let _:Prims.unit =
    Core.Slice.impl__copy_from_slice (Core.Ops.Index.f_index_mut ciphertext
          ({ Core.Ops.Range.f_start = v_C1_LEN } <: Core.Ops.Range.t_RangeFrom usize)
        <:
        t_Slice u8)
      (Core.Array.impl_23__as_slice v_C2_LEN c2 <: t_Slice u8)
  in
  Core.Convert.f_into ciphertext, sampling_A_error
  <:
  (Libcrux.Kem.Kyber.Types.t_KyberCiphertext v_CIPHERTEXT_SIZE &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)

let generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (key_generation_seed: t_Slice u8)
    : FStar.HyperStack.ST.St
    ((Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
        Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let (prf_input: t_Array u8 (sz 33)):t_Array u8 (sz 33) = Rust_primitives.Hax.repeat 0uy (sz 33) in
  let secret_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let error_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let (domain_separator: u8):u8 = 0uy in
  let hashed:t_Array u8 (sz 64) = Libcrux.Kem.Kyber.Hash_functions.v_G key_generation_seed in
  let seed_for_A, seed_for_secret_and_error:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at (Rust_primitives.unsize hashed <: t_Slice u8) (sz 32)
  in
  let v_A_transpose, sampling_A_error:(t_Array
      (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
    sample_matrix_A v_K
      (Libcrux.Kem.Kyber.Conversions.into_padded_array (sz 34) seed_for_A <: t_Array u8 (sz 34))
      true
  in
  let _:Prims.unit =
    Core.Slice.impl__copy_from_slice (Core.Ops.Index.f_index_mut prf_input
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Core.Slice.impl__len seed_for_secret_and_error <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        t_Slice u8)
      seed_for_secret_and_error
  in
  let domain_separator:u8 =
    Rust_primitives.Hax.failure ""
      "{\n        (for i in (0)..(K) {\n            |domain_separator| {\n                let _: tuple0 = {\n                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                        prf_input,\n                        32,\n                        domain_separator,\n                    )\n                };\n                {\n                    let domain_separator: int = { core::ops::arith::Add::add(domain_separator, 1) };\n                    {\n                        let pat_ascription!(prf_output as [int; ETA1_RANDOMNESS_SIZE]): [int;\n                            ETA1_RANDOMNESS_SIZE] = {\n                            libcrux::kem::kyber::hash_functions::v_PRF::<generic_value!(todo)>(\n                                rust_primitives::unsize(prf_input),\n                            )\n                        };\n                        {\n                            let secret: libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement = {libcrux::kem::kyber::sampling::sample_from_binomial_distribution::<generic_value!(todo)>(rust_primitives::unsize(prf_output))};\n                            {\n                                let _: tuple0 = {\n                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(secret_as_ntt,i,libcrux::kem::kyber::ntt::ntt_binomially_sampled_ring_element(secret))\n                                };\n                                domain_separator\n                            }\n                        }\n                    }\n                }\n            }\n        })(domain_separator)\n    }"

  in
  let domain_separator:u8 =
    Rust_primitives.Hax.failure ""
      "{\n        (for i in (0)..(K) {\n            |domain_separator| {\n                let _: tuple0 = {\n                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                        prf_input,\n                        32,\n                        domain_separator,\n                    )\n                };\n                {\n                    let domain_separator: int = { core::ops::arith::Add::add(domain_separator, 1) };\n                    {\n                        let pat_ascription!(prf_output as [int; ETA1_RANDOMNESS_SIZE]): [int;\n                            ETA1_RANDOMNESS_SIZE] = {\n                            libcrux::kem::kyber::hash_functions::v_PRF::<generic_value!(todo)>(\n                                rust_primitives::unsize(prf_input),\n                            )\n                        };\n                        {\n                            let error: libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement = {libcrux::kem::kyber::sampling::sample_from_binomial_distribution::<generic_value!(todo)>(rust_primitives::unsize(prf_output))};\n                            {\n                                let _: tuple0 = {\n                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(error_as_ntt,i,libcrux::kem::kyber::ntt::ntt_binomially_sampled_ring_element(error))\n                                };\n                                domain_separator\n                            }\n                        }\n                    }\n                }\n            }\n        })(domain_separator)\n    }"

  in
  let tt_as_ntt:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Libcrux.Kem.Kyber.Ntt.compute_As_plus_e v_K v_A_transpose secret_as_ntt error_as_ntt
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__new v_PUBLIC_KEY_SIZE
      (Rust_primitives.Hax.repeat 0uy v_PUBLIC_KEY_SIZE <: t_Array u8 v_PUBLIC_KEY_SIZE)
  in
  let public_key_serialized:Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized
      (Rust_primitives.unsize (serialize_key v_K v_RANKED_BYTES_PER_RING_ELEMENT tt_as_ntt
            <:
            t_Array u8 v_RANKED_BYTES_PER_RING_ELEMENT)
        <:
        t_Slice u8)
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Libcrux.Kem.Kyber.Conversions.impl__array v_PUBLIC_KEY_SIZE
      (Libcrux.Kem.Kyber.Conversions.f_push public_key_serialized seed_for_A
        <:
        Libcrux.Kem.Kyber.Conversions.t_UpdatableArray v_PUBLIC_KEY_SIZE)
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_key v_K v_PRIVATE_KEY_SIZE secret_as_ntt
  in
  (Core.Convert.f_into secret_key_serialized, Core.Convert.f_into public_key_serialized
    <:
    (Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
      Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE)),
  sampling_A_error
  <:
  ((Libcrux.Kem.Kyber.Types.t_PrivateKey v_PRIVATE_KEY_SIZE &
      Libcrux.Kem.Kyber.Types.t_KyberPublicKey v_PUBLIC_KEY_SIZE) &
    Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
