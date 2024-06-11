module Libcrux_ml_kem.Hash_functions.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// The state.
/// It's only used for SHAKE128.
/// All other functions don't actually use any members.
type t_Simd256Hash = { f_shake128_state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_K: usize) : Libcrux_ml_kem.Hash_functions.t_Hash t_Simd256Hash v_K =
  {
    f_G_pre = (fun (input: t_Slice u8) -> true);
    f_G_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 64)) -> true);
    f_G
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
        let digest:t_Array u8 (sz 64) = Libcrux_sha3.Portable.sha512 digest input in
        digest);
    f_H_pre = (fun (input: t_Slice u8) -> true);
    f_H_post = (fun (input: t_Slice u8) (out: t_Array u8 (sz 32)) -> true);
    f_H
    =
    (fun (input: t_Slice u8) ->
        let digest:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
        let digest:t_Array u8 (sz 32) = Libcrux_sha3.Portable.sha256 digest input in
        digest);
    f_PRF_pre = (fun (v_LEN: usize) (input: t_Slice u8) -> true);
    f_PRF_post = (fun (v_LEN: usize) (input: t_Slice u8) (out: t_Array u8 v_LEN) -> true);
    f_PRF
    =
    (fun (v_LEN: usize) (input: t_Slice u8) ->
        let digest:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
        let digest:t_Array u8 v_LEN = Libcrux_sha3.Portable.shake256 digest input in
        digest);
    f_PRFxN_pre = (fun (v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K) -> true);
    f_PRFxN_post
    =
    (fun
        (v_LEN: usize)
        (input: t_Array (t_Array u8 (sz 33)) v_K)
        (out1: t_Array (t_Array u8 v_LEN) v_K)
        ->
        true);
    f_PRFxN
    =
    (fun (v_LEN: usize) (input: t_Array (t_Array u8 (sz 33)) v_K) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
              then
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                    <:
                    Rust_primitives.Hax.t_Never)
            in
            ()
        in
        let out:t_Array (t_Array u8 v_LEN) v_K =
          Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: t_Array u8 v_LEN) v_K
        in
        let _:Prims.unit = "failure" in
        out);
    f_shake128_init_absorb_pre = (fun (input: t_Array (t_Array u8 (sz 34)) v_K) -> true);
    f_shake128_init_absorb_post
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) (out: t_Simd256Hash) -> true);
    f_shake128_init_absorb
    =
    (fun (input: t_Array (t_Array u8 (sz 34)) v_K) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
              then
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                    <:
                    Rust_primitives.Hax.t_Never)
            in
            ()
        in
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
          Libcrux_sha3.Avx2.X4.Incremental.shake128_init ()
        in
        let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
          match cast (v_K <: usize) <: u8 with
          | 2uy ->
            let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
              Libcrux_sha3.Avx2.X4.Incremental.shake128_absorb_final state
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
            in
            state
          | 3uy ->
            let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
              Libcrux_sha3.Avx2.X4.Incremental.shake128_absorb_final state
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
            in
            state
          | 4uy ->
            let state:Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState4 =
              Libcrux_sha3.Avx2.X4.Incremental.shake128_absorb_final state
                (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
            in
            state
          | _ -> state
        in
        { f_shake128_state = state } <: t_Simd256Hash);
    f_shake128_squeeze_three_blocks_pre = (fun (self: t_Simd256Hash) -> true);
    f_shake128_squeeze_three_blocks_post
    =
    (fun (self: t_Simd256Hash) (out1: (t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K)) -> true);
    f_shake128_squeeze_three_blocks
    =
    (fun (self: t_Simd256Hash) ->
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
              then
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                    <:
                    Rust_primitives.Hax.t_Never)
            in
            ()
        in
        let out:t_Array (t_Array u8 (sz 504)) v_K =
          Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 504) <: t_Array u8 (sz 504)
            )
            v_K
        in
        let _:Prims.unit =
          match cast (v_K <: usize) <: u8 with
          | 2uy ->
            let dummy_out0:t_Array u8 (sz 504) = Rust_primitives.Hax.repeat 0uy (sz 504) in
            let dummy_out1:t_Array u8 (sz 504) = Rust_primitives.Hax.repeat 0uy (sz 504) in
            Rust_primitives.Hax.failure ""
              "{\n        let Tuple2(out0, out1): tuple2<&mut [[int; 504]], &mut [[int; 504]]> = {\n            core::slice::impl__split_at_mut::<[int; 504]>(rust_primitives::unsize(&mut (out)), 1)\n        };\n        {\n            let _: tuple0 = {\n                libcrux_sha3::avx2::x4::incremental::shake128_squeeze_first_three_blocks(\n                    &mut (deref(\n                        &mut (proj_libcrux_ml_kem::hash_functions::avx2::f_shake128_state(self)),\n                    )),\n                    rust_primitives::unsize(\n                        &mut (deref(&mut (core::ops::index::Index::index(deref(out0), 0)))),\n                    ),\n                    rust_primitives::unsize(\n                        &mut (deref(&mut (core::ops::index::Index::index(deref(out1), 0)))),\n                    ),\n                    rust_primitives::unsize(&mut (deref(&mut (dummy_out0)))),\n                    rust_primitives::unsize(&mut (deref(&mut (dummy_out1)))),\n                )\n            };\n            Tuple0\n        }\n    }"

          | 3uy ->
            let dummy_out0:t_Array u8 (sz 504) = Rust_primitives.Hax.repeat 0uy (sz 504) in
            Rust_primitives.Hax.failure ""
              "{\n        let Tuple2(out0, out12): tuple2<&mut [[int; 504]], &mut [[int; 504]]> = {\n            core::slice::impl__split_at_mut::<[int; 504]>(rust_primitives::unsize(&mut (out)), 1)\n        };\n        {\n            let Tuple2(out1, out2): tuple2<&mut [[int; 504]], &mut [[int; 504]]> =\n                { core::slice::impl__split_at_mut::<[int; 504]>(&mut (deref(out12)), 1) };\n            {\n                let _: tuple0 = {\n                    libcrux_sha3::avx2::x4::incremental::shake128_squeeze_first_three_blocks(\n                        &mut (deref(\n                            &mut (proj_libcrux_ml_kem::hash_functions::avx2::f_shake128_state(\n                                self,\n                            )),\n                        )),\n                        rust_primitives::unsize(\n                            &mut (deref(&mut (core::ops::index::Index::index(deref(out0), 0)))),\n                        ),\n                        rust_primitives::unsize(\n                            &mut (deref(&mut (core::ops::index::Index::index(deref(out1), 0)))),\n                        ),\n                        rust_primitives::unsize(\n                            &mut (deref(&mut (core::ops::index::Index::index(deref(out2), 0)))),\n                        ),\n                        rust_primitives::unsize(&mut (deref(&mut (dummy_out0)))),\n                    )\n                };\n                Tuple0\n            }\n        }\n    }"

          | 4uy ->
            Rust_primitives.Hax.failure ""
              "{\n        let Tuple2(out0, out123): tuple2<&mut [[int; 504]], &mut [[int; 504]]> = {\n            core::slice::impl__split_at_mut::<[int; 504]>(rust_primitives::unsize(&mut (out)), 1)\n        };\n        {\n            let Tuple2(out1, out23): tuple2<&mut [[int; 504]], &mut [[int; 504]]> =\n                { core::slice::impl__split_at_mut::<[int; 504]>(&mut (deref(out123)), 1) };\n            {\n                let Tuple2(out2, out3): tuple2<&mut [[int; 504]], &mut [[int; 504]]> =\n                    { core::slice::impl__split_at_mut::<[int; 504]>(&mut (deref(out23)), 1) };\n                {\n                    let _: tuple0 = {\n                        libcrux_sha3::avx2::x4::incremental::shake128_squeeze_first_three_blocks(\n                            &mut (deref(\n                                &mut (proj_libcrux_ml_kem::hash_functions::avx2::f_shake128_state(\n                                    self,\n                                )),\n                            )),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out0), 0)))),\n                            ),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out1), 0)))),\n                            ),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out2), 0)))),\n                            ),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out3), 0)))),\n                            ),\n                        )\n                    };\n                    Tuple0\n                }\n            }\n        }\n    }"

          | _ ->
            Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                          (let list =
                              [
                                "internal error: entered unreachable code: This function must only be called with N = 2, 3, 4"
                              ]
                            in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                        <:
                        t_Slice string)
                      (Rust_primitives.unsize (Core.Fmt.Rt.impl_1__none ()
                            <:
                            t_Array Core.Fmt.Rt.t_Argument (sz 0))
                        <:
                        t_Slice Core.Fmt.Rt.t_Argument)
                    <:
                    Core.Fmt.t_Arguments)
                <:
                Rust_primitives.Hax.t_Never)
        in
        let hax_temp_output:t_Array (t_Array u8 (sz 504)) v_K = out in
        self, hax_temp_output <: (t_Simd256Hash & t_Array (t_Array u8 (sz 504)) v_K));
    f_shake128_squeeze_block_pre = (fun (self: t_Simd256Hash) -> true);
    f_shake128_squeeze_block_post
    =
    (fun (self: t_Simd256Hash) (out1: (t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K)) -> true);
    f_shake128_squeeze_block
    =
    fun (self: t_Simd256Hash) ->
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            if ~.((v_K =. sz 2 <: bool) || (v_K =. sz 3 <: bool) || (v_K =. sz 4 <: bool))
            then
              Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: K == 2 || K == 3 || K == 4"

                  <:
                  Rust_primitives.Hax.t_Never)
          in
          ()
      in
      let out:t_Array (t_Array u8 (sz 168)) v_K =
        Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 168) <: t_Array u8 (sz 168))
          v_K
      in
      let _:Prims.unit =
        match cast (v_K <: usize) <: u8 with
        | 2uy ->
          let dummy_out0:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
          let dummy_out1:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
          Rust_primitives.Hax.failure ""
            "{\n        let Tuple2(out0, out1): tuple2<&mut [[int; 168]], &mut [[int; 168]]> = {\n            core::slice::impl__split_at_mut::<[int; 168]>(rust_primitives::unsize(&mut (out)), 1)\n        };\n        {\n            let _: tuple0 = {\n                libcrux_sha3::avx2::x4::incremental::shake128_squeeze_next_block(\n                    &mut (deref(\n                        &mut (proj_libcrux_ml_kem::hash_functions::avx2::f_shake128_state(self)),\n                    )),\n                    rust_primitives::unsize(\n                        &mut (deref(&mut (core::ops::index::Index::index(deref(out0), 0)))),\n                    ),\n                    rust_primitives::unsize(\n                        &mut (deref(&mut (core::ops::index::Index::index(deref(out1), 0)))),\n                    ),\n                    rust_primitives::unsize(&mut (deref(&mut (dummy_out0)))),\n                    rust_primitives::unsize(&mut (deref(&mut (dummy_out1)))),\n                )\n            };\n            Tuple0\n        }\n    }"

        | 3uy ->
          let dummy_out0:t_Array u8 (sz 168) = Rust_primitives.Hax.repeat 0uy (sz 168) in
          Rust_primitives.Hax.failure ""
            "{\n        let Tuple2(out0, out12): tuple2<&mut [[int; 168]], &mut [[int; 168]]> = {\n            core::slice::impl__split_at_mut::<[int; 168]>(rust_primitives::unsize(&mut (out)), 1)\n        };\n        {\n            let Tuple2(out1, out2): tuple2<&mut [[int; 168]], &mut [[int; 168]]> =\n                { core::slice::impl__split_at_mut::<[int; 168]>(&mut (deref(out12)), 1) };\n            {\n                let _: tuple0 = {\n                    libcrux_sha3::avx2::x4::incremental::shake128_squeeze_next_block(\n                        &mut (deref(\n                            &mut (proj_libcrux_ml_kem::hash_functions::avx2::f_shake128_state(\n                                self,\n                            )),\n                        )),\n                        rust_primitives::unsize(\n                            &mut (deref(&mut (core::ops::index::Index::index(deref(out0), 0)))),\n                        ),\n                        rust_primitives::unsize(\n                            &mut (deref(&mut (core::ops::index::Index::index(deref(out1), 0)))),\n                        ),\n                        rust_primitives::unsize(\n                            &mut (deref(&mut (core::ops::index::Index::index(deref(out2), 0)))),\n                        ),\n                        rust_primitives::unsize(&mut (deref(&mut (dummy_out0)))),\n                    )\n                };\n                Tuple0\n            }\n        }\n    }"

        | 4uy ->
          Rust_primitives.Hax.failure ""
            "{\n        let Tuple2(out0, out123): tuple2<&mut [[int; 168]], &mut [[int; 168]]> = {\n            core::slice::impl__split_at_mut::<[int; 168]>(rust_primitives::unsize(&mut (out)), 1)\n        };\n        {\n            let Tuple2(out1, out23): tuple2<&mut [[int; 168]], &mut [[int; 168]]> =\n                { core::slice::impl__split_at_mut::<[int; 168]>(&mut (deref(out123)), 1) };\n            {\n                let Tuple2(out2, out3): tuple2<&mut [[int; 168]], &mut [[int; 168]]> =\n                    { core::slice::impl__split_at_mut::<[int; 168]>(&mut (deref(out23)), 1) };\n                {\n                    let _: tuple0 = {\n                        libcrux_sha3::avx2::x4::incremental::shake128_squeeze_next_block(\n                            &mut (deref(\n                                &mut (proj_libcrux_ml_kem::hash_functions::avx2::f_shake128_state(\n                                    self,\n                                )),\n                            )),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out0), 0)))),\n                            ),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out1), 0)))),\n                            ),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out2), 0)))),\n                            ),\n                            rust_primitives::unsize(\n                                &mut (deref(&mut (core::ops::index::Index::index(deref(out3), 0)))),\n                            ),\n                        )\n                    };\n                    Tuple0\n                }\n            }\n        }\n    }"

        | _ ->
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                        (let list =
                            [
                              "internal error: entered unreachable code: This function is only called with 2, 3, 4"
                            ]
                          in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      t_Slice string)
                    (Rust_primitives.unsize (Core.Fmt.Rt.impl_1__none ()
                          <:
                          t_Array Core.Fmt.Rt.t_Argument (sz 0))
                      <:
                      t_Slice Core.Fmt.Rt.t_Argument)
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Rust_primitives.Hax.t_Never)
      in
      let hax_temp_output:t_Array (t_Array u8 (sz 168)) v_K = out in
      self, hax_temp_output <: (t_Simd256Hash & t_Array (t_Array u8 (sz 168)) v_K)
  }
