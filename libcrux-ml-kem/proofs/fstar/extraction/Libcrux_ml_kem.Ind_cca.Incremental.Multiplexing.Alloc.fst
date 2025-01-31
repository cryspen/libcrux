module Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.Alloc
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Ind_cca.Incremental.Types in
  ()

let generate_keypair
      (v_K v_CPA_PRIVATE_KEY_SIZE v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (randomness: t_Array u8 (mk_usize 64))
     =
  Rust_primitives.unsize (Rust_primitives.unsize (if
            Libcrux_platform.Platform.simd256_support () <: bool
          then
            Rust_primitives.unsize (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Avx2.generate_keypair
                      v_K
                      v_CPA_PRIVATE_KEY_SIZE
                      v_PRIVATE_KEY_SIZE
                      v_PUBLIC_KEY_SIZE
                      v_BYTES_PER_RING_ELEMENT
                      v_ETA1
                      v_ETA1_RANDOMNESS_SIZE
                      randomness
                    <:
                    Alloc.Boxed.t_Box
                      (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
                          Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector) Alloc.Alloc.t_Global)
                <:
                Alloc.Boxed.t_Box
                  (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
                  Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
              Alloc.Alloc.t_Global
          else
            if Libcrux_platform.Platform.simd128_support () <: bool
            then
              Rust_primitives.unsize (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Neon.generate_keypair
                        v_K
                        v_CPA_PRIVATE_KEY_SIZE
                        v_PRIVATE_KEY_SIZE
                        v_PUBLIC_KEY_SIZE
                        v_BYTES_PER_RING_ELEMENT
                        v_ETA1
                        v_ETA1_RANDOMNESS_SIZE
                        randomness
                      <:
                      Alloc.Boxed.t_Box
                        (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
                            Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
                        Alloc.Alloc.t_Global)
                  <:
                  Alloc.Boxed.t_Box
                    (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
                    Alloc.Alloc.t_Global)
              <:
              Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
                Alloc.Alloc.t_Global
            else
              Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Portable.generate_keypair v_K
                    v_CPA_PRIVATE_KEY_SIZE
                    v_PRIVATE_KEY_SIZE
                    v_PUBLIC_KEY_SIZE
                    v_BYTES_PER_RING_ELEMENT
                    v_ETA1
                    v_ETA1_RANDOMNESS_SIZE
                    randomness
                  <:
                  Alloc.Boxed.t_Box
                    (Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
                        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
                    Alloc.Alloc.t_Global)
              <:
              Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
                Alloc.Alloc.t_Global)
      <:
      Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
        Alloc.Alloc.t_Global)

let encapsulate1
      (v_K v_CIPHERTEXT_SIZE v_C1_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (public_key_part: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey1)
      (randomness: t_Array u8 (mk_usize 32))
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    let c, s, ss:(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
      Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
        Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector &
      t_Array u8 (mk_usize 32)) =
      Libcrux_ml_kem.Ind_cca.Incremental.Avx2.encapsulate1 v_K v_CIPHERTEXT_SIZE v_C1_SIZE
        v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
        v_ETA2_RANDOMNESS_SIZE public_key_part randomness
    in
    c, Rust_primitives.unsize s, ss
    <:
    (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
      Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
        Alloc.Alloc.t_Global &
      t_Array u8 (mk_usize 32))
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      let c, s, ss:(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
          Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector &
        t_Array u8 (mk_usize 32)) =
        Libcrux_ml_kem.Ind_cca.Incremental.Neon.encapsulate1 v_K v_CIPHERTEXT_SIZE v_C1_SIZE
          v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
          v_ETA2_RANDOMNESS_SIZE public_key_part randomness
      in
      c, Rust_primitives.unsize s, ss
      <:
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
        Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
          Alloc.Alloc.t_Global &
        t_Array u8 (mk_usize 32))
    else
      let c, s, ss:(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector &
        t_Array u8 (mk_usize 32)) =
        Libcrux_ml_kem.Ind_cca.Incremental.Portable.encapsulate1 v_K v_CIPHERTEXT_SIZE v_C1_SIZE
          v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_U_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
          v_ETA2_RANDOMNESS_SIZE public_key_part randomness
      in
      c, Rust_primitives.unsize s, ss
      <:
      (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE &
        Alloc.Boxed.t_Box (dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
          Alloc.Alloc.t_Global &
        t_Array u8 (mk_usize 32))

let encapsulate2
      (v_K v_PK2_LEN v_C2_SIZE v_VECTOR_V_COMPRESSION_FACTOR: usize)
      (state: dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
      (public_key_part: t_Slice u8)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    let state:Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector =
      Libcrux_ml_kem.Ind_cca.Incremental.Avx2.as_state v_K
        (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Types.f_as_any #(dyn 1
                    (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
                #FStar.Tactics.Typeclasses.solve
                state
              <:
              dyn 1 (fun z -> Core.Any.t_Any z))
          <:
          dyn 1 (fun z -> Core.Any.t_Any z))
    in
    match
      Core.Convert.f_try_from #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
        #(t_Slice u8)
        #FStar.Tactics.Typeclasses.solve
        public_key_part
      <:
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
    with
    | Core.Result.Result_Ok pk2 ->
      Core.Result.Result_Ok
      (Libcrux_ml_kem.Ind_cca.Incremental.Avx2.encapsulate2 v_K
          v_PK2_LEN
          v_C2_SIZE
          v_VECTOR_V_COMPRESSION_FACTOR
          state
          pk2)
      <:
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
        Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      let state:Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
        Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
        Libcrux_ml_kem.Ind_cca.Incremental.Neon.as_state v_K
          (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Types.f_as_any #(dyn 1
                      (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
                  #FStar.Tactics.Typeclasses.solve
                  state
                <:
                dyn 1 (fun z -> Core.Any.t_Any z))
            <:
            dyn 1 (fun z -> Core.Any.t_Any z))
      in
      match
        Core.Convert.f_try_from #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          public_key_part
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      with
      | Core.Result.Result_Ok pk2 ->
        Core.Result.Result_Ok
        (Libcrux_ml_kem.Ind_cca.Incremental.Neon.encapsulate2 v_K
            v_PK2_LEN
            v_C2_SIZE
            v_VECTOR_V_COMPRESSION_FACTOR
            state
            pk2)
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
    else
      let state:Libcrux_ml_kem.Ind_cca.Incremental.Types.t_EncapsState v_K
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
        Libcrux_ml_kem.Ind_cca.Incremental.Portable.as_state v_K
          (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Types.f_as_any #(dyn 1
                      (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_State z))
                  #FStar.Tactics.Typeclasses.solve
                  state
                <:
                dyn 1 (fun z -> Core.Any.t_Any z))
            <:
            dyn 1 (fun z -> Core.Any.t_Any z))
      in
      match
        Core.Convert.f_try_from #(Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          public_key_part
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_PublicKey2 v_PK2_LEN)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      with
      | Core.Result.Result_Ok pk2 ->
        Core.Result.Result_Ok
        (Libcrux_ml_kem.Ind_cca.Incremental.Portable.encapsulate2 v_K
            v_PK2_LEN
            v_C2_SIZE
            v_VECTOR_V_COMPRESSION_FACTOR
            state
            pk2)
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
          Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Error

let decapsulate
      (v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE:
          usize)
      (private_key: dyn 1 (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
      (ciphertext1: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext1 v_C1_SIZE)
      (ciphertext2: Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Ciphertext2 v_C2_SIZE)
     =
  if Libcrux_platform.Platform.simd256_support ()
  then
    let private_key:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
      Libcrux_ml_kem.Vector.Avx2.t_SIMD256Vector =
      Libcrux_ml_kem.Ind_cca.Incremental.Avx2.as_keypair v_K
        (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Types.f_as_any #(dyn 1
                    (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
                #FStar.Tactics.Typeclasses.solve
                private_key
              <:
              dyn 1 (fun z -> Core.Any.t_Any z))
          <:
          dyn 1 (fun z -> Core.Any.t_Any z))
    in
    Libcrux_ml_kem.Ind_cca.Incremental.Avx2.decapsulate v_K v_SECRET_KEY_SIZE v_CPA_SECRET_KEY_SIZE
      v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE v_C2_SIZE
      v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
      v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
      private_key ciphertext1 ciphertext2
  else
    if Libcrux_platform.Platform.simd128_support ()
    then
      let private_key:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
        Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector =
        Libcrux_ml_kem.Ind_cca.Incremental.Neon.as_keypair v_K
          (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Types.f_as_any #(dyn 1
                      (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
                  #FStar.Tactics.Typeclasses.solve
                  private_key
                <:
                dyn 1 (fun z -> Core.Any.t_Any z))
            <:
            dyn 1 (fun z -> Core.Any.t_Any z))
      in
      Libcrux_ml_kem.Ind_cca.Incremental.Neon.decapsulate v_K v_SECRET_KEY_SIZE
        v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
        v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
        v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
        private_key ciphertext1 ciphertext2
    else
      let private_key:Libcrux_ml_kem.Ind_cca.Unpacked.t_MlKemKeyPairUnpacked v_K
        Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
        Libcrux_ml_kem.Ind_cca.Incremental.Portable.as_keypair v_K
          (Rust_primitives.unsize (Libcrux_ml_kem.Ind_cca.Incremental.Types.f_as_any #(dyn 1
                      (fun z -> Libcrux_ml_kem.Ind_cca.Incremental.Types.t_Keys z))
                  #FStar.Tactics.Typeclasses.solve
                  private_key
                <:
                dyn 1 (fun z -> Core.Any.t_Any z))
            <:
            dyn 1 (fun z -> Core.Any.t_Any z))
      in
      Libcrux_ml_kem.Ind_cca.Incremental.Portable.decapsulate v_K v_SECRET_KEY_SIZE
        v_CPA_SECRET_KEY_SIZE v_PUBLIC_KEY_SIZE v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_SIZE
        v_C2_SIZE v_VECTOR_U_COMPRESSION_FACTOR v_VECTOR_V_COMPRESSION_FACTOR v_C1_BLOCK_SIZE v_ETA1
        v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE v_IMPLICIT_REJECTION_HASH_INPUT_SIZE
        private_key ciphertext1 ciphertext2
