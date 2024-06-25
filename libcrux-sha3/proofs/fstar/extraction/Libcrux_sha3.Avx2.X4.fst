module Libcrux_sha3.Avx2.X4
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let shake256
      (v_LEN: usize)
      (input0 input1 input2 input3: t_Slice u8)
      (out: t_Array (t_Array u8 v_LEN) (sz 4))
     =
  let hax_temp_output:Prims.unit =
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                  (let list =
                      [
                        "not implemented: The target architecture does not support neon instructions."
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
  out
