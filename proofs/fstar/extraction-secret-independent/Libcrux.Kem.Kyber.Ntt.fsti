module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i32 (sz 128) =
  let list =
    [
      (-1044l); (-758l); (-359l); (-1517l); 1493l; 1422l; 287l; 202l; (-171l); 622l; 1577l; 182l;
      962l; (-1202l); (-1474l); 1468l; 573l; (-1325l); 264l; 383l; (-829l); 1458l; (-1602l); (-130l);
      (-681l); 1017l; 732l; 608l; (-1542l); 411l; (-205l); (-1571l); 1223l; 652l; (-552l); 1015l;
      (-1293l); 1491l; (-282l); (-1544l); 516l; (-8l); (-320l); (-666l); (-1618l); (-1162l); 126l;
      1469l; (-853l); (-90l); (-271l); 830l; 107l; (-1421l); (-247l); (-951l); (-398l); 961l;
      (-1508l); (-725l); 448l; (-1065l); 677l; (-1275l); (-1103l); 430l; 555l; 843l; (-1251l); 871l;
      1550l; 105l; 422l; 587l; 177l; (-235l); (-291l); (-460l); 1574l; 1653l; (-246l); 778l; 1159l;
      (-147l); (-777l); 1483l; (-602l); 1119l; (-1590l); 644l; (-872l); 349l; 418l; 329l; (-156l);
      (-75l); 817l; 1097l; 603l; 610l; 1322l; (-1285l); (-1465l); 384l; (-1215l); (-136l); 1218l;
      (-1335l); (-874l); 220l; (-1187l); (-1659l); (-1185l); (-1530l); (-1278l); 794l; (-1510l);
      (-854l); (-870l); 478l; (-108l); (-308l); 996l; 991l; 958l; (-1460l); 1522l; 1628l
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list list

val ntt_multiply_binomials: (i32 & i32) -> (i32 & i32) -> zeta: i32
  -> Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery (v_K: usize) (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_3_
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_3328_
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_binomially_sampled_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <.
                  (Core.Slice.impl__len (Rust_primitives.unsize re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize)
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    (Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                          <:
                          i32)
                      <:
                      i32) <=.
                    3l
                    <:
                    bool)
              <:
              bool))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Hax_lib.v_forall (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len (Rust_primitives.unsize result
                              .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      v (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[
                              i ]
                            <:
                            i32)
                        <:
                        i32) <
                      v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool)
                <:
                bool))

val ntt_multiply (lhs rhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    let lhs_i = (lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32) in
                    (lhs_i >=. 0l <: bool) &&
                    (lhs_i <. 4096l <: bool
                    ) &&
                    (v (Core.Num.impl__i32__abs (rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                            <:
                            i32)
                        <:
                        i32) <=
                      v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool))
              <:
              bool))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Hax_lib.v_forall (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len (Rust_primitives.unsize result
                              .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      v (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[
                              i ]
                            <:
                            i32)
                        <:
                        i32) <=
                      v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool)
                <:
                bool))

val ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <.
                  (Core.Slice.impl__len (Rust_primitives.unsize re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize)
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    (Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                          <:
                          i32)
                      <:
                      i32) <=.
                    3328l
                    <:
                    bool)
              <:
              bool))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Hax_lib.v_forall (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len (Rust_primitives.unsize result
                              .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      v (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[
                              i ]
                            <:
                            i32)
                        <:
                        i32) <
                      v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool)
                <:
                bool))
