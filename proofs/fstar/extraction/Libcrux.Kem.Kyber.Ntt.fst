module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_ZETAS_MONTGOMERY_DOMAIN: array i32 128sz =
  let list =
    [
      1044l; 758l; 359l; 1517l; 1493l; 1422l; 287l; 202l; 171l; 622l; 1577l; 182l; 962l; 1202l;
      1474l; 1468l; 573l; 1325l; 264l; 383l; 829l; 1458l; 1602l; 130l; 681l; 1017l; 732l; 608l;
      1542l; 411l; 205l; 1571l; 1223l; 652l; 552l; 1015l; 1293l; 1491l; 282l; 1544l; 516l; 8l; 320l;
      666l; 1618l; 1162l; 126l; 1469l; 853l; 90l; 271l; 830l; 107l; 1421l; 247l; 951l; 398l; 961l;
      1508l; 725l; 448l; 1065l; 677l; 1275l; 1103l; 430l; 555l; 843l; 1251l; 871l; 1550l; 105l; 422l;
      587l; 177l; 235l; 291l; 460l; 1574l; 1653l; 246l; 778l; 1159l; 147l; 777l; 1483l; 602l; 1119l;
      1590l; 644l; 872l; 349l; 418l; 329l; 156l; 75l; 817l; 1097l; 603l; 610l; 1322l; 1285l; 1465l;
      384l; 1215l; 136l; 1218l; 1335l; 874l; 220l; 1187l; 1659l; 1185l; 1530l; 1278l; 794l; 1510l;
      854l; 870l; 478l; 108l; 308l; 996l; 991l; 958l; 1460l; 1522l; 1628l
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list list

let ntt_representation (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let zeta_i:usize = 0sz in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 128sz <: usize
                })
              (2sz *. 128sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i +. 1sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = offset;
                      Core.Ops.Range.Range.f_end = offset +. 128sz <: usize
                    })
                <:
                _)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re.[ j +. 128sz <: usize ]
                          <:
                          i32) *.
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 128sz <: usize)
                      ((re.[ j ] <: i32) -. t <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 64sz <: usize
                })
              (2sz *. 64sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i +. 1sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = offset;
                      Core.Ops.Range.Range.f_end = offset +. 64sz <: usize
                    })
                <:
                _)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re.[ j +. 64sz <: usize ]
                          <:
                          i32) *.
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 64sz <: usize)
                      ((re.[ j ] <: i32) -. t <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 32sz <: usize
                })
              (2sz *. 32sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i +. 1sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = offset;
                      Core.Ops.Range.Range.f_end = offset +. 32sz <: usize
                    })
                <:
                _)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re.[ j +. 32sz <: usize ]
                          <:
                          i32) *.
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 32sz <: usize)
                      ((re.[ j ] <: i32) -. t <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 16sz <: usize
                })
              (2sz *. 16sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i +. 1sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = offset;
                      Core.Ops.Range.Range.f_end = offset +. 16sz <: usize
                    })
                <:
                _)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re.[ j +. 16sz <: usize ]
                          <:
                          i32) *.
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 16sz <: usize)
                      ((re.[ j ] <: i32) -. t <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 8sz <: usize
                })
              (2sz *. 8sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i +. 1sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = offset;
                      Core.Ops.Range.Range.f_end = offset +. 8sz <: usize
                    })
                <:
                _)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re.[ j +. 8sz <: usize ] <: i32
                        ) *.
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 8sz <: usize)
                      ((re.[ j ] <: i32) -. t <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 4sz <: usize
                })
              (2sz *. 4sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i +. 1sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = offset;
                      Core.Ops.Range.Range.f_end = offset +. 4sz <: usize
                    })
                <:
                _)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re.[ j +. 4sz <: usize ] <: i32
                        ) *.
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 4sz <: usize)
                      ((re.[ j ] <: i32) -. t <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 2sz <: usize
                })
              (2sz *. 2sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i +. 1sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = offset;
                      Core.Ops.Range.Range.f_end = offset +. 2sz <: usize
                    })
                <:
                _)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re.[ j +. 2sz <: usize ] <: i32
                        ) *.
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 2sz <: usize)
                      ((re.[ j ] <: i32) -. t <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 re
          .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
        Libcrux.Kem.Kyber.Arithmetic.barrett_reduce
    }
  in
  re

let invert_ntt_montgomery (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let zeta_i:usize = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /. 2sz in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 2sz <: usize
                })
              (2sz *. 2sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i -. 1sz in
          let zeta_i_value:i32 = v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] in
          let v_end:usize = offset +. 2sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = offset; Core.Ops.Range.Range.f_end = v_end })
                <:
                _)
              re
              (fun re j ->
                  let a_minus_b:i32 = (re.[ j +. 2sz <: usize ] <: i32) -. (re.[ j ] <: i32) in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      j
                      ((re.[ j ] <: i32) +. (re.[ j +. 2sz <: usize ] <: i32) <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 2sz <: usize)
                      (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *. zeta_i_value
                            <:
                            i32)
                        <:
                        i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 4sz <: usize
                })
              (2sz *. 4sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i -. 1sz in
          let zeta_i_value:i32 = v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] in
          let v_end:usize = offset +. 4sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = offset; Core.Ops.Range.Range.f_end = v_end })
                <:
                _)
              re
              (fun re j ->
                  let a_minus_b:i32 = (re.[ j +. 4sz <: usize ] <: i32) -. (re.[ j ] <: i32) in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      j
                      ((re.[ j ] <: i32) +. (re.[ j +. 4sz <: usize ] <: i32) <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 4sz <: usize)
                      (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *. zeta_i_value
                            <:
                            i32)
                        <:
                        i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 8sz <: usize
                })
              (2sz *. 8sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i -. 1sz in
          let zeta_i_value:i32 = v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] in
          let v_end:usize = offset +. 8sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = offset; Core.Ops.Range.Range.f_end = v_end })
                <:
                _)
              re
              (fun re j ->
                  let a_minus_b:i32 = (re.[ j +. 8sz <: usize ] <: i32) -. (re.[ j ] <: i32) in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      j
                      ((re.[ j ] <: i32) +. (re.[ j +. 8sz <: usize ] <: i32) <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 8sz <: usize)
                      (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *. zeta_i_value
                            <:
                            i32)
                        <:
                        i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 16sz <: usize
                })
              (2sz *. 16sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i -. 1sz in
          let zeta_i_value:i32 = v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] in
          let v_end:usize = offset +. 16sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = offset; Core.Ops.Range.Range.f_end = v_end })
                <:
                _)
              re
              (fun re j ->
                  let a_minus_b:i32 = (re.[ j +. 16sz <: usize ] <: i32) -. (re.[ j ] <: i32) in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      j
                      ((re.[ j ] <: i32) +. (re.[ j +. 16sz <: usize ] <: i32) <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 16sz <: usize)
                      (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *. zeta_i_value
                            <:
                            i32)
                        <:
                        i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 32sz <: usize
                })
              (2sz *. 32sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i -. 1sz in
          let zeta_i_value:i32 = v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] in
          let v_end:usize = offset +. 32sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = offset; Core.Ops.Range.Range.f_end = v_end })
                <:
                _)
              re
              (fun re j ->
                  let a_minus_b:i32 = (re.[ j +. 32sz <: usize ] <: i32) -. (re.[ j ] <: i32) in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      j
                      ((re.[ j ] <: i32) +. (re.[ j +. 32sz <: usize ] <: i32) <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 32sz <: usize)
                      (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *. zeta_i_value
                            <:
                            i32)
                        <:
                        i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 64sz <: usize
                })
              (2sz *. 64sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i -. 1sz in
          let zeta_i_value:i32 = v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] in
          let v_end:usize = offset +. 64sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = offset; Core.Ops.Range.Range.f_end = v_end })
                <:
                _)
              re
              (fun re j ->
                  let a_minus_b:i32 = (re.[ j +. 64sz <: usize ] <: i32) -. (re.[ j ] <: i32) in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      j
                      ((re.[ j ] <: i32) +. (re.[ j +. 64sz <: usize ] <: i32) <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 64sz <: usize)
                      (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *. zeta_i_value
                            <:
                            i32)
                        <:
                        i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT -. 128sz <: usize
                })
              (2sz *. 128sz <: usize)
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) offset ->
          let zeta_i:Prims.unit = zeta_i -. 1sz in
          let zeta_i_value:i32 = v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] in
          let v_end:usize = offset +. 128sz in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = offset; Core.Ops.Range.Range.f_end = v_end })
                <:
                _)
              re
              (fun re j ->
                  let a_minus_b:i32 = (re.[ j +. 128sz <: usize ] <: i32) -. (re.[ j ] <: i32) in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      j
                      ((re.[ j ] <: i32) +. (re.[ j +. 128sz <: usize ] <: i32) <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    Rust_primitives.Hax.update_at re
                      (j +. 128sz <: usize)
                      (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *. zeta_i_value
                            <:
                            i32)
                        <:
                        i32)
                  in
                  re)
          in
          re, zeta_i)
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 re
          .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
        (fun coefficient ->
            Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce
                  (coefficient *. 1441l <: i32)
                <:
                i32)
            <:
            i32)
    }
  in
  re

let ntt_multiply_binomials (a0, a1: (i32 & i32)) (b0, b1: (i32 & i32)) (zeta: i32) : (i32 & i32) =
  (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a0 *. b0 <: i32) <: i32) +.
  (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a1 *.
              b1
              <:
              i32)
          <:
          i32) *.
        zeta
        <:
        i32)
    <:
    i32),
  (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a0 *. b1 <: i32) <: i32) +.
  (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a1 *. b0 <: i32) <: i32)

let ntt_multiply (left right: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                })
              4sz
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      out
      (fun out i ->
          let product:(i32 & i32) =
            ntt_multiply_binomials ((left.[ i ] <: i32), (left.[ i +. 1sz <: usize ] <: i32))
              ((right.[ i ] <: i32), (right.[ i +. 1sz <: usize ] <: i32))
              (v_ZETAS_MONTGOMERY_DOMAIN.[ 64sz +. (i /. 4sz <: usize) <: usize ] <: i32)
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out i product._1
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out (i +. 1sz <: usize) product._2
          in
          let product:(i32 & i32) =
            ntt_multiply_binomials ((left.[ i +. 2sz <: usize ] <: i32),
                (left.[ i +. 3sz <: usize ] <: i32))
              ((right.[ i +. 2sz <: usize ] <: i32), (right.[ i +. 3sz <: usize ] <: i32))
              (Core.Ops.Arith.Neg.neg (v_ZETAS_MONTGOMERY_DOMAIN.[ 64sz +. (i /. 4sz <: usize)
                      <:
                      usize ]
                    <:
                    i32)
                <:
                i32)
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out (i +. 2sz <: usize) product._1
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out (i +. 3sz <: usize) product._2
          in
          out)
  in
  out

let multiply_row_by_column_montgomery
      (#k: usize)
      (row_vector column_vector:
          array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let result =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.zip
              (Core.Slice.iter_under_impl (Rust_primitives.unsize row_vector
                    <:
                    slice Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              (Core.Slice.iter_under_impl (Rust_primitives.unsize column_vector
                    <:
                    slice Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
            <:
            Core.Iter.Adapters.Zip.t_Zip
              (Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) _)
        <:
        _)
      result
      (fun result (row_element, column_element) ->
          result +.
          (ntt_multiply row_element column_element
            <:
            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          <:
          _)
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      result with
      Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 result
          .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
        Libcrux.Kem.Kyber.Arithmetic.barrett_reduce
    }
  in
  result

let multiply_matrix_by_column_montgomery
      (#k: usize)
      (matrix: array (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K)
      (vector: array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
  let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl (Rust_primitives.unsize matrix
                    <:
                    slice (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
                <:
                Core.Slice.Iter.t_Iter
                (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)))
        <:
        _)
      result
      (fun result (i, row) ->
          let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  (Core.Iter.Traits.Iterator.Iterator.enumerate (Core.Slice.iter_under_impl (Rust_primitives.unsize
                              row
                            <:
                            slice Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                        <:
                        Core.Slice.Iter.t_Iter
                        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement))
                <:
                _)
              result
              (fun result (j, matrix_element) ->
                  let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    ntt_multiply matrix_element
                      (vector.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
                    Rust_primitives.Hax.update_at result
                      i
                      ((result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +.
                        product
                        <:
                        _)
                  in
                  result)
          in
          let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at result
              i
              ({
                  (result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) with
                  Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  =
                  Core.Array.map_under_impl_23 (result.[ i ]
                      <:
                      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                      .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    Libcrux.Kem.Kyber.Arithmetic.barrett_reduce
                  <:
                  array i32 256sz
                })
          in
          result)
  in
  result

let multiply_matrix_by_column
      (#k: usize)
      (matrix: array (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K)
      (vector: array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
  let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl v_K
  in
  let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl (Rust_primitives.unsize matrix
                    <:
                    slice (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
                <:
                Core.Slice.Iter.t_Iter
                (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)))
        <:
        _)
      result
      (fun result (i, row) ->
          let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  (Core.Iter.Traits.Iterator.Iterator.enumerate (Core.Slice.iter_under_impl (Rust_primitives.unsize
                              row
                            <:
                            slice Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                        <:
                        Core.Slice.Iter.t_Iter
                        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement))
                <:
                _)
              result
              (fun result (j, matrix_element) ->
                  let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    ntt_multiply matrix_element
                      (vector.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
                    Rust_primitives.Hax.update_at result
                      i
                      ((result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) +.
                        product
                        <:
                        _)
                  in
                  result)
          in
          let result:array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at result
              i
              ({
                  (result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) with
                  Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  =
                  Core.Array.map_under_impl_23 (result.[ i ]
                      <:
                      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                      .Libcrux.Kem.Kyber.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    (fun coefficient ->
                        let coefficient_montgomery:i32 =
                          Libcrux.Kem.Kyber.Arithmetic.to_montgomery_domain coefficient
                        in
                        Libcrux.Kem.Kyber.Arithmetic.barrett_reduce coefficient_montgomery)
                  <:
                  array i32 256sz
                })
          in
          result)
  in
  result