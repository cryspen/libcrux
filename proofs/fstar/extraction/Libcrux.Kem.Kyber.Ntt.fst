module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_ZETAS_MONTGOMERY_DOMAIN: t_Array i32 (sz 128) =
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

let ntt_binomially_sampled_ring_element
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient -> (Core.Num.impl__i32__abs coefficient <: i32) <=. 3l <: bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient| coefficient.abs() <= 3)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let zeta_i:usize = sz 0 in
  let zeta_i:usize = zeta_i +! sz 1 in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128
            })
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re j ->
          let t:i32 =
            (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! sz 128 <: usize ] <: i32) *!
            (-1600l)
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (j +! sz 128 <: usize)
                ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                j
                ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
            }
          in
          re)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3l +! (3l *! (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32) <: i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3 + (3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 6l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3l +!
                (((8l -! 6l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3 + ((8 - 6) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 5l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3l +!
                (((8l -! 5l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3 + ((8 - 5) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 4l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3l +!
                (((8l -! 4l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3 + ((8 - 4) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 3l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3l +!
                (((8l -! 3l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3 + ((8 - 3) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 2l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3l +!
                (((8l -! 2l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3 + ((8 - 2) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 1l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3l +!
                (((8l -! 1l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3 + ((8 - 1) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
        Libcrux.Kem.Kyber.Arithmetic.barrett_reduce
    }
  in
  re

let ntt_vector_u
      (#v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient -> (Core.Num.impl__i32__abs coefficient <: i32) <=. 3328l <: bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient| coefficient.abs() <= 3328)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let zeta_i:usize = sz 0 in
  let step:usize = sz 1 <<! 7l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3328l +!
                (((8l -! 7l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3328 + ((8 - 7) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 6l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3328l +!
                (((8l -! 6l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3328 + ((8 - 6) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 5l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3328l +!
                (((8l -! 5l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3328 + ((8 - 5) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 4l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3328l +!
                (((8l -! 4l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3328 + ((8 - 4) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 3l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3328l +!
                (((8l -! 3l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3328 + ((8 - 3) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 2l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3328l +!
                (((8l -! 2l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3328 + ((8 - 2) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let step:usize = sz 1 <<! 1l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i +! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let t:i32 =
                    Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                          <:
                          i32) *!
                        (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                        <:
                        i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              (3328l +!
                (((8l -! 1l <: i32) *! 3l <: i32) *!
                  (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS /! 2l <: i32)
                  <:
                  i32)
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        { coefficient.abs() < 3328 + ((8 - 1) * 3 * (FIELD_MODULUS / 2)) })"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
        Libcrux.Kem.Kyber.Arithmetic.barrett_reduce
    }
  in
  re

let invert_ntt_montgomery
      (#v_K: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              ((cast v_K <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().all(|coefficient|\\n        coefficient.abs() < (K as i32) * FIELD_MODULUS)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let zeta_i:usize = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 2 in
  let step:usize = sz 1 <<! 1l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let step:usize = sz 1 <<! 2l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let step:usize = sz 1 <<! 3l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let step:usize = sz 1 <<! 4l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let step:usize = sz 1 <<! 5l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let step:usize = sz 1 <<! 6l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let step:usize = sz 1 <<! 7l in
  let re, zeta_i:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128 /! step <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      (re, zeta_i)
      (fun (re, zeta_i) round ->
          let zeta_i:usize = zeta_i -! sz 1 in
          let offset:usize = (round *! step <: usize) *! sz 2 in
          let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! step <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              re
              (fun re j ->
                  let a_minus_b:i32 =
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ] <: i32) -!
                    (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +!
                          (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! step <: usize ]
                            <:
                            i32)
                          <:
                          i32)
                    }
                  in
                  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    {
                      re with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        (j +! step <: usize)
                        (Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a_minus_b *!
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                          <:
                          i32)
                    }
                  in
                  re)
          in
          re, zeta_i)
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(((Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 0 ]
                    <:
                    i32)
                <:
                i32) <.
              ((128l *! (cast v_K <: i32) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                <:
                i32)
              <:
              bool) &&
            ((Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 1 ]
                    <:
                    i32)
                <:
                i32) <.
              ((128l *! (cast v_K <: i32) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                <:
                i32)
              <:
              bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients[0].abs() < 128 * (K as i32) * FIELD_MODULUS &&\\n    re.coefficients[1].abs() < 128 * (K as i32) * FIELD_MODULUS"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Iter.Adapters.Skip.t_Skip
        (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Array.Iter.t_IntoIter i32 (sz 256))) &
        bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Iterator.f_skip (Core.Iter.Traits.Iterator.f_enumerate
                  (Core.Iter.Traits.Collect.f_into_iter re
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    Core.Array.Iter.t_IntoIter i32 (sz 256))
                <:
                Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Array.Iter.t_IntoIter i32 (sz 256)))
              (sz 2)
            <:
            Core.Iter.Adapters.Skip.t_Skip
            (Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Array.Iter.t_IntoIter i32 (sz 256))))
          (fun (i, coefficient) ->
              (Core.Num.impl__i32__abs coefficient <: i32) <.
              ((128l /! (1l <<! (Core.Num.impl__usize__ilog2 i <: u32) <: i32) <: i32) *!
                Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                <:
                i32)
              <:
              bool)
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: re.coefficients.into_iter().enumerate().skip(2).all(|(i, coefficient)|\\n        coefficient.abs() < (128 / (1 << i.ilog2())) * FIELD_MODULUS)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 8
            })
        <:
        Core.Ops.Range.t_Range usize)
      re
      (fun re i ->
          {
            re with
            Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            =
            Rust_primitives.Hax.update_at re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (re
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                    <:
                    i32)
                <:
                i32)
            <:
            t_Array i32 (sz 256)
          })
  in
  re

let ntt_multiply_binomials (a0, a1: (i32 & i32)) (b0, b1: (i32 & i32)) (zeta: i32) : (i32 & i32) =
  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((a0 *! b0 <: i32) +!
      ((Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a1 *! b1 <: i32) <: i32) *! zeta <: i32)
      <:
      i32),
  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((a0 *! b1 <: i32) +! (a1 *! b0 <: i32) <: i32)

let ntt_multiply (left right: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter left
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient -> (coefficient >=. 0l <: bool) && (coefficient <. 4096l <: bool))
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: left.coefficients.into_iter().all(|coefficient|\\n        coefficient >= 0 && coefficient < 4096)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter right
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (coefficient >.
                (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)
                <:
                bool) &&
              (coefficient <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: bool))
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: right.coefficients.into_iter().all(|coefficient|\\n        coefficient > -FIELD_MODULUS && coefficient < FIELD_MODULUS)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 4 <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let product:(i32 & i32) =
            ntt_multiply_binomials ((left.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 4 *! i
                    <:
                    usize ]
                  <:
                  i32),
                (left.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1
                    <:
                    usize ]
                  <:
                  i32))
              ((right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 4 *! i <: usize ] <: i32),
                (right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1
                    <:
                    usize ]
                  <:
                  i32))
              (v_ZETAS_MONTGOMERY_DOMAIN.[ sz 64 +! i <: usize ] <: i32)
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at out.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                (sz 4 *! i <: usize)
                product._1
            }
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at out.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 1 <: usize)
                product._2
            }
          in
          let product:(i32 & i32) =
            ntt_multiply_binomials ((left.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i
                      <:
                      usize) +!
                    sz 2
                    <:
                    usize ]
                  <:
                  i32),
                (left.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3
                    <:
                    usize ]
                  <:
                  i32))
              ((right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2
                    <:
                    usize ]
                  <:
                  i32),
                (right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3
                    <:
                    usize ]
                  <:
                  i32))
              (Core.Ops.Arith.Neg.neg (v_ZETAS_MONTGOMERY_DOMAIN.[ sz 64 +! i <: usize ] <: i32)
                <:
                i32)
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at out.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 2 <: usize)
                product._1
            }
          in
          let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              out with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at out.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                ((sz 4 *! i <: usize) +! sz 3 <: usize)
                product._2
            }
          in
          out)
  in
  let _:Prims.unit =
    if true
    then
      let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
        Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter out
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            Core.Array.Iter.t_IntoIter i32 (sz 256))
          (fun coefficient ->
              (coefficient >.
                (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)
                <:
                bool) &&
              (coefficient <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: bool))
      in
      let _:Prims.unit =
        if ~.out
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: out.coefficients.into_iter().all(|coefficient|\\n        coefficient > -FIELD_MODULUS && coefficient < FIELD_MODULUS)"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  out

let compute_message
      (#v_K: usize)
      (v: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
      (secret_as_ntt u_as_ntt:
          t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            ntt_multiply (secret_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              (u_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element result product
          in
          result)
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    invert_ntt_montgomery result
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize result
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                  <:
                  t_Slice i32)
              <:
              usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let coefficient_normal_form:i32 =
            Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((result
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                  <:
                  i32) *!
                1441l
                <:
                i32)
          in
          let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              result with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                i
                (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce ((v
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                        <:
                        i32) -!
                      coefficient_normal_form
                      <:
                      i32)
                  <:
                  i32)
            }
          in
          result)
  in
  result

let compute_ring_element_v
      (#v_K: usize)
      (tt_as_ntt r_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
      (error_2_ message: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            })
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            ntt_multiply (tt_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              (r_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element result product
          in
          result)
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    invert_ntt_montgomery result
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize result
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                  <:
                  t_Slice i32)
              <:
              usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let coefficient_normal_form:i32 =
            Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((result
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                  <:
                  i32) *!
                1441l
                <:
                i32)
          in
          let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            {
              result with
              Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              =
              Rust_primitives.Hax.update_at result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                i
                (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce ((coefficient_normal_form +!
                        (error_2_.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32)
                        <:
                        i32) +!
                      (message.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32)
                      <:
                      i32)
                  <:
                  i32)
            }
          in
          result)
  in
  result

let compute_vector_u
      (#v_K: usize)
      (a_as_ntt:
          t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K)
      (r_as_ntt error_1_: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize a_as_ntt
                    <:
                    t_Slice (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
                <:
                Core.Slice.Iter.t_Iter
                (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Slice.Iter.t_Iter
          (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)))
      result
      (fun result (i, row) ->
          let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                      (Core.Slice.impl__iter (Rust_primitives.unsize row
                            <:
                            t_Slice Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                        <:
                        Core.Slice.Iter.t_Iter
                        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement))
                <:
                Core.Iter.Adapters.Enumerate.t_Enumerate
                (Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement))
              result
              (fun result (j, a_element) ->
                  let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    ntt_multiply a_element
                      (r_as_ntt.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
                    Rust_primitives.Hax.update_at result
                      i
                      (Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element (result.[ i ]
                            <:
                            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                          product
                        <:
                        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  result)
          in
          let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Rust_primitives.Hax.update_at result
              i
              (invert_ntt_montgomery (result.[ i ]
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end
                    =
                    Core.Slice.impl__len (Rust_primitives.unsize (result.[ i ]
                            <:
                            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize
                  })
              <:
              Core.Ops.Range.t_Range usize)
            result
            (fun result j ->
                let coefficient_normal_form:i32 =
                  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (((result.[ i ]
                          <:
                          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]
                        <:
                        i32) *!
                      1441l
                      <:
                      i32)
                in
                let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
                  Rust_primitives.Hax.update_at result
                    i
                    ({
                        (result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) with
                        Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        =
                        Rust_primitives.Hax.update_at (result.[ i ]
                            <:
                            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                          j
                          (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (coefficient_normal_form +!
                                ((error_1_.[ i ]
                                    <:
                                    Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]
                                  <:
                                  i32)
                                <:
                                i32)
                            <:
                            i32)
                        <:
                        t_Array i32 (sz 256)
                      })
                in
                result))
  in
  result

let compute_As_plus_e
      (#v_K: usize)
      (matrix_A:
          t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K)
      (s_as_ntt error_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize matrix_A
                    <:
                    t_Slice (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
                <:
                Core.Slice.Iter.t_Iter
                (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Slice.Iter.t_Iter
          (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)))
      result
      (fun result (i, row) ->
          let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                      (Core.Slice.impl__iter (Rust_primitives.unsize row
                            <:
                            t_Slice Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                        <:
                        Core.Slice.Iter.t_Iter
                        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement))
                <:
                Core.Iter.Adapters.Enumerate.t_Enumerate
                (Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement))
              result
              (fun result (j, matrix_element) ->
                  let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                    ntt_multiply matrix_element
                      (s_as_ntt.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
                    Rust_primitives.Hax.update_at result
                      i
                      (Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element (result.[ i ]
                            <:
                            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                          product
                        <:
                        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  result)
          in
          let _:Prims.unit =
            if true
            then
              let _, out:(Core.Array.Iter.t_IntoIter i32 (sz 256) & bool) =
                Core.Iter.Traits.Iterator.f_all (Core.Iter.Traits.Collect.f_into_iter (result.[ i ]
                        <:
                        Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    <:
                    Core.Array.Iter.t_IntoIter i32 (sz 256))
                  (fun coefficient ->
                      (Core.Num.impl__i32__abs coefficient <: i32) <.
                      ((cast v_K <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32)
                      <:
                      bool)
              in
              let _:Prims.unit =
                if ~.out
                then
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: result[i].coefficients.into_iter().all(|coefficient|\\n        coefficient.abs() < (K as i32) * FIELD_MODULUS)"

                      <:
                      Rust_primitives.Hax.t_Never)
              in
              ()
          in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end
                    =
                    Core.Slice.impl__len (Rust_primitives.unsize (result.[ i ]
                            <:
                            Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize
                  })
              <:
              Core.Ops.Range.t_Range usize)
            result
            (fun result j ->
                let coefficient_normal_form:i32 =
                  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (((result.[ i ]
                          <:
                          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]
                        <:
                        i32) *!
                      1353l
                      <:
                      i32)
                in
                Rust_primitives.Hax.update_at result
                  i
                  ({
                      (result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement) with
                      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      =
                      Rust_primitives.Hax.update_at (result.[ i ]
                          <:
                          Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        j
                        (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (coefficient_normal_form +!
                              ((error_as_ntt.[ i ]
                                  <:
                                  Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
                                  .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]
                                <:
                                i32)
                              <:
                              i32)
                          <:
                          i32)
                      <:
                      t_Array i32 (sz 256)
                    })))
  in
  result