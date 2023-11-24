module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

let ntt_multiply_binomials (a0, a1: (i32 & i32)) (b0, b1: (i32 & i32)) (zeta: i32)
    : FStar.HyperStack.ST.St (i32 & i32) =
  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((a0 *! b0 <: i32) +!
      ((Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce (a1 *! b1 <: i32) <: i32) *! zeta <: i32)
      <:
      i32),
  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((a0 *! b1 <: i32) +! (a1 *! b0 <: i32) <: i32)
  <:
  (i32 & i32)

let invert_ntt_montgomery
      (v_K: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 2 in
  let step:usize = sz 1 <<! 1l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Sub::sub(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let a_minus_b: int = {\n                                            core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step))))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(a_minus_b,core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i))))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let step:usize = sz 1 <<! 2l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Sub::sub(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let a_minus_b: int = {\n                                            core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step))))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(a_minus_b,core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i))))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let step:usize = sz 1 <<! 3l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Sub::sub(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let a_minus_b: int = {\n                                            core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step))))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(a_minus_b,core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i))))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let step:usize = sz 1 <<! 4l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Sub::sub(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let a_minus_b: int = {\n                                            core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step))))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(a_minus_b,core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i))))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let step:usize = sz 1 <<! 5l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Sub::sub(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let a_minus_b: int = {\n                                            core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step))))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(a_minus_b,core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i))))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let step:usize = sz 1 <<! 6l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Sub::sub(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let a_minus_b: int = {\n                                            core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step))))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(a_minus_b,core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i))))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let step:usize = sz 1 <<! 7l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Sub::sub(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let a_minus_b: int = {\n                                            core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step))))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(a_minus_b,core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i))))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (sz 8)
      (fun i ->
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize re
              .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            i
            (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (re
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                  <:
                  i32)
              <:
              i32)
          <:
          Prims.unit)
  in
  re

let ntt_binomially_sampled_ring_element
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = sz 0 in
  let zeta_i:usize = zeta_i +! sz 1 in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (sz 128)
      (fun j ->
          let j:usize = j in
          let t:i32 =
            (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j +! sz 128 <: usize ] <: i32) *!
            (-1600l)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              (j +! sz 128 <: usize)
              ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) -! t <: i32)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize re
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              j
              ((re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32) +! t <: i32)
          in
          ())
  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 6l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 5l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 4l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 3l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 2l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 1l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map (sz 256)
        re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
        Libcrux.Kem.Kyber.Arithmetic.barrett_reduce
    }
    <:
    Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  in
  re

let ntt_multiply (left right: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! sz 4 <: usize)
      (fun i ->
          let i:usize = i in
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
                  i32)
                <:
                (i32 & i32))
              ((right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ sz 4 *! i <: usize ] <: i32),
                (right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 1
                    <:
                    usize ]
                  <:
                  i32)
                <:
                (i32 & i32))
              (v_ZETAS_MONTGOMERY_DOMAIN.[ sz 64 +! i <: usize ] <: i32)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              (sz 4 *! i <: usize)
              product._1
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              ((sz 4 *! i <: usize) +! sz 1 <: usize)
              product._2
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
                  i32)
                <:
                (i32 & i32))
              ((right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 2
                    <:
                    usize ]
                  <:
                  i32),
                (right.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ (sz 4 *! i <: usize) +! sz 3
                    <:
                    usize ]
                  <:
                  i32)
                <:
                (i32 & i32))
              (Core.Ops.Arith.Neg.neg (v_ZETAS_MONTGOMERY_DOMAIN.[ sz 64 +! i <: usize ] <: i32)
                <:
                i32)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              ((sz 4 *! i <: usize) +! sz 2 <: usize)
              product._1
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              ((sz 4 *! i <: usize) +! sz 3 <: usize)
              product._2
          in
          ())
  in
  let _:Prims.unit = () <: Prims.unit in
  out

let compute_As_plus_e
      (v_K: usize)
      (matrix_A:
          t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K)
      (s_as_ntt error_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nLoop without mutation?HERE\n"
      "{\n        for Tuple2(i, row) in (core::iter::traits::collect::f_into_iter::<\n            core::iter::adapters::enumerate::t_Enumerate<\n                core::slice::iter::t_Iter<\n                    [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n                >,\n            >,\n        >(core::iter::traits::iterator::f_enumerate::<\n            core::slice::iter::t_Iter<\n                [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n            >,\n        >(core::slice::impl__iter::<\n            [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n        >(rust_primitives::unsize(matrix_A)))))\n        {\n            {\n                let _: tuple0 = {\n                    {\n                        for Tuple2(j, matrix_element) in (core::iter::traits::collect::f_into_iter::<\n                            core::iter::adapters::enumerate::t_Enumerate<\n                                core::slice::iter::t_Iter<\n                                    libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                                >,\n                            >,\n                        >(\n                            core::iter::traits::iterator::f_enumerate::<\n                                core::slice::iter::t_Iter<\n                                    libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                                >,\n                            >(core::slice::impl__iter::<\n                                libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                            >(\n                                rust_primitives::unsize(row)\n                            )),\n                        )) {\n                            {\n                                let product: libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement = {libcrux::kem::kyber::ntt::ntt_multiply(matrix_element,core::ops::index::Index::index(s_as_ntt,j))};\n                                {\n                                    let _: tuple0 = {\n                                        libcrux::kem::kyber::arithmetic::add_to_ring_element::<\n                                            generic_value!(todo),\n                                        >(\n                                            core::ops::index::Index::index(result, i), product\n                                        )\n                                    };\n                                    Tuple0\n                                }\n                            }\n                        }\n                    }\n                };\n                {\n                    for j in (0)..(core::slice::impl__len::<int>(rust_primitives::unsize(\n                        proj_libcrux::kem::kyber::arithmetic::f_coefficients(\n                            core::ops::index::Index::index(result, i),\n                        ),\n                    ))) {\n                        {\n                            let coefficient_normal_form: int = {\n                                libcrux::kem::kyber::arithmetic::montgomery_reduce(\n                                    core::ops::arith::Mul::mul(\n                                        core::ops::index::Index::index(\n                                            proj_libcrux::kem::kyber::arithmetic::f_coefficients(\n                                                core::ops::index::Index::index(result, i),\n                                            ),\n                                            j,\n                                        ),\n                                        1353,\n                                    ),\n                                )\n                            };\n                            rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                                proj_libcrux::kem::kyber::arithmetic::f_coefficients(\n                                    core::ops::index::Index::index(result, i),\n                                ),\n                                j,\n                                libcrux::kem::kyber::arithmetic::barrett_reduce(\n                                    core::ops::arith::Add::add(\n                                        coefficient_normal_form,\n                                        core::ops::index::Index::index(\n                                            proj_libcrux::kem::kyber::arithmetic::f_coefficients(\n                                                core::ops::index::Index::index(error_as_ntt, i),\n                                            ),\n                                            j,\n                                        ),\n                                    ),\n                                ),\n                            )\n                        }\n                    }\n                }\n            }\n        }\n    }"

  in
  result

let compute_message
      (v_K: usize)
      (v: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
      (secret_as_ntt u_as_ntt:
          t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            ntt_multiply (secret_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              (u_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          let _:Prims.unit = Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K result product in
          ())
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    invert_ntt_montgomery v_K result
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (Core.Slice.impl__len (Rust_primitives.unsize result
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            t_Slice i32)
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let coefficient_normal_form:i32 =
            Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((result
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                  <:
                  i32) *!
                1441l
                <:
                i32)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize result
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
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
          in
          ())
  in
  result

let compute_ring_element_v
      (v_K: usize)
      (tt_as_ntt r_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
      (error_2_ message: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          let product:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
            ntt_multiply (tt_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
              (r_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
          in
          let _:Prims.unit = Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K result product in
          ())
  in
  let result:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    invert_ntt_montgomery v_K result
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (Core.Slice.impl__len (Rust_primitives.unsize result
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
            <:
            t_Slice i32)
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let coefficient_normal_form:i32 =
            Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((result
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                  <:
                  i32) *!
                1441l
                <:
                i32)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize result
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
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
          in
          ())
  in
  result

let compute_vector_u
      (v_K: usize)
      (a_as_ntt:
          t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) v_K)
      (r_as_ntt error_1_: t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K) =
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
      v_K
  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nLoop without mutation?HERE\n"
      "{\n        for Tuple2(i, row) in (core::iter::traits::collect::f_into_iter::<\n            core::iter::adapters::enumerate::t_Enumerate<\n                core::slice::iter::t_Iter<\n                    [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n                >,\n            >,\n        >(core::iter::traits::iterator::f_enumerate::<\n            core::slice::iter::t_Iter<\n                [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n            >,\n        >(core::slice::impl__iter::<\n            [libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement; K],\n        >(rust_primitives::unsize(a_as_ntt)))))\n        {\n            {\n                let _: tuple0 = {\n                    {\n                        for Tuple2(j, a_element) in (core::iter::traits::collect::f_into_iter::<\n                            core::iter::adapters::enumerate::t_Enumerate<\n                                core::slice::iter::t_Iter<\n                                    libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                                >,\n                            >,\n                        >(\n                            core::iter::traits::iterator::f_enumerate::<\n                                core::slice::iter::t_Iter<\n                                    libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                                >,\n                            >(core::slice::impl__iter::<\n                                libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                            >(\n                                rust_primitives::unsize(row)\n                            )),\n                        )) {\n                            {\n                                let product: libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement = {libcrux::kem::kyber::ntt::ntt_multiply(a_element,core::ops::index::Index::index(r_as_ntt,j))};\n                                {\n                                    let _: tuple0 = {\n                                        libcrux::kem::kyber::arithmetic::add_to_ring_element::<\n                                            generic_value!(todo),\n                                        >(\n                                            core::ops::index::Index::index(result, i), product\n                                        )\n                                    };\n                                    Tuple0\n                                }\n                            }\n                        }\n                    }\n                };\n                {\n                    let _: tuple0 = {\n                        rust_primitives::hax::monomorphized_update_at::update_array_at_usize(\n                            result,\n                            i,\n                            libcrux::kem::kyber::ntt::invert_ntt_montgomery::<generic_value!(todo)>(\n                                core::clone::f_clone::<\n                                    libcrux::kem::kyber::arithmetic::t_KyberPolynomialRingElement,\n                                >(core::ops::index::Index::index(\n                                    result, i,\n                                )),\n                            ),\n                        )\n                    };\n                    {\n                        for j in (0)..(core::slice::impl__len::<int>(rust_primitives::unsize(\n                            proj_libcrux::kem::kyber::arithmetic::f_coefficients(\n                                core::ops::index::Index::index(result, i),\n                            ),\n                        ))) {\n                            {\n                                let coefficient_normal_form: int = {\n                                    libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(core::ops::index::Index::index(result,i)),j),1441))\n                                };\n                                {\n                                    let _: tuple0 = {\n                                        rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(core::ops::index::Index::index(result,i)),j,libcrux::kem::kyber::arithmetic::barrett_reduce(core::ops::arith::Add::add(coefficient_normal_form,core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(core::ops::index::Index::index(error_1,i)),j))))\n                                    };\n                                    Tuple0\n                                }\n                            }\n                        }\n                    }\n                }\n            }\n        }\n    }"

  in
  result

let ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  let zeta_i:usize = sz 0 in
  let step:usize = sz 1 <<! 7l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 6l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 5l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 4l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 3l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 2l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let step:usize = sz 1 <<! 1l in
  let zeta_i:usize =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nOnly for loop are being functionalized for now\n"
      "{\n        (for round in (0)..(core::ops::arith::Div::div(128, step)) {\n            |zeta_i| {\n                let zeta_i: int = { core::ops::arith::Add::add(zeta_i, 1) };\n                {\n                    let offset: int =\n                        { core::ops::arith::Mul::mul(core::ops::arith::Mul::mul(round, step), 2) };\n                    {\n                        let Tuple0: tuple0 = {\n                            {\n                                for j in (offset)..(core::ops::arith::Add::add(offset, step)) {\n                                    {\n                                        let t: int = {\n                                            libcrux::kem::kyber::arithmetic::montgomery_reduce(core::ops::arith::Mul::mul(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step)),core::ops::index::Index::index(libcrux::kem::kyber::ntt::v_ZETAS_MONTGOMERY_DOMAIN,zeta_i)))\n                                        };\n                                        {\n                                            let _: tuple0 = {\n                                                rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),core::ops::arith::Add::add(j,step),core::ops::arith::Sub::sub(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                            };\n                                            {\n                                                let _: tuple0 = {\n                                                    rust_primitives::hax::monomorphized_update_at::update_array_at_usize(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j,core::ops::arith::Add::add(core::ops::index::Index::index(proj_libcrux::kem::kyber::arithmetic::f_coefficients(re),j),t))\n                                                };\n                                                Tuple0\n                                            }\n                                        }\n                                    }\n                                }\n                            }\n                        };\n                        zeta_i\n                    }\n                }\n            }\n        })(zeta_i)\n    }"

  in
  let _:Prims.unit = () <: Prims.unit in
  let re:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map (sz 256)
        re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
        Libcrux.Kem.Kyber.Arithmetic.barrett_reduce
    }
    <:
    Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  in
  re
