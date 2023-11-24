channel c.

fn encapsulate<impl CryptoRng + Rng>(
  pk : t_PublicKey, rng : impl CryptoRng + Rng
){
  rust_primitives::hax::control_flow_monad::mexception::run(
    rust_primitives::hax::failure(
      "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Monadic_binding] have been found in the AST" }
",
      "{
        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>
        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]
        let Tuple2(rng, hax_temp_output): tuple2<
            impl CryptoRng + Rng,
            core::result::t_Result<
                tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>,
                libcrux::kem::t_Error,
            >,
        > = {
            (match pk {
                libcrux::kem::PublicKey_X25519(pk) => {
                    {
                        let Tuple2(tmp0, out): tuple2<
                            impl CryptoRng + Rng,
                            core::result::t_Result<
                                tuple2<
                                    libcrux::ecdh::x25519::t_PrivateKey,
                                    libcrux::ecdh::x25519::t_PublicKey,
                                >,
                                libcrux::ecdh::t_Error,
                            >,
                        > = { libcrux::ecdh::x25519::key_gen::<impl CryptoRng + Rng>(rng) };
                        {
                            let rng: impl CryptoRng + Rng = { tmp0 };
                            {
                                let hoist2: core::result::t_Result<
                                    tuple2<
                                        libcrux::ecdh::x25519::t_PrivateKey,
                                        libcrux::ecdh::x25519::t_PublicKey,
                                    >,
                                    libcrux::ecdh::t_Error,
                                > = { out };
                                {
                                    let hoist3: core::ops::control_flow::t_ControlFlow<
                                        core::result::t_Result<
                                            core::convert::t_Infallible,
                                            libcrux::ecdh::t_Error,
                                        >,
                                        tuple2<
                                            libcrux::ecdh::x25519::t_PrivateKey,
                                            libcrux::ecdh::x25519::t_PublicKey,
                                        >,
                                    > = {
                                        core::ops::try_trait::f_branch::<
                                            core::result::t_Result<
                                                tuple2<
                                                    libcrux::ecdh::x25519::t_PrivateKey,
                                                    libcrux::ecdh::x25519::t_PublicKey,
                                                >,
                                                libcrux::ecdh::t_Error,
                                            >,
                                        >(hoist2)
                                    };
                                    {
                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, tuple2<libcrux::ecdh::x25519::t_PrivateKey, libcrux::ecdh::x25519::t_PublicKey>>
                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let Tuple2(new_sk, new_pk): tuple2<libcrux::ecdh::x25519::t_PrivateKey, libcrux::ecdh::x25519::t_PublicKey> = {(match hoist3 {core::ops::control_flow::ControlFlow_Break(residual) => {{// Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
#[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist1: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::ecdh::t_Error>>(residual)))};core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist1))}},core::ops::control_flow::ControlFlow_Continue(val) => {core::ops::control_flow::ControlFlow_Continue(val)}})};
                                        {
                                            // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, libcrux::ecdh::x25519::t_PublicKey>
                                            #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let gxy: libcrux::ecdh::x25519::t_PublicKey = {(match core::ops::try_trait::f_branch::<core::result::t_Result<libcrux::ecdh::x25519::t_PublicKey, libcrux::ecdh::t_Error>>(libcrux::ecdh::x25519::derive(pk,new_sk)) {core::ops::control_flow::ControlFlow_Break(residual) => {{// Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
#[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist4: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::ecdh::t_Error>>(residual)))};core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist4))}},core::ops::control_flow::ControlFlow_Continue(val) => {core::ops::control_flow::ControlFlow_Continue(val)}})};
                                            core::ops::control_flow::ControlFlow_Continue(Tuple2(
                                                rng,
                                                core::result::Result_Ok(Tuple2(
                                                    libcrux::kem::Ss_X25519(gxy),
                                                    libcrux::kem::Ct_X25519(new_pk),
                                                )),
                                            ))
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                libcrux::kem::PublicKey_P256(pk) => {
                    {
                        let Tuple2(tmp0, out): tuple2<
                            impl CryptoRng + Rng,
                            core::result::t_Result<
                                tuple2<
                                    libcrux::ecdh::p256::t_PrivateKey,
                                    libcrux::ecdh::p256::t_PublicKey,
                                >,
                                libcrux::ecdh::t_Error,
                            >,
                        > = { libcrux::ecdh::p256::key_gen::<impl CryptoRng + Rng>(rng) };
                        {
                            let rng: impl CryptoRng + Rng = { tmp0 };
                            {
                                let hoist6: core::result::t_Result<
                                    tuple2<
                                        libcrux::ecdh::p256::t_PrivateKey,
                                        libcrux::ecdh::p256::t_PublicKey,
                                    >,
                                    libcrux::ecdh::t_Error,
                                > = { out };
                                {
                                    let hoist7: core::ops::control_flow::t_ControlFlow<
                                        core::result::t_Result<
                                            core::convert::t_Infallible,
                                            libcrux::ecdh::t_Error,
                                        >,
                                        tuple2<
                                            libcrux::ecdh::p256::t_PrivateKey,
                                            libcrux::ecdh::p256::t_PublicKey,
                                        >,
                                    > = {
                                        core::ops::try_trait::f_branch::<
                                            core::result::t_Result<
                                                tuple2<
                                                    libcrux::ecdh::p256::t_PrivateKey,
                                                    libcrux::ecdh::p256::t_PublicKey,
                                                >,
                                                libcrux::ecdh::t_Error,
                                            >,
                                        >(hoist6)
                                    };
                                    {
                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, tuple2<libcrux::ecdh::p256::t_PrivateKey, libcrux::ecdh::p256::t_PublicKey>>
                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let Tuple2(new_sk, new_pk): tuple2<libcrux::ecdh::p256::t_PrivateKey, libcrux::ecdh::p256::t_PublicKey> = {(match hoist7 {core::ops::control_flow::ControlFlow_Break(residual) => {{// Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
#[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist5: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::ecdh::t_Error>>(residual)))};core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist5))}},core::ops::control_flow::ControlFlow_Continue(val) => {core::ops::control_flow::ControlFlow_Continue(val)}})};
                                        {
                                            // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, libcrux::ecdh::p256::t_PublicKey>
                                            #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let gxy: libcrux::ecdh::p256::t_PublicKey = {(match core::ops::try_trait::f_branch::<core::result::t_Result<libcrux::ecdh::p256::t_PublicKey, libcrux::ecdh::t_Error>>(libcrux::ecdh::p256_derive(pk,new_sk)) {core::ops::control_flow::ControlFlow_Break(residual) => {{// Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
#[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist8: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::ecdh::t_Error>>(residual)))};core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist8))}},core::ops::control_flow::ControlFlow_Continue(val) => {core::ops::control_flow::ControlFlow_Continue(val)}})};
                                            core::ops::control_flow::ControlFlow_Continue(Tuple2(
                                                rng,
                                                core::result::Result_Ok(Tuple2(
                                                    libcrux::kem::Ss_P256(gxy),
                                                    libcrux::kem::Ct_P256(new_pk),
                                                )),
                                            ))
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                libcrux::kem::PublicKey_Kyber512(pk) => {
                    {
                        let Tuple2(tmp0, out): tuple2<
                            impl CryptoRng + Rng,
                            core::result::t_Result<[int; 32], libcrux::kem::t_Error>,
                        > = { libcrux::kem::kyber_rand::<impl CryptoRng + Rng>(rng) };
                        {
                            let rng: impl CryptoRng + Rng = { tmp0 };
                            {
                                let hoist10: core::result::t_Result<
                                    [int; 32],
                                    libcrux::kem::t_Error,
                                > = { out };
                                {
                                    let hoist11: core::ops::control_flow::t_ControlFlow<
                                        core::result::t_Result<
                                            core::convert::t_Infallible,
                                            libcrux::kem::t_Error,
                                        >,
                                        [int; 32],
                                    > = {
                                        core::ops::try_trait::f_branch::<
                                            core::result::t_Result<
                                                [int; 32],
                                                libcrux::kem::t_Error,
                                            >,
                                        >(hoist10)
                                    };
                                    {
                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, [int;32]>
                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]
                                        let seed: [int;
                                            32] = {
                                            (match hoist11 {
                                                core::ops::control_flow::ControlFlow_Break(
                                                    residual,
                                                ) => {
                                                    {
                                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
                                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist9: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::kem::t_Error>>(residual)))};
                                                        core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist9))
                                                    }
                                                }
                                                core::ops::control_flow::ControlFlow_Continue(
                                                    val,
                                                ) => core::ops::control_flow::ControlFlow_Continue(
                                                    val,
                                                ),
                                            })
                                        };
                                        core::ops::control_flow::ControlFlow_Continue(
                                            (match libcrux::kem::kyber::kyber512::encapsulate_512_(
                                                pk, seed,
                                            ) {
                                                core::result::Result_Ok(Tuple2(ct, ss)) => Tuple2(
                                                    rng,
                                                    core::result::Result_Ok(Tuple2(
                                                        libcrux::kem::Ss_Kyber512(ss),
                                                        libcrux::kem::Ct_Kyber512(ct),
                                                    )),
                                                ),
                                                _ => Tuple2(
                                                    rng,
                                                    core::result::Result_Err(
                                                        libcrux::kem::Error_Encapsulate(),
                                                    ),
                                                ),
                                            }),
                                        )
                                    }
                                }
                            }
                        }
                    }
                }
                libcrux::kem::PublicKey_Kyber768(pk) => {
                    {
                        let Tuple2(tmp0, out): tuple2<
                            impl CryptoRng + Rng,
                            core::result::t_Result<[int; 32], libcrux::kem::t_Error>,
                        > = { libcrux::kem::kyber_rand::<impl CryptoRng + Rng>(rng) };
                        {
                            let rng: impl CryptoRng + Rng = { tmp0 };
                            {
                                let hoist13: core::result::t_Result<
                                    [int; 32],
                                    libcrux::kem::t_Error,
                                > = { out };
                                {
                                    let hoist14: core::ops::control_flow::t_ControlFlow<
                                        core::result::t_Result<
                                            core::convert::t_Infallible,
                                            libcrux::kem::t_Error,
                                        >,
                                        [int; 32],
                                    > = {
                                        core::ops::try_trait::f_branch::<
                                            core::result::t_Result<
                                                [int; 32],
                                                libcrux::kem::t_Error,
                                            >,
                                        >(hoist13)
                                    };
                                    {
                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, [int;32]>
                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]
                                        let seed: [int;
                                            32] = {
                                            (match hoist14 {
                                                core::ops::control_flow::ControlFlow_Break(
                                                    residual,
                                                ) => {
                                                    {
                                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
                                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist12: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::kem::t_Error>>(residual)))};
                                                        core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist12))
                                                    }
                                                }
                                                core::ops::control_flow::ControlFlow_Continue(
                                                    val,
                                                ) => core::ops::control_flow::ControlFlow_Continue(
                                                    val,
                                                ),
                                            })
                                        };
                                        core::ops::control_flow::ControlFlow_Continue(
                                            (match libcrux::kem::kyber::kyber768::encapsulate_768_(
                                                pk, seed,
                                            ) {
                                                core::result::Result_Ok(Tuple2(ct, ss)) => Tuple2(
                                                    rng,
                                                    core::result::Result_Ok(Tuple2(
                                                        libcrux::kem::Ss_Kyber768(ss),
                                                        libcrux::kem::Ct_Kyber768(ct),
                                                    )),
                                                ),
                                                _ => Tuple2(
                                                    rng,
                                                    core::result::Result_Err(
                                                        libcrux::kem::Error_Encapsulate(),
                                                    ),
                                                ),
                                            }),
                                        )
                                    }
                                }
                            }
                        }
                    }
                }
                libcrux::kem::PublicKey_Kyber768X25519(libcrux::kem::Kyber768X25519PublicKey {
                    f_kyber: kpk,
                    f_x25519: xpk,
                }) => {
                    {
                        let Tuple2(tmp0, out): tuple2<
                            impl CryptoRng + Rng,
                            core::result::t_Result<[int; 32], libcrux::kem::t_Error>,
                        > = { libcrux::kem::kyber_rand::<impl CryptoRng + Rng>(rng) };
                        {
                            let rng: impl CryptoRng + Rng = { tmp0 };
                            {
                                let hoist16: core::result::t_Result<
                                    [int; 32],
                                    libcrux::kem::t_Error,
                                > = { out };
                                {
                                    let hoist17: core::ops::control_flow::t_ControlFlow<
                                        core::result::t_Result<
                                            core::convert::t_Infallible,
                                            libcrux::kem::t_Error,
                                        >,
                                        [int; 32],
                                    > = {
                                        core::ops::try_trait::f_branch::<
                                            core::result::t_Result<
                                                [int; 32],
                                                libcrux::kem::t_Error,
                                            >,
                                        >(hoist16)
                                    };
                                    {
                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, [int;32]>
                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]
                                        let seed: [int;
                                            32] = {
                                            (match hoist17 {
                                                core::ops::control_flow::ControlFlow_Break(
                                                    residual,
                                                ) => {
                                                    {
                                                        // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
                                                        #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist15: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::kem::t_Error>>(residual)))};
                                                        core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist15))
                                                    }
                                                }
                                                core::ops::control_flow::ControlFlow_Continue(
                                                    val,
                                                ) => core::ops::control_flow::ControlFlow_Continue(
                                                    val,
                                                ),
                                            })
                                        };
                                        {
                                            // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, tuple2<libcrux::kem::kyber::types::t_KyberCiphertext<generic_value!(todo)>, [int;32]>>
                                            #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let Tuple2(kyber_ct, kyber_ss): tuple2<libcrux::kem::kyber::types::t_KyberCiphertext<generic_value!(todo)>, [int;32]> = {(match core::ops::try_trait::f_branch::<core::result::t_Result<tuple2<libcrux::kem::kyber::types::t_KyberCiphertext<generic_value!(todo)>, [int;32]>, libcrux::kem::t_Error>>(core::result::impl__map_err::<tuple2<libcrux::kem::kyber::types::t_KyberCiphertext<generic_value!(todo)>, [int;32]>,libcrux::kem::kyber::types::t_Error,libcrux::kem::t_Error,arrow!(libcrux::kem::kyber::types::t_Error -> libcrux::kem::t_Error)>(libcrux::kem::kyber::kyber768::encapsulate_768_(kpk,seed),(|_| {libcrux::kem::Error_Encapsulate()}))) {core::ops::control_flow::ControlFlow_Break(residual) => {{// Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
#[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist18: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::kem::t_Error>>(residual)))};core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist18))}},core::ops::control_flow::ControlFlow_Continue(val) => {core::ops::control_flow::ControlFlow_Continue(val)}})};
                                            {
                                                let Tuple2(tmp0, out): tuple2<
                                                    impl CryptoRng + Rng,
                                                    core::result::t_Result<
                                                        tuple2<
                                                            libcrux::ecdh::x25519::t_PrivateKey,
                                                            libcrux::ecdh::x25519::t_PublicKey,
                                                        >,
                                                        libcrux::ecdh::t_Error,
                                                    >,
                                                > = {
                                                    libcrux::ecdh::x25519::key_gen::<
                                                        impl CryptoRng + Rng,
                                                    >(
                                                        rng
                                                    )
                                                };
                                                {
                                                    let rng: impl CryptoRng + Rng = { tmp0 };
                                                    {
                                                        let hoist20: core::result::t_Result<
                                                            tuple2<
                                                                libcrux::ecdh::x25519::t_PrivateKey,
                                                                libcrux::ecdh::x25519::t_PublicKey,
                                                            >,
                                                            libcrux::ecdh::t_Error,
                                                        > = { out };
                                                        {
                                                            let hoist21: core::ops::control_flow::t_ControlFlow<core::result::t_Result<core::convert::t_Infallible, libcrux::ecdh::t_Error>, tuple2<libcrux::ecdh::x25519::t_PrivateKey, libcrux::ecdh::x25519::t_PublicKey>> = {core::ops::try_trait::f_branch::<core::result::t_Result<tuple2<libcrux::ecdh::x25519::t_PrivateKey, libcrux::ecdh::x25519::t_PublicKey>, libcrux::ecdh::t_Error>>(hoist20)};
                                                            {
                                                                // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, tuple2<libcrux::ecdh::x25519::t_PrivateKey, libcrux::ecdh::x25519::t_PublicKey>>
                                                                #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let Tuple2(x_sk, x_pk): tuple2<libcrux::ecdh::x25519::t_PrivateKey, libcrux::ecdh::x25519::t_PublicKey> = {(match hoist21 {core::ops::control_flow::ControlFlow_Break(residual) => {{// Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
#[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist19: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::ecdh::t_Error>>(residual)))};core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist19))}},core::ops::control_flow::ControlFlow_Continue(val) => {core::ops::control_flow::ControlFlow_Continue(val)}})};
                                                                {
                                                                    // Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, libcrux::ecdh::x25519::t_PublicKey>
                                                                    #[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let x_ss: libcrux::ecdh::x25519::t_PublicKey = {(match core::ops::try_trait::f_branch::<core::result::t_Result<libcrux::ecdh::x25519::t_PublicKey, libcrux::ecdh::t_Error>>(libcrux::ecdh::x25519::derive(xpk,x_sk)) {core::ops::control_flow::ControlFlow_Break(residual) => {{// Note: rhs.typ=core::ops::control_flow::t_ControlFlow<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>, rust_primitives::hax::t_Never>
#[monadic_let(MException<tuple2<impl CryptoRng + Rng, core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>>>)]let hoist22: rust_primitives::hax::t_Never = {core::ops::control_flow::ControlFlow::v_Break(Tuple2(rng,core::ops::try_trait::f_from_residual::<core::result::t_Result<tuple2<libcrux::kem::t_Ss, libcrux::kem::t_Ct>, libcrux::kem::t_Error>,core::result::t_Result<core::convert::t_Infallible, libcrux::ecdh::t_Error>>(residual)))};core::ops::control_flow::ControlFlow_Continue(rust_primitives::hax::never_to_any(hoist22))}},core::ops::control_flow::ControlFlow_Continue(val) => {core::ops::control_flow::ControlFlow_Continue(val)}})};
                                                                    core::ops::control_flow::ControlFlow_Continue(Tuple2(rng,core::result::Result_Ok(Tuple2(libcrux::kem::Ss_Kyber768X25519(kyber_ss,x_ss),libcrux::kem::Ct_Kyber768X25519(kyber_ct,x_pk)))))
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                _ => core::ops::control_flow::ControlFlow_Continue(Tuple2(
                    rng,
                    core::result::Result_Err(libcrux::kem::Error_UnsupportedAlgorithm()),
                )),
            })
        };
        core::ops::control_flow::ControlFlow_Continue(Tuple2(rng, hax_temp_output))
    }"
    )
  )
}

fn encapsulate<const v_K : usize,const v_CIPHERTEXT_SIZE : usize,const v_PUBLIC_KEY_SIZE : usize,const v_T_AS_NTT_ENCODED_SIZE : usize,const v_C1_SIZE : usize,const v_C2_SIZE : usize,const v_VECTOR_U_COMPRESSION_FACTOR : usize,const v_VECTOR_V_COMPRESSION_FACTOR : usize,const v_VECTOR_U_BLOCK_LEN : usize,const v_ETA1 : usize,const v_ETA1_RANDOMNESS_SIZE : usize,const v_ETA2 : usize,const v_ETA2_RANDOMNESS_SIZE : usize>(
  public_key : libcrux::kem::kyber::types::t_KyberPublicKey<v_PUBLIC_KEY_SIZE>,
  randomness : [u8
  ;
  32]
){
  let
  to_hash:[u8 ; 64]
  =

    rust_primitives::hax::failure(
      "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Slice] have been found in the AST" }
",
      "libcrux::kem::kyber::conversions::into_padded_array"
    )(
      rust_primitives::hax::failure(
        "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Slice] have been found in the AST" }
",
        "rust_primitives::unsize(randomness)"
      )
    )
  ;
  let
  to_hash
  =

    rust_primitives::hax::failure(
      "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Slice] have been found in the AST" }
",
      "rust_primitives::hax::update_at"
    )(
      to_hash,
      core::ops::range::RangeFrom (
        core::ops::range::f_start,:
          libcrux::kem::kyber::constants::v_H_DIGEST_SIZE

      ),
      rust_primitives::hax::failure(
        "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Slice] have been found in the AST" }
",
        "core::slice::impl__copy_from_slice::<int>(
        core::ops::index::Index::index(
            to_hash,
            core::ops::range::RangeFrom {
                f_start: libcrux::kem::kyber::constants::v_H_DIGEST_SIZE,
            },
        ),
        rust_primitives::unsize(libcrux::kem::kyber::hash_functions::v_H(
            rust_primitives::unsize(libcrux::kem::kyber::types::impl_24__as_slice::<
                generic_value!(todo),
            >(public_key)),
        )),
    )"
      )
    )
  ;
  let
  hashed
  =

    rust_primitives::hax::failure(
      "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Slice] have been found in the AST" }
",
      "libcrux::kem::kyber::hash_functions::v_G"
    )(
      rust_primitives::hax::failure(
        "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Slice] have been found in the AST" }
",
        "rust_primitives::unsize(to_hash)"
      )
    )
  ;
  rust_primitives::hax::failure(
    "(reject_not_in_ProVerif) ExplicitRejection { reason: "a node of kind [Slice] have been found in the AST" }
",
    "{
        let Tuple2(shared_secret, pseudorandomness): tuple2<[int], [int]> = {
            core::slice::impl__split_at::<int>(
                rust_primitives::unsize(hashed),
                libcrux::kem::kyber::constants::v_SHARED_SECRET_SIZE,
            )
        };
        {
            let Tuple2(ciphertext, sampling_a_error): tuple2<
                libcrux::kem::kyber::types::t_KyberCiphertext<generic_value!(todo)>,
                core::option::t_Option<libcrux::kem::kyber::types::t_Error>,
            > = {
                libcrux::kem::kyber::ind_cpa::encrypt::<
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                    generic_value!(todo),
                >(
                    rust_primitives::unsize(libcrux::kem::kyber::types::impl_24__as_slice::<
                        generic_value!(todo),
                    >(public_key)),
                    randomness,
                    pseudorandomness,
                )
            };
            (match sampling_a_error {
                core::option::Option_Some(e) => core::result::Result_Err(e),
                core::option::Option_None => core::result::Result_Ok(Tuple2(
                    ciphertext,
                    core::result::impl__unwrap::<[int; 32], core::array::t_TryFromSliceError>(
                        core::convert::f_try_into::<[int], [int; 32]>(shared_secret),
                    ),
                )),
            })
        }
    }"
  )
}

process
    0
