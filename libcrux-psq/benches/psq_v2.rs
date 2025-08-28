use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use libcrux_psq::protocol::{
    api::{Builder, IntoSession, Protocol},
    dhkem::DHKeyPair,
    initiator::{QueryInitiator, RegistrationInitiator},
    pqkem::PQKeyPair,
    responder::Responder,
};
use rand::CryptoRng;

pub fn randombytes(n: usize) -> Vec<u8> {
    use rand::rngs::OsRng;
    use rand::TryRngCore;

    let mut bytes = vec![0u8; n];
    OsRng.try_fill_bytes(&mut bytes).unwrap();
    bytes
}

fn query<const PQ: bool>(c: &mut Criterion) {
    let mut rng = rand::rng();
    let ciphersuite = if PQ { "x25519" } else { "x25519-mlkem768" };
    let ctx = b"Test Context";
    let aad_initiator = b"Test Data I";
    let aad_responder = b"Test Data R";

    // External setup
    let responder_ecdh_keys = DHKeyPair::new(&mut rng);
    let responder_pq_keys = PQKeyPair::new(&mut rng);

    // x25519

    // Setup initiator
    let mut initiator = query_initiator(rand::rng(), ctx, aad_initiator, &responder_ecdh_keys);
    c.bench_function(&format!("[Query] Initiator setup"), |b| {
        b.iter_batched(
            || rand::rng(),
            |rng| {
                initiator = query_initiator(rng, ctx, aad_initiator, &responder_ecdh_keys);
            },
            BatchSize::SmallInput,
        )
    });

    // Setup responder
    let mut responder = build_responder::<PQ>(
        rand::rng(),
        ctx,
        aad_responder,
        &responder_ecdh_keys,
        &responder_pq_keys,
    );
    c.bench_function(&format!("[Query] Responder setup {ciphersuite}"), |b| {
        b.iter_batched(
            || rand::rng(),
            |rng| {
                responder = build_responder::<PQ>(
                    rng,
                    ctx,
                    aad_responder,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );
            },
            BatchSize::SmallInput,
        )
    });

    // Setup for sending messages.

    // Send first message
    c.bench_function(
        &format!("[Query] Initiator send query {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let msg_channel = vec![0u8; 4096];

                    let initiator =
                        query_initiator(rand::rng(), ctx, aad_initiator, &responder_ecdh_keys);

                    (initiator, msg_channel)
                },
                |(initiator, msg_channel)| {
                    let query_payload_initiator = b"Query_init";
                    let _len_i = initiator
                        .write_message(query_payload_initiator, msg_channel)
                        .unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Read first message
    c.bench_function(
        &format!("[Query] Responder read message {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let mut msg_channel = vec![0u8; 4096];
                    let payload_buf_responder = vec![0u8; 4096];

                    let mut initiator =
                        query_initiator(rand::rng(), ctx, aad_initiator, &responder_ecdh_keys);

                    let query_payload_initiator = b"Query_init";
                    let _len_i = initiator
                        .write_message(query_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    (responder, msg_channel, payload_buf_responder)
                },
                |(responder, msg_channel, payload_buf_responder)| {
                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(msg_channel, payload_buf_responder)
                        .unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Respond
    c.bench_function(&format!("[Query] Responder respond {ciphersuite}"), |b| {
        b.iter_batched_ref(
            || {
                let mut msg_channel = vec![0u8; 4096];
                let mut payload_buf_responder = vec![0u8; 4096];

                let mut initiator =
                    query_initiator(rand::rng(), ctx, aad_initiator, &responder_ecdh_keys);

                let query_payload_initiator = b"Query_init";
                let _len_i = initiator
                    .write_message(query_payload_initiator, &mut msg_channel)
                    .unwrap();

                let mut responder = build_responder::<PQ>(
                    rand::rng(),
                    ctx,
                    aad_responder,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );

                let (_len_r_deserialized, _len_r_payload) = responder
                    .read_message(&msg_channel, &mut payload_buf_responder)
                    .unwrap();

                (responder, msg_channel)
            },
            |(responder, msg_channel)| {
                let query_payload_responder = b"Query_respond";
                let _len_r = responder
                    .write_message(query_payload_responder, msg_channel)
                    .unwrap();
            },
            BatchSize::SmallInput,
        )
    });

    // Finalize on query initiator
    c.bench_function(&format!("[Query] Finalize initiator {ciphersuite}"), |b| {
        b.iter_batched_ref(
            || {
                let mut msg_channel = vec![0u8; 4096];
                let mut payload_buf_responder = vec![0u8; 4096];
                let payload_buf_initiator = vec![0u8; 4096];

                let mut initiator =
                    query_initiator(rand::rng(), ctx, aad_initiator, &responder_ecdh_keys);

                let query_payload_initiator = b"Query_init";
                let _len_i = initiator
                    .write_message(query_payload_initiator, &mut msg_channel)
                    .unwrap();

                let mut responder = build_responder::<PQ>(
                    rand::rng(),
                    ctx,
                    aad_responder,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );

                let (_len_r_deserialized, _len_r_payload) = responder
                    .read_message(&msg_channel, &mut payload_buf_responder)
                    .unwrap();

                let query_payload_responder = b"Query_respond";
                let _len_r = responder
                    .write_message(query_payload_responder, &mut msg_channel)
                    .unwrap();

                (initiator, msg_channel, payload_buf_initiator)
            },
            |(initiator, msg_channel, payload_buf_initiator)| {
                let (_len_i_deserialized, _len_i_payload) = initiator
                    .read_message(msg_channel, payload_buf_initiator)
                    .unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

fn registration<const PQ: bool>(c: &mut Criterion) {
    let mut rng = rand::rng();
    let ciphersuite = if PQ { "x25519" } else { "x25519-mlkem768" };
    let ctx = b"Test Context";
    let aad_initiator_outer = b"Test Data I Outer";
    let aad_initiator_inner = b"Test Data I Inner";
    let aad_responder = b"Test Data R";

    // External setup
    let responder_ecdh_keys = DHKeyPair::new(&mut rng);
    let responder_pq_keys = PQKeyPair::new(&mut rng);
    let initiator_ecdh_keys = DHKeyPair::new(&mut rng);

    // x25519

    // Setup initiator
    let mut initiator = registration_initiator::<PQ>(
        rand::rng(),
        ctx,
        aad_initiator_outer,
        aad_initiator_inner,
        &responder_ecdh_keys,
        &responder_pq_keys,
        &initiator_ecdh_keys,
    );
    c.bench_function(&format!("[Registration] Initiator setup"), |b| {
        b.iter_batched(
            || rand::rng(),
            |rng| {
                initiator = registration_initiator::<PQ>(
                    rng,
                    ctx,
                    aad_initiator_outer,
                    aad_initiator_inner,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                    &initiator_ecdh_keys,
                );
            },
            BatchSize::SmallInput,
        )
    });

    // Setup responder
    let mut responder = build_responder::<PQ>(
        rand::rng(),
        ctx,
        aad_responder,
        &responder_ecdh_keys,
        &responder_pq_keys,
    );
    c.bench_function(
        &format!("[Registration] Responder setup {ciphersuite}"),
        |b| {
            b.iter_batched(
                || rand::rng(),
                |rng| {
                    responder = build_responder::<PQ>(
                        rng,
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Setup for sending messages.

    // Send first message
    c.bench_function(
        &format!("[Registration] Initiator send registration {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let msg_channel = vec![0u8; 4096];

                    let initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    (initiator, msg_channel)
                },
                |(initiator, msg_channel)| {
                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, msg_channel)
                        .unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Read first message
    c.bench_function(
        &format!("[Registration] Responder read message {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let mut msg_channel = vec![0u8; 4096];
                    let payload_buf_responder = vec![0u8; 4096];

                    let mut initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    (responder, msg_channel, payload_buf_responder)
                },
                |(responder, msg_channel, payload_buf_responder)| {
                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(msg_channel, payload_buf_responder)
                        .unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Respond
    c.bench_function(
        &format!("[Registration] Responder respond {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let mut msg_channel = vec![0u8; 4096];
                    let mut payload_buf_responder = vec![0u8; 4096];

                    let mut initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let mut responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(&msg_channel, &mut payload_buf_responder)
                        .unwrap();

                    (responder, msg_channel)
                },
                |(responder, msg_channel)| {
                    let registration_payload_responder = b"Registration_respond";
                    let _len_r = responder
                        .write_message(registration_payload_responder, msg_channel)
                        .unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Finalize on registration initiator
    c.bench_function(
        &format!("[Registration] Finalize initiator {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let mut msg_channel = vec![0u8; 4096];
                    let mut payload_buf_responder = vec![0u8; 4096];
                    let payload_buf_initiator = vec![0u8; 4096];

                    let mut initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let mut responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(&msg_channel, &mut payload_buf_responder)
                        .unwrap();

                    let registration_payload_responder = b"Registration_respond";
                    let _len_r = responder
                        .write_message(registration_payload_responder, &mut msg_channel)
                        .unwrap();

                    (initiator, msg_channel, payload_buf_initiator)
                },
                |(initiator, msg_channel, payload_buf_initiator)| {
                    let (_len_i_deserialized, _len_i_payload) = initiator
                        .read_message(msg_channel, payload_buf_initiator)
                        .unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // IntoTransport transform Initiator
    c.bench_function(
        &format!("[Registration] IntoTransport Responder {ciphersuite}"),
        |b| {
            b.iter_batched(
                || {
                    let mut msg_channel = vec![0u8; 4096];
                    let mut payload_buf_responder = vec![0u8; 4096];

                    let mut initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let mut responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(&msg_channel, &mut payload_buf_responder)
                        .unwrap();

                    let registration_payload_responder = b"Registration_respond";
                    let _len_r = responder
                        .write_message(registration_payload_responder, &mut msg_channel)
                        .unwrap();

                    responder
                },
                |responder| {
                    let _ = responder.into_session();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // IntoTransport transform Initiator
    c.bench_function(
        &format!("[Registration] IntoTransport Initiator {ciphersuite}"),
        |b| {
            b.iter_batched(
                || {
                    let mut msg_channel = vec![0u8; 4096];
                    let mut payload_buf_responder = vec![0u8; 4096];
                    let mut payload_buf_initiator = vec![0u8; 4096];

                    let mut initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let mut responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(&msg_channel, &mut payload_buf_responder)
                        .unwrap();

                    let registration_payload_responder = b"Registration_respond";
                    let _len_r = responder
                        .write_message(registration_payload_responder, &mut msg_channel)
                        .unwrap();

                    let (_len_i_deserialized, _len_i_payload) = initiator
                        .read_message(&msg_channel, &mut payload_buf_initiator)
                        .unwrap();

                    initiator
                },
                |initiator| {
                    let _ = initiator.into_session();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Transport write message
    c.bench_function(
        &format!("[Registration] Transport Write {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let mut msg_channel = vec![0u8; 5050];
                    let mut payload_buf_responder = vec![0u8; 4096];
                    let mut payload_buf_initiator = vec![0u8; 4096];

                    let mut initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let mut responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(&msg_channel, &mut payload_buf_responder)
                        .unwrap();

                    let registration_payload_responder = b"Registration_respond";
                    let _len_r = responder
                        .write_message(registration_payload_responder, &mut msg_channel)
                        .unwrap();

                    let (_len_i_deserialized, _len_i_payload) = initiator
                        .read_message(&msg_channel, &mut payload_buf_initiator)
                        .unwrap();

                    let mut initiator = initiator.into_session().unwrap();
                    let (_channel_no, channel) = initiator.channel().unwrap();
                    let payload = randombytes(4096);
                    (channel, msg_channel, payload)
                },
                |(channel, msg_channel, payload)| {
                    let _ = channel.write_message(payload, msg_channel).unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );

    // Transport read message
    c.bench_function(
        &format!("[Registration] Transport Read {ciphersuite}"),
        |b| {
            b.iter_batched_ref(
                || {
                    let mut msg_channel = vec![0u8; 5050];
                    let mut payload_buf_responder = vec![0u8; 4096];
                    let mut payload_buf_initiator = vec![0u8; 4096];

                    let mut initiator = registration_initiator::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_initiator_outer,
                        aad_initiator_inner,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                        &initiator_ecdh_keys,
                    );

                    let registration_payload_initiator = b"Registration_init";
                    let _len_i = initiator
                        .write_message(registration_payload_initiator, &mut msg_channel)
                        .unwrap();

                    let mut responder = build_responder::<PQ>(
                        rand::rng(),
                        ctx,
                        aad_responder,
                        &responder_ecdh_keys,
                        &responder_pq_keys,
                    );

                    let (_len_r_deserialized, _len_r_payload) = responder
                        .read_message(&msg_channel, &mut payload_buf_responder)
                        .unwrap();

                    let registration_payload_responder = b"Registration_respond";
                    let _len_r = responder
                        .write_message(registration_payload_responder, &mut msg_channel)
                        .unwrap();

                    let (_len_i_deserialized, _len_i_payload) = initiator
                        .read_message(&msg_channel, &mut payload_buf_initiator)
                        .unwrap();

                    let mut initiator = initiator.into_session().unwrap();

                    let (_channel_no, mut initiator_channel) = initiator.channel().unwrap();

                    let _ = initiator_channel
                        .write_message(&randombytes(4096), &mut msg_channel)
                        .unwrap();

                    let mut responder = responder.into_session().unwrap();
                    let (_channel_no, responder_channel) = responder.channel().unwrap();
                    (responder_channel, msg_channel, payload_buf_responder)
                },
                |(responder_channel, msg_channel, payload_buf_responder)| {
                    let _ = responder_channel
                        .read_message(msg_channel, payload_buf_responder)
                        .unwrap();
                },
                BatchSize::SmallInput,
            )
        },
    );
}

#[inline(always)]
fn build_responder<'a, const PQ: bool>(
    rng: impl CryptoRng,
    ctx: &'a [u8],
    aad_responder: &'a [u8],
    responder_ecdh_keys: &'a DHKeyPair,
    responder_pq_keys: &'a PQKeyPair,
) -> Responder<'a, impl CryptoRng> {
    let mut responder = Builder::new(rng)
        .context(ctx)
        .outer_aad(aad_responder)
        .longterm_ecdh_keys(responder_ecdh_keys)
        .recent_keys_upper_bound(30);
    if PQ {
        responder = responder.longterm_pq_keys(&responder_pq_keys);
    }
    responder.build_responder().unwrap()
}

#[inline(always)]
fn query_initiator<'a>(
    rng: impl CryptoRng,
    ctx: &'a [u8],
    aad_initiator: &'a [u8],
    responder_ecdh_keys: &'a DHKeyPair,
) -> QueryInitiator<'a> {
    Builder::new(rng)
        .outer_aad(aad_initiator)
        .context(ctx)
        .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk)
        .build_query_initiator()
        .unwrap()
}

#[inline(always)]
fn registration_initiator<'a, const PQ: bool>(
    rng: impl CryptoRng,
    ctx: &'a [u8],
    aad_initiator_outer: &'a [u8],
    aad_initiator_inner: &'a [u8],
    responder_ecdh_keys: &'a DHKeyPair,
    responder_pq_keys: &'a PQKeyPair,
    initiator_ecdh_keys: &'a DHKeyPair,
) -> RegistrationInitiator<'a, impl CryptoRng> {
    let mut builder = Builder::new(rng)
        .outer_aad(aad_initiator_outer)
        .outer_aad(aad_initiator_inner)
        .context(ctx)
        .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk)
        .longterm_ecdh_keys(initiator_ecdh_keys);
    if PQ {
        builder = builder.peer_longterm_pq_pk(&responder_pq_keys.pk);
    }
    builder.build_registration_initiator().unwrap()
}

pub fn protocol(c: &mut Criterion) {
    // PSQv2 query protocol
    query::<true>(c);
    query::<false>(c);
    // PSQv2 registration protocol
    registration::<true>(c);
    registration::<false>(c);
}

criterion_group!(benches, protocol);
criterion_main!(benches);
