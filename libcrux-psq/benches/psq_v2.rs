use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use libcrux_ml_kem::mlkem768::{self, MlKem768KeyPair};
use libcrux_psq::protocol::{
    api::{Builder, HandshakeState as _},
    ecdh::KEMKeyPair,
    initiator::QueryInitiator,
    responder::Responder,
};
use rand::CryptoRng;

fn query<const PQ: bool>(c: &mut Criterion) {
    let mut rng = rand::rng();
    let ciphersuite = if PQ { "x25519" } else { "x25519-mlkem768" };
    let ctx = b"Test Context";
    let aad_initiator = b"Test Data I";
    let aad_responder = b"Test Data R";

    // External setup
    let responder_ecdh_keys = KEMKeyPair::new(&mut rng);
    let responder_pq_keys = mlkem768::rand::generate_key_pair(&mut rng);

    // x25519

    // Setup initiator
    let mut initiator = query_initiator::<PQ>(
        rand::rng(),
        ctx,
        aad_initiator,
        &responder_ecdh_keys,
        &responder_pq_keys,
    );
    c.bench_function(&format!("Initiator setup {ciphersuite}"), |b| {
        b.iter_batched(
            || rand::rng(),
            |rng| {
                initiator = query_initiator::<PQ>(
                    rng,
                    ctx,
                    aad_initiator,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );
            },
            BatchSize::SmallInput,
        )
    });

    // Setup responder
    let mut responder = query_responder::<PQ>(
        rand::rng(),
        ctx,
        aad_responder,
        &responder_ecdh_keys,
        &responder_pq_keys,
    );
    c.bench_function(&format!("Responder setup {ciphersuite}"), |b| {
        b.iter_batched(
            || rand::rng(),
            |rng| {
                responder = query_responder::<PQ>(
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
    c.bench_function(&format!("Initiator send query {ciphersuite}"), |b| {
        b.iter_batched_ref(
            || {
                let msg_channel = vec![0u8; 4096];

                let initiator = query_initiator::<PQ>(
                    rand::rng(),
                    ctx,
                    aad_initiator,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );

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
    });

    // Read first message
    c.bench_function(&format!("Responder read message {ciphersuite}"), |b| {
        b.iter_batched_ref(
            || {
                let mut msg_channel = vec![0u8; 4096];
                let payload_buf_responder = vec![0u8; 4096];

                let mut initiator = query_initiator::<PQ>(
                    rand::rng(),
                    ctx,
                    aad_initiator,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );

                let query_payload_initiator = b"Query_init";
                let _len_i = initiator
                    .write_message(query_payload_initiator, &mut msg_channel)
                    .unwrap();

                let responder = query_responder::<PQ>(
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
    });

    // Respond
    c.bench_function(&format!("Responder respond {ciphersuite}"), |b| {
        b.iter_batched_ref(
            || {
                let mut msg_channel = vec![0u8; 4096];
                let mut payload_buf_responder = vec![0u8; 4096];

                let mut initiator = query_initiator::<PQ>(
                    rand::rng(),
                    ctx,
                    aad_initiator,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );

                let query_payload_initiator = b"Query_init";
                let _len_i = initiator
                    .write_message(query_payload_initiator, &mut msg_channel)
                    .unwrap();

                let mut responder = query_responder::<PQ>(
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
    c.bench_function(&format!("Finalize initiator {ciphersuite}"), |b| {
        b.iter_batched_ref(
            || {
                let mut msg_channel = vec![0u8; 4096];
                let mut payload_buf_responder = vec![0u8; 4096];
                let payload_buf_initiator = vec![0u8; 4096];

                let mut initiator = query_initiator::<PQ>(
                    rand::rng(),
                    ctx,
                    aad_initiator,
                    &responder_ecdh_keys,
                    &responder_pq_keys,
                );

                let query_payload_initiator = b"Query_init";
                let _len_i = initiator
                    .write_message(query_payload_initiator, &mut msg_channel)
                    .unwrap();

                let mut responder = query_responder::<PQ>(
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

#[inline(always)]
fn query_responder<'a, const PQ: bool>(
    rng: impl CryptoRng,
    ctx: &'a [u8],
    aad_responder: &'a [u8],
    responder_ecdh_keys: &'a KEMKeyPair,
    responder_pq_keys: &'a MlKem768KeyPair,
) -> Responder<'a, impl CryptoRng> {
    let mut responder = Builder::new(rng)
        .context(ctx)
        .outer_aad(aad_responder)
        .longterm_ecdh_keys(responder_ecdh_keys)
        .bound_recent_keys_by(30);
    if PQ {
        responder = responder.longterm_pq_keys(&responder_pq_keys);
    }
    responder.build_responder().unwrap()
}

#[inline(always)]
fn query_initiator<'a, const PQ: bool>(
    rng: impl CryptoRng,
    ctx: &'a [u8],
    aad_initiator: &'a [u8],
    responder_ecdh_keys: &'a KEMKeyPair,
    responder_pq_keys: &'a MlKem768KeyPair,
) -> QueryInitiator<'a> {
    let mut builder = Builder::new(rng)
        .outer_aad(aad_initiator)
        .context(ctx)
        .peer_longterm_ecdh_pk(&responder_ecdh_keys.pk);
    if PQ {
        builder = builder.peer_longterm_pq_pk(responder_pq_keys.public_key());
    }
    builder.build_query_initiator().unwrap()
}

pub fn protocol(c: &mut Criterion) {
    // PSQv2 query protocol
    query::<true>(c);
    query::<false>(c);
    // registration(c);
}

criterion_group!(benches, protocol);
criterion_main!(benches);
