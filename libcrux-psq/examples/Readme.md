# PSQ Generator Example

The example `psq.rs` implements a simple PSQ pre-shared key generator
and confirmation handshake between an initiator and a responder
communicating via a TCP stream. The PSQ pre-shared key generated this
way may then be inserted wherever a PSK of the given length is
accepted.

## What does the example do?
The responder will wait for initiator connections on a fixed port and
the initator will connect to that port to send out the PSQ message.

When you add `RUST_LOG=debug`, the debug output will show the derived
PSK at both side.

The example uses ML-KEM 768 as the PSQ KEM and Ed25519 for client
authentication. Another option for the PSQ KEM is Classic McEliece
(under feature `classic-mceliece`) using the
[`classic-mceliece-rust`](https://crates.io/crates/classic-mceliece-rust/2.0.2)
crate.

The example implements a setup phase that is to be considered outside
of the protocol. In this phase the initiator generates a signing key
and sends over a certificate to the responder (In this case, the
certificate is just the verification key itself).  Similarly, the
responder creates a PSQ public key and makes that available to the
initiator during setup.

## How can I run it?
To start the responder: `RUST_LOG=debug cargo run --example psq -- responder`
To start the initiator: `RUST_LOG=debug cargo run --example psq -- initiator`

This will run responder and initator on fixed ports on
`localhost`. The example implements the following additional command
line arguments:
 - `--host`: to specify a different responder hostname
 - `--port`: to specify a different responde port
 - `--context`: to specify a domain separation context for the
   generated pre-shared key (defaults to `example application
   context`)
 - `--handle`: to specify a handle for the generated PSK at the
   responder side (defaults to `psq example handle`)
