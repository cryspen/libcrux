use std::{
    backtrace,
    net::{TcpListener, TcpStream},
    time::Duration,
};

use clap::Parser;
use libcrux_psq::legacy::{
    cred::Ed25519,
    impls::MlKem768,
    psk_registration::{Initiator, InitiatorMsg, Responder, ResponderMsg},
};
use libcrux_traits::kem::KEM;
use tls_codec::{Deserialize, Serialize, Size};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Error {
    InvalidArguments,
    Codec,
    Psq,
    Io,
    Kem,
}

fn print_bt() {
    let bt = backtrace::Backtrace::capture();
    log::error!("{bt}");
}

impl From<tls_codec::Error> for Error {
    fn from(value: tls_codec::Error) -> Self {
        log::error!("TLSCodec error: {value:?}");
        print_bt();
        Self::Codec
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        log::error!("IO error: {e:?}");
        print_bt();
        Self::Io
    }
}

impl From<libcrux_kem::Error> for Error {
    fn from(e: libcrux_kem::Error) -> Self {
        log::error!("KEM error: {e:?}");
        print_bt();
        Self::Kem
    }
}

impl From<libcrux_psq::legacy::Error> for Error {
    fn from(e: libcrux_psq::legacy::Error) -> Self {
        log::error!("PSQ error: {e:?}");
        print_bt();
        Self::Psq
    }
}

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
enum Side {
    Initiator,
    Responder,
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Side: initiator or responder
    #[arg(value_enum)]
    side: Side,

    #[arg(long)]
    host: Option<String>,

    #[arg(long)]
    port: Option<u16>,

    #[arg(long)]
    context: Option<String>,

    #[arg(long)]
    handle: Option<String>,
}

fn main() -> Result<(), Error> {
    // Add logging
    pretty_env_logger::try_init().unwrap();

    let args = Args::parse();

    if args.handle.is_some() && matches!(args.side, Side::Initiator) {
        log::info!("A handle can only be set on the responder.");
        return Err(Error::InvalidArguments);
    }

    let host = args.host.unwrap_or("localhost".to_string());
    let port = args.port.unwrap_or(0x7071);

    let ctx = args
        .context
        .unwrap_or("example application context".to_string());
    let handle = args.handle.unwrap_or("psq example handle".to_string());

    match args.side {
        Side::Initiator => initiator(host, port, ctx)?,
        Side::Responder => responder(host, port, ctx, handle)?,
    }

    Ok(())
}

/// The initiator protocol
fn initiator(host: String, port: u16, ctx: String) -> Result<(), Error> {
    // Set up networking
    let mut stream = TcpStream::connect((host.clone(), port))?;
    stream.set_nodelay(true)?;

    log::info!("Starting new Initiator connection ...");
    log::debug!("  {host}:{port}");

    // This setup is outside of PSQ but required to set up both sides for the protocol.
    let (sk, credential, responder_pk) = {
        // Register an Ed25519 identity with the responder.
        let mut rng = rand::rng();
        let (sk, pk) = libcrux_ed25519::generate_key_pair(&mut rng).unwrap();

        // Send the public key to the responder
        pk.tls_serialize(&mut stream)?;

        // Get the responder's public key.
        let responder_pk =
            <libcrux_psq::legacy::impls::MlKem768 as KEM>::EncapsulationKey::tls_deserialize(
                &mut stream,
            )?;

        (sk, pk, responder_pk)
    };

    // Generate the first PSQ message
    let mut rng = rand::rng();
    let (state, msg) = Initiator::send_initial_message::<Ed25519, MlKem768>(
        ctx.as_bytes(),
        Duration::from_secs(3600),
        &responder_pk,
        sk.as_ref(),
        &credential,
        &mut rng,
    )
    .unwrap();
    log::trace!(
        "sending {} bytes for initiator msg",
        msg.tls_serialized_len()
    );
    msg.tls_serialize(&mut stream)?;

    // Read the response
    let responder_msg = ResponderMsg::tls_deserialize(&mut stream)?;
    log::trace!(
        "read {} bytes for responder msg",
        responder_msg.tls_serialized_len()
    );

    // Finish the handshake
    let psk = state.complete_handshake(&responder_msg)?;

    log::debug!(
        "Registered psk for: {}",
        String::from_utf8(psk.psk_handle.clone()).unwrap()
    );
    log::debug!("  with psk: {:x?}", psk.psk);

    Ok(())
}

fn responder(host: String, port: u16, ctx: String, handle: String) -> Result<(), Error> {
    let listener = TcpListener::bind((host.as_str(), port)).unwrap();

    log::info!("Listening for incoming connection ...");
    log::debug!("  {host}:{port}");

    for stream in listener.incoming() {
        let Ok(mut stream) = stream else {
            return Err(Error::Io);
        };

        log::info!("  Accepted incoming connection ...");

        // Setup before running PSQ
        let (initiator_credential, sk, pk) = {
            // Read and store the initiator identity.
            let initiator_credential =
                libcrux_ed25519::VerificationKey::tls_deserialize(&mut stream)?;

            // Generate the responder key pair.
            let mut rng = rand::rng();
            let (sk, pk) = MlKem768::generate_key_pair(&mut rng).unwrap();

            // Send the public key to the initiator.
            let _bytes_written = pk.tls_serialize(&mut stream)?;

            (initiator_credential, sk, pk)
        };

        // Read the initial PSQ message.
        let msg = InitiatorMsg::<MlKem768>::tls_deserialize(&mut stream)?;
        log::trace!("read {} bytes for initiator msg", msg.tls_serialized_len());

        let (psk, msg) = Responder::send::<Ed25519, MlKem768>(
            handle.as_bytes(),
            Duration::from_secs(3600),
            ctx.as_bytes(),
            &pk,
            &sk,
            &initiator_credential,
            &msg,
        )?;

        // Send the message back.
        let _bytes_written = msg.tls_serialize(&mut stream)?;

        log::debug!(
            "Registered psk for: {}",
            String::from_utf8(psk.psk_handle.clone()).unwrap()
        );
        log::debug!("  with psk: {:x?}", psk.psk);
    }

    Ok(())
}
