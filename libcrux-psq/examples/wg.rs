use std::{
    fs::File,
    io::{BufReader, BufWriter},
    net::SocketAddr,
    str::FromStr,
};

use base64::{prelude::BASE64_STANDARD, Engine};
use clap::{command, Parser};
use defguard_wireguard_rs::{
    error::WireguardInterfaceError,
    key::Key,
    net::{IpAddrMask, IpAddrParseError},
    InterfaceConfiguration, WGApi, WireguardInterfaceApi,
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct Peer {
    public_key: String,
    allowed_ips: String,
    endpoint: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct Interface {
    private_key: String,
    address: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct Client {
    // Interface
    interface: Interface,

    // Peer
    peer: Peer,
}

#[derive(Debug, Serialize, Deserialize)]
struct Server {
    // Interface
    interface: Interface,

    // Peers
    peers: Vec<Peer>,
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Client
    #[arg(short, long)]
    client: Option<String>,

    /// Server
    #[arg(short, long)]
    server: Option<String>,

    /// Generate a new config
    #[arg(short, long)]
    generate: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Error {
    InvalidArguments,
    WireGuard,
    IpAddrError,
    IoError,
    SerdeError,
}

impl From<WireguardInterfaceError> for Error {
    fn from(e: WireguardInterfaceError) -> Self {
        log::error!("Wireguard interface error: {e:?}");
        Self::WireGuard
    }
}

impl From<IpAddrParseError> for Error {
    fn from(e: IpAddrParseError) -> Self {
        log::error!("IP addr parse error: {e:?}");
        Self::IpAddrError
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        log::error!("IO error: {e:?}");
        Self::IoError
    }
}

impl From<serde_json::Error> for Error {
    fn from(e: serde_json::Error) -> Self {
        log::error!("JSON error: {e:?}");
        Self::SerdeError
    }
}

fn main() -> Result<(), Error> {
    // Add logging
    pretty_env_logger::try_init().unwrap();

    let args = Args::parse();

    if args.server.is_some() && args.client.is_some() && !args.generate {
        return Err(Error::InvalidArguments);
    }

    if args.generate {
        // Generate a new config
        let mut rng = rand::rng();
        let (sk, pk) = libcrux_ecdh::key_gen(libcrux_ecdh::Algorithm::X25519, &mut rng).unwrap();
        let (sk_server, pk_server) =
            libcrux_ecdh::key_gen(libcrux_ecdh::Algorithm::X25519, &mut rng).unwrap();

        let client = Client {
            interface: Interface {
                private_key: BASE64_STANDARD.encode(&sk),
                address: "10.0.0.2/24".to_string(),
            },

            peer: Peer {
                public_key: BASE64_STANDARD.encode(&pk_server),
                allowed_ips: "0.0.0.0/0".to_string(),
                // localhost endpoint only
                endpoint: Some("127.0.0.1".to_string()),
            },
        };

        let server = Server {
            interface: Interface {
                private_key: BASE64_STANDARD.encode(&sk_server),
                address: "10.0.0.1/24".to_string(),
            },
            peers: vec![Peer {
                public_key: BASE64_STANDARD.encode(&pk),
                allowed_ips: "10.0.0.2/32".to_string(),
                endpoint: None,
            }],
        };

        let file = File::create(args.client.clone().unwrap())?;
        let mut writer = BufWriter::new(file);
        serde_json::to_writer_pretty(&mut writer, &client)?;

        let file = File::create(args.server.clone().unwrap())?;
        let mut writer = BufWriter::new(file);
        serde_json::to_writer_pretty(&mut writer, &server)?;
    }

    if let Some(cfg_file) = &args.server {
        let server_cfg = {
            let file = File::open(cfg_file)?;
            let mut reader = BufReader::new(file);
            serde_json::from_reader(&mut reader)?
        };

        server(server_cfg)?;
    }

    Ok(())
}

fn client() -> Result<(), Error> {
    // Create new API object for interface
    let ifname: String = if cfg!(target_os = "linux") || cfg!(target_os = "freebsd") {
        "wg0".into()
    } else {
        "utun3".into()
    };

    #[cfg(not(target_os = "macos"))]
    let wgapi = WGApi::<Kernel>::new(ifname.clone())?;
    #[cfg(target_os = "macos")]
    let wgapi = WGApi::new(ifname.clone(), true)?;

    // create interface
    wgapi.create_interface()?;

    // Generate key pair
    let mut rng = rand::rng();
    let (sk, pk) = libcrux_ecdh::key_gen(libcrux_ecdh::Algorithm::X25519, &mut rng).unwrap();

    // Peer key
    let peer_key = Key::new(pk.as_slice().try_into().unwrap());
    let mut peer = defguard_wireguard_rs::host::Peer::new(peer_key.clone());

    log::info!("endpoint");

    // Your WireGuard server endpoint which client connects to
    let endpoint: SocketAddr = "10.10.10.10:55001".parse().unwrap();

    // Peer endpoint and interval
    peer.endpoint = Some(endpoint);
    peer.persistent_keepalive_interval = Some(25);
    peer.allowed_ips.push(IpAddrMask::from_str("10.6.0.0/24")?);
    peer.allowed_ips
        .push(IpAddrMask::from_str("192.168.22.0/24")?);

    // interface configuration
    let interface_config = InterfaceConfiguration {
        name: ifname.clone(),
        prvkey: BASE64_STANDARD.encode(&sk),
        port: 12345,
        peers: vec![peer],
        address: "10.6.0.30".parse().unwrap(),
    };

    #[cfg(not(windows))]
    wgapi.configure_interface(&interface_config)?;
    #[cfg(windows)]
    wgapi.configure_interface(&interface_config, &[], &[])?;
    wgapi.configure_peer_routing(&interface_config.peers)?;

    Ok(())
}

fn server(server: Server) -> Result<(), Error> {
    log::info!("Starting wireguard server ...");

    // Create new api object for interface management
    let ifname: String = if cfg!(target_os = "linux") || cfg!(target_os = "freebsd") {
        "wg0".into()
    } else {
        "utun3".into()
    };

    #[cfg(not(target_os = "macos"))]
    let wgapi = WGApi::<Kernel>::new(ifname.clone())?;
    #[cfg(target_os = "macos")]
    let wgapi = WGApi::new(ifname.clone(), true)?;

    // create host interface
    wgapi.create_interface()?;

    // read current interface status
    let host = wgapi.read_interface_data()?;
    log::info!("WireGuard interface before configuration: {host:#?}");

    let mut interface_config = InterfaceConfiguration {
        name: ifname.clone(),
        prvkey: server.interface.private_key,
        address: server.interface.address,
        port: 12345,
        peers: vec![],
    };

    // prepare initial WireGuard interface configuration with one client
    for peer in server.peers {
        let peer_key = Key::new(
            BASE64_STANDARD
                .decode(peer.public_key)
                .unwrap()
                .try_into()
                .unwrap(),
        );
        let mut new_peer = defguard_wireguard_rs::host::Peer::new(peer_key);
        let addr = IpAddrMask::from_str(&peer.allowed_ips).unwrap();
        new_peer.allowed_ips.push(addr);

        interface_config.peers.push(new_peer);
    }

    log::info!("Prepared interface configuration: {interface_config:?}");

    // apply initial interface configuration
    #[cfg(not(windows))]
    wgapi.configure_interface(&interface_config)?;
    #[cfg(windows)]
    wgapi.configure_interface(&interface_config, &[])?;

    // read current interface status
    let host = wgapi.read_interface_data()?;
    log::info!("WireGuard interface after configuration: {host:#?}");

    // read current interface status
    let host = wgapi.read_interface_data()?;
    log::info!("WireGuard interface with peers: {host:#?}");

    // remove interface
    wgapi.remove_interface()?;

    Ok(())
}
