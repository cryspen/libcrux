use std::{
    fs::File,
    io::{Read, Write},
};

use libcrux::{
    drbg::{self, Drag},
    kem,
};

use clap::{Parser, Subcommand};

#[derive(Clone, Copy, Debug)]
#[repr(u16)]
enum Variant {
    MlKem512 = 512,
    MlKem768 = 768,
    MlKem1024 = 1024,
}

#[derive(Subcommand)]
enum GenerateCli {
    GenerateKey {
        /// Optionally, a file name to store the keys into.
        ///
        /// The keys will be store into `$out.pub` and `$out` when this is used.
        #[arg(short, long)]
        out: Option<String>,
    },
    Encaps {
        /// Public key input file to encrypt to.
        #[arg(short, long)]
        key: String,

        /// Optionally, a file name to store the encapsulation output.
        ///
        /// This defaults to `mlkem.ct``.
        #[arg(short, long)]
        out: Option<String>,
    },
    Decaps {
        /// Private key input file to decapsulate with.
        #[arg(short, long)]
        key: String,

        /// Optionally, a file name to store the encapsulation output.
        ///
        /// This defaults to `mlkem.ct``.
        #[arg(short, long)]
        out: Option<String>,
    },
}

#[derive(Parser)]
struct Cli {
    /// Generate a key pair and write it out.
    ///
    /// When no output files are given, `mlkem.pub` and `mlkem` are used.
    #[command(subcommand)]
    cmd: GenerateCli,

    /// The key length, 512, 768, or 1024
    ///
    /// Defaults to 768
    #[arg(short, long)]
    length: Option<u16>,
}

fn main() {
    pretty_env_logger::init();

    let cli = Cli::parse();

    let alg = if let Some(l) = cli.length {
        match l {
            512 => kem::Algorithm::MlKem512,
            768 => kem::Algorithm::MlKem768,
            1024 => kem::Algorithm::MlKem1024,
            _ => {
                eprintln!("Invalid algorithm variant {l}");
                return;
            }
        }
    } else {
        kem::Algorithm::MlKem768
    };

    let mut rng = Drag::new(libcrux::digest::Algorithm::Sha256).unwrap();

    match cli.cmd {
        GenerateCli::GenerateKey { out: file } => {
            // Generate a key pair and write it out.
            let (sk_name, pk_name) = match file {
                Some(n) => (n.clone(), format!("{n}.pub")),
                None => ("mlkem".to_owned(), "mlkem.pub".to_owned()),
            };

            let (secret_key, public_key) = kem::key_gen(alg, &mut rng).unwrap();

            File::create(sk_name)
                .expect("Can not create file {sk_name}")
                .write_all(&secret_key.encode())
                .expect("Error writing private key");
            File::create(pk_name)
                .expect("Can not create file {pk_name}")
                .write_all(&public_key.encode())
                .expect("Error writing public key");
        }

        GenerateCli::Encaps { key, out } => {
            let mut pk = Vec::new();
            File::open(key)
                .expect("Error opening key file {key}")
                .read_to_end(&mut pk)
                .expect("Error reading key file {key}.");
            let pk = kem::PublicKey::decode(alg, &pk).expect("Error decoding public key");

            let (shared_secret, ciphertext) =
                pk.encapsulate(&mut rng).expect("Error encapsulating");

            let out = match out {
                Some(n) => n,
                None => "mlkem.ct".to_owned(),
            };

            let mut out_file = File::create(out).expect("Can not create file {pk_name}");
            out_file
                .write_all(&shared_secret.encode())
                .expect("Error writing public key");
            out_file
                .write_all(&ciphertext.encode())
                .expect("Error writing public key");
        }
        GenerateCli::Decaps { key, out } => todo!(),
    }
}
