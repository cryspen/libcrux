RUST_TARGET_FLAG=--target=thumbv7em-none-eabihf

# Check no_std compatibility for crates that support it by default
cargo build \
  -p libcrux-chacha20poly1305 \
  -p libcrux-curve25519 \
  -p libcrux-ecdsa \
  -p libcrux-hacl-rs \
  -p libcrux-hkdf \
  -p libcrux-hmac \
  -p libcrux-intrinsics \
  -p libcrux-sha3 \
  -p libcrux-p256 \
  -p libcrux-poly1305 \
  -p libcrux-rsa \
  -p libcrux-secrets \
  -p libcrux-sha2 \
  -p libcrux-traits \
  $RUST_TARGET_FLAG

# Check no_std compatibility for default features except std
  cargo build \
  -p libcrux-ecdh \
  -p libcrux-kem \
  -p libcrux-ml-dsa -F mldsa44,mldsa65,mldsa87 \
  -p libcrux-ml-kem -F default-no-std \
  --no-default-features \
  $RUST_TARGET_FLAG
