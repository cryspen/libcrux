mod multiplexed;

pub use multiplexed::*;

#[cfg(feature = "chacha20poly1305")]
pub use libcrux_chacha20poly1305 as chacha20poly1305;

#[cfg(feature = "xchacha20poly1305")]
pub use libcrux_chacha20poly1305::xchacha20_poly1305 as xchacha20poly1305;
