//! This module implements a libcrux-backed provider for the [hpke_rs] crate and
//! re-exports the items of that crate, specialized to the libcrux provider.
//!
//! <div class="warning">
//!
//! This is where the HPKE hacspec specification used to live, but that was moved to
//! <https://github.com/cryspen/hpke-spec>.
//!
//! </div>

pub mod provider;

pub type Context = hpke_rs::Context<provider::Provider>;
pub type Hpke = hpke_rs::Hpke<provider::Provider>;
pub use hpke_rs::{HpkeError, HpkeKeyPair, HpkePrivateKey, HpkePublicKey, Mode};

pub mod prelude {
    pub use super::{
        Context, Hpke, HpkeError, HpkeKeyPair, HpkePrivateKey, HpkePublicKey, Mode as HpkeMode,
        Mode,
    };
    pub use core::convert::TryFrom;
}
