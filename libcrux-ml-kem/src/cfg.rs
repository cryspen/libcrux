/// Macro to simplify feature gating of verified code that should only be enabled
/// when unverified code is disabled.
macro_rules! cfg_verified {
    ($($item:item)*) => {
        $(
            #[cfg(not(feature = "pre-verification"))]
            #[allow(missing_docs)]
            $item
        )*
    }
}

/// Macro to simplify `pre-verification` feature gating
macro_rules! cfg_pre_verification {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "pre-verification")]
            #[cfg_attr(docsrs, doc(cfg(feature = "pre-verification")))]
            $item
        )*
    }
}

/// Macro to simplify `kyber` feature gating
#[cfg(feature = "pre-verification")]
macro_rules! cfg_kyber {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            $item
        )*
    }
}

/// Macro to simplify `eurydice` cfg gating
#[allow(unused_macros)]
macro_rules! cfg_no_eurydice {
    ($($item:item)*) => {
        $(
            #[cfg(not(eurydice))]
            $item
        )*
    }
}
