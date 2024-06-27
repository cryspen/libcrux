/// Macro to simplify feature gating of verified code
macro_rules! cfg_verified {
    ($($item:item)*) => {
        $(
            #[cfg(not(feature = "pre-verification"))]
            $item
        )*
    }
}

/// Macro to simplify `pre-verification` feature gating
macro_rules! cfg_pre_verification {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "pre-verification")]
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
            $item
        )*
    }
}
