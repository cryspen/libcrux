macro_rules! hax_debug_assert {
    ($($arg:tt)*) => {
        #[cfg(hax)]
        {
            hax_lib::debug_assert!($($arg)*)
        }
        #[cfg(not(hax))]
        {
            debug_assert!($($arg)*)
        }
    };
}

pub(crate) use hax_debug_assert;
