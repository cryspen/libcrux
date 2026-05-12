//! Helper functions for constant time tests using valgrind.
//!
//! When libcrux-ml-dsa is compiled with the `valgrind_ct_test` cfg,
//! these functions will mark the respective memory as undefined (classify)
//! or defined (declassify). Running the binary compiled with the cfg
//! under valgrind's memcheck tool will check for any code paths
//! dependent on the classified memory.

/// Mark memory as secret.
///
/// No-op if `valgrind_ct_test` cfg is not enabled.
#[cfg_attr(not(valgrind_ct_test), allow(unused_variables))]
pub(crate) fn ct_classify<T: ?Sized>(val: &T) {
    #[cfg(valgrind_ct_test)]
    {
        use std::ffi::c_void;
        crabgrind::memcheck::mark_memory(
            val as *const _ as *const c_void,
            size_of_val(val),
            crabgrind::memcheck::MemState::Undefined,
        )
        .expect("libcrux-ml-dsa compiled with '--cfg valgrind_ct_test' must be run under valgrind");
    }
    // Otherwise, no-op
}

/// Declassify secret memory.
///
/// No-op if `valgrind_ct_test` cfg is not enabled.
#[cfg_attr(not(valgrind_ct_test), allow(unused_variables))]
pub(crate) fn ct_declassify<T: ?Sized>(val: &T) {
    #[cfg(valgrind_ct_test)]
    {
        use std::ffi::c_void;
        // If we expect the error, we get false positives in sign_internal.
        // If a valgrind_ct_test binary is not run under valgrind, the expect
        // in the classify should fail, so it is okay here to ignore the error
        let _ = crabgrind::memcheck::mark_memory(
            val as *const _ as *const c_void,
            size_of_val(val),
            crabgrind::memcheck::MemState::Defined,
        );
    }
    // Otherwise, no-op
}
