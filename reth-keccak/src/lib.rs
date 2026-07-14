#![no_std]

use core::{hint::spin_loop, ptr, slice};
use sha3::{Digest, Keccak256};

/// Hashes input with Reth's locked RustCrypto Keccak-256 dependency path.
///
/// The caller may pass a null input only for an empty message; output must always have room for
/// 32 bytes. The return value is zero on success and negative for an invalid ABI argument.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn reth_keccak256(input: *const u8, len: usize, out: *mut u8) -> i32 {
    if out.is_null() || (input.is_null() && len != 0) {
        return -1;
    }
    let bytes = if len == 0 {
        &[]
    } else {
        // SAFETY: the C ABI contract requires a valid range for nonempty input.
        unsafe { slice::from_raw_parts(input, len) }
    };
    let digest = Keccak256::digest(bytes);
    // SAFETY: the C ABI contract requires 32 writable bytes at out.
    unsafe { ptr::copy_nonoverlapping(digest.as_ptr(), out, 32) };
    0
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {
        spin_loop();
    }
}
