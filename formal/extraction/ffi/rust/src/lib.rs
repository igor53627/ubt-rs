//! Rust FFI bindings for OCaml extracted UBT code.
//!
//! This crate provides C-compatible functions that can be called from OCaml
//! to use the Rust UBT implementation's cryptographic primitives.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                     OCaml Extracted Code                        │
//! │  (Formally verified tree operations from Rocq/Coq proofs)       │
//! └───────────────────────────┬─────────────────────────────────────┘
//!                             │ Ctypes FFI calls
//!                             ▼
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                     This Rust Library                           │
//! │  (C-compatible FFI functions for hash operations)               │
//! └───────────────────────────┬─────────────────────────────────────┘
//!                             │ Direct Rust calls
//!                             ▼
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                     UBT Rust Crate                              │
//! │  (BLAKE3/SHA256 hashing, tree types)                            │
//! └─────────────────────────────────────────────────────────────────┘
//! ```

use std::slice;

/// BLAKE3 hash of 32 bytes → 32 bytes
///
/// # Safety
/// - `input` must point to at least 32 bytes
/// - `output` must point to at least 32 bytes of writable memory
#[no_mangle]
pub unsafe extern "C" fn rust_blake3_hash_32(input: *const u8, output: *mut u8) {
    let input_slice = slice::from_raw_parts(input, 32);
    let hash = blake3::hash(input_slice);
    let output_slice = slice::from_raw_parts_mut(output, 32);
    output_slice.copy_from_slice(hash.as_bytes());
}

/// BLAKE3 hash of 64 bytes → 32 bytes (for internal node hashing)
///
/// # Safety
/// - `left` must point to at least 32 bytes
/// - `right` must point to at least 32 bytes
/// - `output` must point to at least 32 bytes of writable memory
#[no_mangle]
pub unsafe extern "C" fn rust_blake3_hash_64(
    left: *const u8,
    right: *const u8,
    output: *mut u8,
) {
    let left_slice = slice::from_raw_parts(left, 32);
    let right_slice = slice::from_raw_parts(right, 32);

    let mut hasher = blake3::Hasher::new();
    hasher.update(left_slice);
    hasher.update(right_slice);
    let hash = hasher.finalize();

    let output_slice = slice::from_raw_parts_mut(output, 32);
    output_slice.copy_from_slice(hash.as_bytes());
}

/// BLAKE3 hash for stem nodes: hash(stem || 0x00 || subtree_root)
///
/// Per EIP-7864, stem nodes are hashed as:
/// `hash(31-byte stem || 0x00 marker || 32-byte subtree root)`
///
/// # Safety
/// - `stem` must point to at least 31 bytes
/// - `subtree_root` must point to at least 32 bytes
/// - `output` must point to at least 32 bytes of writable memory
#[no_mangle]
pub unsafe extern "C" fn rust_blake3_hash_stem(
    stem: *const u8,
    subtree_root: *const u8,
    output: *mut u8,
) {
    let stem_slice = slice::from_raw_parts(stem, 31);
    let subtree_slice = slice::from_raw_parts(subtree_root, 32);

    let mut hasher = blake3::Hasher::new();
    hasher.update(stem_slice);
    hasher.update(&[0x00]); // Marker byte
    hasher.update(subtree_slice);
    let hash = hasher.finalize();

    let output_slice = slice::from_raw_parts_mut(output, 32);
    output_slice.copy_from_slice(hash.as_bytes());
}

/// SHA256 hash of 32 bytes → 32 bytes
/// (Alternative hasher for compatibility testing)
///
/// # Safety
/// - `input` must point to at least 32 bytes
/// - `output` must point to at least 32 bytes of writable memory
#[no_mangle]
pub unsafe extern "C" fn rust_sha256_hash_32(input: *const u8, output: *mut u8) {
    use sha2::{Digest, Sha256};

    let input_slice = slice::from_raw_parts(input, 32);
    let hash = Sha256::digest(input_slice);

    let output_slice = slice::from_raw_parts_mut(output, 32);
    output_slice.copy_from_slice(&hash);
}

/// SHA256 hash of 64 bytes → 32 bytes
///
/// # Safety
/// - `left` must point to at least 32 bytes
/// - `right` must point to at least 32 bytes
/// - `output` must point to at least 32 bytes of writable memory
#[no_mangle]
pub unsafe extern "C" fn rust_sha256_hash_64(
    left: *const u8,
    right: *const u8,
    output: *mut u8,
) {
    use sha2::{Digest, Sha256};

    let left_slice = slice::from_raw_parts(left, 32);
    let right_slice = slice::from_raw_parts(right, 32);

    let mut hasher = Sha256::new();
    hasher.update(left_slice);
    hasher.update(right_slice);
    let hash = hasher.finalize();

    let output_slice = slice::from_raw_parts_mut(output, 32);
    output_slice.copy_from_slice(&hash);
}

/// Get the version string for this FFI library.
///
/// # Safety
/// - Returns a pointer to a static null-terminated string
#[no_mangle]
pub extern "C" fn rust_ubt_ffi_version() -> *const u8 {
    b"ubt-ffi-0.1.0\0".as_ptr()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_blake3_hash_32() {
        let input = [0x42u8; 32];
        let mut output = [0u8; 32];

        unsafe {
            rust_blake3_hash_32(input.as_ptr(), output.as_mut_ptr());
        }

        // Verify output is not all zeros
        assert!(output.iter().any(|&b| b != 0));

        // Verify deterministic
        let mut output2 = [0u8; 32];
        unsafe {
            rust_blake3_hash_32(input.as_ptr(), output2.as_mut_ptr());
        }
        assert_eq!(output, output2);
    }

    #[test]
    fn test_blake3_hash_64() {
        let left = [0x01u8; 32];
        let right = [0x02u8; 32];
        let mut output = [0u8; 32];

        unsafe {
            rust_blake3_hash_64(left.as_ptr(), right.as_ptr(), output.as_mut_ptr());
        }

        assert!(output.iter().any(|&b| b != 0));
    }

    #[test]
    fn test_blake3_hash_stem() {
        let stem = [0x03u8; 31];
        let subtree_root = [0x04u8; 32];
        let mut output = [0u8; 32];

        unsafe {
            rust_blake3_hash_stem(stem.as_ptr(), subtree_root.as_ptr(), output.as_mut_ptr());
        }

        assert!(output.iter().any(|&b| b != 0));
    }

    #[test]
    fn test_version() {
        let version = rust_ubt_ffi_version();
        let version_str = unsafe { std::ffi::CStr::from_ptr(version as *const i8) };
        assert_eq!(version_str.to_str().unwrap(), "ubt-ffi-0.1.0");
    }
}
