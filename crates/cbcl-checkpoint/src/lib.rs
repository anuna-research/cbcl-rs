//! SPEC-035-cached-state-checkpoints: reusable native certificates and verified continuation.
#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]
extern crate alloc;

#[cfg(all(test, feature = "std"))]
mod all_heads_tests;

pub mod certificate;
#[cfg(all(test, feature = "std"))]
mod closed_grammar_tests;
pub mod codec;
pub mod coverage;
pub mod evidence;
#[cfg(feature = "std")]
pub mod host;
#[cfg(all(test, feature = "std"))]
mod host_boundary_tests;
#[cfg(all(test, feature = "std"))]
mod lifecycle_tests;
pub mod member;
pub mod progress_resume;
pub mod resource_resume;
#[cfg(feature = "std")]
pub mod runtime;
#[cfg(all(test, feature = "std"))]
mod scaling_tests;
pub mod summary;
#[cfg(test)]
pub(crate) mod test_support;

use sha2::{Digest, Sha256};
pub type Hash = [u8; 32];
pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    Missing(alloc::vec::Vec<alloc::string::String>),
    Unsupported,
    Budget,
    Concurrent,
    Io(alloc::string::String),
    Disabled,
    Cancelled,
}
impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
#[cfg(feature = "std")]
impl std::error::Error for Error {}
#[cfg(feature = "std")]
impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e.to_string())
    }
}
pub fn hash(domain: &[u8], payload: &[u8]) -> Hash {
    let mut h = Sha256::new();
    h.update((domain.len() as u32).to_be_bytes());
    h.update(domain);
    h.update((payload.len() as u32).to_be_bytes());
    h.update(payload);
    h.finalize().into()
}
pub fn hex(bytes: &[u8]) -> alloc::string::String {
    use core::fmt::Write;
    let mut s = alloc::string::String::new();
    for b in bytes {
        write!(&mut s, "{b:02x}").expect("string formatting");
    }
    s
}
