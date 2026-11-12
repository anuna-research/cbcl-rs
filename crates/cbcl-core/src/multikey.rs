//! Bounded public Multikey payloads (SPEC-043 CON-4301 / REQ-4308).
//!
//! W3C Controlled Identifiers 1.0: base58btc of a minimal multicodec varint
//! followed by public key bytes. This is structural recognition, not curve-point
//! validation, proof of possession, trust, or support for a signing algorithm.
//! Private keys and unrecognized codecs are never accepted as public keys.
#![forbid(unsafe_code)]

use alloc::{format, string::String, vec::Vec};
use core::{fmt, str::FromStr};

/// Recognition bound applied before base58 decoding. Current public codecs
/// encode at most 51 bytes; this bound is independent of native allocation size.
pub const MAX_TEXT_BYTES: usize = 256;

/// Public key codecs recognized by this profile. Recognition does not imply
/// that a key can be used for signatures; X25519 is for key agreement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PublicKeyCodec {
    Ed25519,
    X25519,
    P256,
    P384,
}

impl PublicKeyCodec {
    pub fn code(self) -> u64 {
        match self {
            Self::Ed25519 => 0xed,
            Self::X25519 => 0xec,
            Self::P256 => 0x1200,
            Self::P384 => 0x1201,
        }
    }

    pub fn from_code(code: u64) -> Result<Self, MultikeyError> {
        match code {
            0xed => Ok(Self::Ed25519),
            0xec => Ok(Self::X25519),
            0x1200 => Ok(Self::P256),
            0x1201 => Ok(Self::P384),
            _ => Err(MultikeyError::UnsupportedCodec(code)),
        }
    }

    fn public_key_size(self) -> usize {
        match self {
            Self::Ed25519 | Self::X25519 => 32,
            Self::P256 => 33,
            Self::P384 => 49,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultikeyError {
    InvalidEncoding,
    InvalidPublicKey,
    UnsupportedCodec(u64),
    UnsupportedSigningCodec(u64),
}

impl fmt::Display for MultikeyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidEncoding => f.write_str("invalid or oversized public Multikey encoding"),
            Self::InvalidPublicKey => {
                f.write_str("invalid public Multikey length or compressed prefix")
            }
            Self::UnsupportedCodec(code) => {
                write!(f, "unsupported public Multikey codec: {code:#x}")
            }
            Self::UnsupportedSigningCodec(code) => {
                write!(f, "unsupported signing Multikey codec: {code:#x}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MultikeyError {}

/// A fully recognized public Multikey. Private fields and checked constructors
/// prevent invalid values from being serialized. No secret-key API is provided.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Multikey {
    codec: PublicKeyCodec,
    bytes: Vec<u8>,
}

impl Multikey {
    pub fn new(codec: PublicKeyCodec, bytes: &[u8]) -> Result<Self, MultikeyError> {
        if bytes.len() != codec.public_key_size()
            || (matches!(codec, PublicKeyCodec::P256 | PublicKeyCodec::P384)
                && !matches!(bytes.first(), Some(2 | 3)))
        {
            return Err(MultikeyError::InvalidPublicKey);
        }
        Ok(Self {
            codec,
            bytes: bytes.into(),
        })
    }

    /// Recognize canonical base58btc and the complete public-key payload.
    pub fn parse(text: &str) -> Result<Self, MultikeyError> {
        if text.len() > MAX_TEXT_BYTES {
            return Err(MultikeyError::InvalidEncoding);
        }
        let encoded = text
            .strip_prefix('z')
            .filter(|s| !s.is_empty())
            .ok_or(MultikeyError::InvalidEncoding)?;
        let payload = bs58::decode(encoded)
            .into_vec()
            .map_err(|_| MultikeyError::InvalidEncoding)?;
        let (code, bytes) =
            unsigned_varint::decode::u64(&payload).map_err(|_| MultikeyError::InvalidEncoding)?;
        let mut buffer = unsigned_varint::encode::u64_buffer();
        let prefix = unsigned_varint::encode::u64(code, &mut buffer);
        if payload.len() - bytes.len() != prefix.len() || !payload.starts_with(prefix) {
            return Err(MultikeyError::InvalidEncoding);
        }
        let key = Self::new(PublicKeyCodec::from_code(code)?, bytes)?;
        // A complete recognized value must have exactly one accepted spelling.
        if key.to_multibase() != text {
            return Err(MultikeyError::InvalidEncoding);
        }
        Ok(key)
    }

    pub fn codec(&self) -> PublicKeyCodec {
        self.codec
    }
    pub fn public_key_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn to_multibase(&self) -> String {
        let mut buffer = unsigned_varint::encode::u64_buffer();
        let prefix = unsigned_varint::encode::u64(self.codec.code(), &mut buffer);
        let mut payload = Vec::with_capacity(prefix.len() + self.bytes.len());
        payload.extend_from_slice(prefix);
        payload.extend_from_slice(&self.bytes);
        format!("z{}", bs58::encode(payload).into_string())
    }
}

impl FromStr for Multikey {
    type Err = MultikeyError;
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        Self::parse(text)
    }
}

impl fmt::Display for Multikey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_multibase())
    }
}
