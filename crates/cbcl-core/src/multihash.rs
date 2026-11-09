//! Canonical SHA2-256 multihashes, in multibase base16 (lowercase) text.
//! Binary layout: unsigned-varint code 0x12, unsigned-varint length 0x20,
//! then the 32 digest bytes. Text is `f1220` followed by 64 lowercase hex digits.
//! Hash input and Merkle construction are independent of this wire encoding.
use alloc::string::String;

pub const SHA2_256_CODE: u8 = 0x12;
pub const DIGEST_SIZE: usize = 32;
pub const TEXT_PREFIX: &str = "f1220";
pub const TEXT_LEN: usize = 69;

pub fn encode(digest: &[u8; DIGEST_SIZE]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut text = String::with_capacity(TEXT_LEN);
    text.push_str(TEXT_PREFIX);
    for b in digest {
        text.push(HEX[(b >> 4) as usize] as char);
        text.push(HEX[(b & 15) as usize] as char);
    }
    text
}

/// Decode only the canonical SHA2-256 multibase representation. Unknown
/// algorithms, noncanonical bases/case, truncation and trailing bytes fail closed.
pub fn decode(text: &str) -> Option<[u8; DIGEST_SIZE]> {
    let hex = text.strip_prefix(TEXT_PREFIX)?;
    if hex.len() != DIGEST_SIZE * 2 {
        return None;
    }
    let nibble = |b: u8| match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        _ => None,
    };
    let mut digest = [0; DIGEST_SIZE];
    for (out, pair) in digest.iter_mut().zip(hex.as_bytes().chunks_exact(2)) {
        *out = nibble(pair[0])? * 16 + nibble(pair[1])?;
    }
    Some(digest)
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};
    #[test]
    fn multiformats_sha2_256_golden_vector() {
        // https://github.com/multiformats/multihash#example
        let digest: [u8; 32] = Sha256::digest(b"multihash").into();
        let text = "f12209cbc07c3f991725836a3aa2a581ca2029198aa420b9d99bc0e131d9f3e2cbe47";
        assert_eq!(encode(&digest), text);
        assert_eq!(decode(text), Some(digest));
    }
    #[test]
    fn rejects_noncanonical_and_unsupported_addresses() {
        let valid = encode(&[0xab; 32]);
        for bad in [
            valid.to_uppercase(),
            valid.replace("f1220", "f1320"),
            valid.replace("f1220", "f121f"),
            valid[1..].into(),
            valid[..68].into(),
            alloc::format!("{valid}00"),
            alloc::format!("sha256:{}", "ab".repeat(32)),
        ] {
            assert_eq!(decode(&bad), None, "{bad}");
        }
    }
}
