//! SPEC-035 ADR-3502: immutable, host-supplied hybrid logical clock evidence.
//!
//! Advancement cases follow Kulkarni et al., Logical Physical Clocks (2014),
//! https://cse.buffalo.edu/tech-reports/2014-04.pdf, section 3. CBCL adds
//! fixed-width u64/u32 evidence and checked overflow refusal.
//!
//! This module reads no clock and performs no IO. Hosts supply physical milliseconds,
//! merge observed timestamps and durably retain the returned value. Recognition proves
//! canonical syntax, not honest clock generation or Byzantine ordering/finality.
#![forbid(unsafe_code)]
use alloc::format;
use alloc::string::String;

/// Fixed canonical spelling: `hlc-` + 16 lowercase hex + `-` + 8 lowercase hex.
pub const WIRE_LEN: usize = 29;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Hlc {
    pub physical_ms: u64,
    pub logical: u32,
}

impl Hlc {
    pub const fn new(physical_ms: u64, logical: u32) -> Self {
        Self {
            physical_ms,
            logical,
        }
    }

    /// Full recognition, including width, separators and lowercase canonical form.
    pub fn parse(text: &str) -> Option<Self> {
        let bytes = text.as_bytes();
        if bytes.len() != WIRE_LEN || !bytes.starts_with(b"hlc-") || bytes[20] != b'-' {
            return None;
        }
        let lower_hex = |b: &u8| b.is_ascii_digit() || (b'a'..=b'f').contains(b);
        if !bytes[4..20].iter().all(lower_hex) || !bytes[21..29].iter().all(lower_hex) {
            return None;
        }
        Some(Self::new(
            u64::from_str_radix(&text[4..20], 16).ok()?,
            u32::from_str_radix(&text[21..29], 16).ok()?,
        ))
    }

    pub fn render(self) -> String {
        format!("hlc-{:016x}-{:08x}", self.physical_ms, self.logical)
    }

    /// Advance for a local event or receipt of remote evidence. Overflow refuses
    /// issuance; it never wraps or silently moves physical time into the future.
    pub fn advance(self, now_ms: u64, remote: Option<Self>) -> Option<Self> {
        let physical = self
            .physical_ms
            .max(now_ms)
            .max(remote.map_or(0, |r| r.physical_ms));
        let logical = match remote {
            Some(r) if physical == self.physical_ms && physical == r.physical_ms => {
                self.logical.max(r.logical).checked_add(1)?
            }
            _ if physical == self.physical_ms => self.logical.checked_add(1)?,
            Some(r) if physical == r.physical_ms => r.logical.checked_add(1)?,
            _ => 0,
        };
        Some(Self::new(physical, logical))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_recognition_and_roundtrip() {
        for stamp in [
            Hlc::new(0, 0),
            Hlc::new(1_800_000_000_000, 42),
            Hlc::new(u64::MAX, u32::MAX),
        ] {
            assert_eq!(Hlc::parse(&stamp.render()), Some(stamp));
        }
        for invalid in [
            "",
            "hlc-1-0",
            "hlc-000000000000000A-00000000",
            "hlc-0000000000000000-000000000",
            "hlc-0000000000000000-0000000g",
            "hlc-0000000000000000-00000000x",
            "hlc-000000000000000é-00000000",
        ] {
            assert_eq!(Hlc::parse(invalid), None, "{invalid}");
        }
    }
    #[test]
    fn advance_handles_skew_receipt_ties_restart_and_overflow() {
        let own = Hlc::new(100, 4);
        assert_eq!(own.advance(99, None), Some(Hlc::new(100, 5)));
        assert_eq!(own.advance(101, None), Some(Hlc::new(101, 0)));
        assert_eq!(
            own.advance(99, Some(Hlc::new(100, 9))),
            Some(Hlc::new(100, 10))
        );
        assert_eq!(
            own.advance(99, Some(Hlc::new(102, 3))),
            Some(Hlc::new(102, 4))
        );
        assert_eq!(
            own.advance(103, Some(Hlc::new(102, 3))),
            Some(Hlc::new(103, 0))
        );
        let restored = Hlc::parse(&own.render()).unwrap();
        assert!(restored.advance(1, None).unwrap() > own);
        assert_eq!(Hlc::new(100, u32::MAX).advance(99, None), None);
        assert_eq!(own.advance(1, Some(Hlc::new(200, u32::MAX))), None);
        assert_eq!(Hlc::new(u64::MAX, u32::MAX).advance(u64::MAX, None), None);
    }
}
