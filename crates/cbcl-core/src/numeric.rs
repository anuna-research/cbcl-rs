//! Deterministic non-integer atoms. Floats are finite IEEE 754 binary64;
//! decimals retain exact, arbitrary precision base-ten values.
use alloc::string::{String, ToString};
use core::{fmt, str::FromStr};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(try_from = "f64", into = "f64"))]
pub struct Float(u64);
impl Float {
    pub fn new(value: f64) -> Result<Self, &'static str> {
        if !value.is_finite() {
            return Err("float must be finite");
        }
        Ok(Self(if value == 0.0 { 0 } else { value.to_bits() }))
    }
    pub fn get(self) -> f64 {
        f64::from_bits(self.0)
    }
}
impl TryFrom<f64> for Float {
    type Error = &'static str;
    fn try_from(value: f64) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}
impl From<Float> for f64 {
    fn from(value: Float) -> Self {
        value.get()
    }
}
impl FromStr for Float {
    type Err = &'static str;
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        Self::new(text.parse().map_err(|_| "invalid float")?)
    }
}
impl fmt::Display for Float {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = self.get().to_string();
        f.write_str(&text)?;
        if !text.contains('.') && !text.contains('e') && !text.contains('E') {
            f.write_str(".0")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(try_from = "String", into = "String"))]
pub struct Decimal(String);
impl Decimal {
    /// Canonical exact value, without the wire's `m` suffix.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
impl FromStr for Decimal {
    type Err = &'static str;
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let (negative, text) = match text.strip_prefix('-') {
            Some(s) => (true, s),
            None => (false, text),
        };
        let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
        if whole.is_empty()
            || !whole.bytes().all(|c| c.is_ascii_digit())
            || !fraction.bytes().all(|c| c.is_ascii_digit())
            || text.ends_with('.')
        {
            return Err("invalid decimal");
        }
        let whole = whole.trim_start_matches('0');
        let fraction = fraction.trim_end_matches('0');
        let mut value = String::new();
        if negative && (!whole.is_empty() || !fraction.is_empty()) {
            value.push('-');
        }
        value.push_str(if whole.is_empty() { "0" } else { whole });
        if !fraction.is_empty() {
            value.push('.');
            value.push_str(fraction);
        }
        Ok(Self(value))
    }
}
impl TryFrom<String> for Decimal {
    type Error = &'static str;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.parse()
    }
}
impl From<Decimal> for String {
    fn from(value: Decimal) -> Self {
        value.0
    }
}
impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}m", self.0)
    }
}

/// Recognize a complete non-integer numeric token. `m` marks an exact decimal;
/// a point or exponent marks a float. Integers keep their existing encoding.
pub fn parse_atom(text: &str) -> Result<Option<crate::sexpr::Atom>, &'static str> {
    let number_start = text.as_bytes().first().is_some_and(u8::is_ascii_digit)
        || text
            .strip_prefix('-')
            .and_then(|s| s.as_bytes().first())
            .is_some_and(u8::is_ascii_digit);
    if !number_start {
        return Ok(None);
    }
    if let Some(value) = text.strip_suffix('m') {
        return value.parse().map(crate::sexpr::Atom::Decimal).map(Some);
    }
    if text.contains('.') || text.contains('e') || text.contains('E') {
        return text.parse().map(crate::sexpr::Atom::Float).map(Some);
    }
    Ok(None)
}
