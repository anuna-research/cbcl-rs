//! Closed bounded binary records and RFC 9804 typed canonical S-expressions.
use crate::{Error, Hash, Result};
use alloc::{
    string::{String, ToString},
    vec::Vec,
};
use cbcl_core::{
    canonical::canonical_encode,
    message::Message,
    sexpr::{Atom, SExpr},
};

pub fn put_u32(out: &mut Vec<u8>, n: usize) {
    out.extend_from_slice(&(n as u32).to_be_bytes());
}
pub fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_u32(out, bytes.len());
    out.extend_from_slice(bytes);
}
pub fn put_string(out: &mut Vec<u8>, s: &str) {
    put_bytes(out, s.as_bytes());
}
pub struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    pub fn new(bytes: &'a [u8], max: usize) -> Result<Self> {
        if bytes.len() > max {
            return Err(Error::Budget);
        }
        Ok(Self { bytes, at: 0 })
    }
    pub fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.at.checked_add(n).ok_or(Error::Budget)?;
        let b = self
            .bytes
            .get(self.at..end)
            .ok_or(Error::Invalid("truncated record"))?;
        self.at = end;
        Ok(b)
    }
    pub fn u32(&mut self) -> Result<usize> {
        Ok(u32::from_be_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| Error::Invalid("integer"))?,
        ) as usize)
    }
    pub fn hash(&mut self) -> Result<Hash> {
        self.take(32)?
            .try_into()
            .map_err(|_| Error::Invalid("hash"))
    }
    pub fn count(&mut self, max: usize) -> Result<usize> {
        let n = self.u32()?;
        if n > max {
            return Err(Error::Budget);
        }
        Ok(n)
    }
    pub fn bytes(&mut self, max: usize) -> Result<&'a [u8]> {
        let n = self.count(max)?;
        self.take(n)
    }
    pub fn string(&mut self, max: usize) -> Result<String> {
        core::str::from_utf8(self.bytes(max)?)
            .map(str::to_string)
            .map_err(|_| Error::Invalid("utf8"))
    }
    pub fn finish(self) -> Result<()> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(Error::Invalid("trailing record bytes"))
        }
    }
}
pub fn message_bytes(message: &Message) -> Vec<u8> {
    canonical_encode(&SExpr::from(message.clone()))
}
pub fn decode_message(bytes: &[u8]) -> Result<Message> {
    if bytes.len() > 256 * 1024 {
        return Err(Error::Budget);
    }
    let sx = decode_sexpr(bytes, 256 * 1024)?;
    let m = Message::try_from(&sx).map_err(|_| Error::Invalid("native message grammar"))?;
    if message_bytes(&m) != bytes {
        return Err(Error::Invalid("noncanonical message fields"));
    }
    Ok(m)
}
pub fn decode_sexpr(bytes: &[u8], max: usize) -> Result<SExpr> {
    if bytes.len() > max {
        return Err(Error::Budget);
    }
    let mut at = 0;
    let mut fuel = max.min(1_000_000);
    let sx = sexpr(bytes, &mut at, 0, &mut fuel)?;
    if at != bytes.len() || canonical_encode(&sx) != bytes {
        return Err(Error::Invalid("noncanonical typed value"));
    }
    Ok(sx)
}
fn sexpr(b: &[u8], at: &mut usize, depth: usize, fuel: &mut usize) -> Result<SExpr> {
    if depth > 64 || *fuel == 0 {
        return Err(Error::Budget);
    }
    *fuel -= 1;
    if b.get(*at) == Some(&b'(') {
        *at += 1;
        let mut v = Vec::new();
        while b.get(*at) != Some(&b')') {
            if *at >= b.len() {
                return Err(Error::Invalid("unterminated list"));
            }
            v.push(sexpr(b, at, depth + 1, fuel)?);
        }
        *at += 1;
        return Ok(SExpr::List(v));
    }
    let start = *at;
    let mut n = 0usize;
    while let Some(c @ b'0'..=b'9') = b.get(*at) {
        n = n
            .checked_mul(10)
            .and_then(|n| n.checked_add((c - b'0') as usize))
            .ok_or(Error::Budget)?;
        *at += 1;
    }
    if start == *at || (*at - start > 1 && b[start] == b'0') || b.get(*at) != Some(&b':') {
        return Err(Error::Invalid("atom length"));
    }
    *at += 1;
    let end = (*at).checked_add(n).ok_or(Error::Budget)?;
    let raw = b.get(*at..end).ok_or(Error::Invalid("atom truncation"))?;
    *at = end;
    let (&tag, text) = raw
        .split_first()
        .ok_or(Error::Invalid("empty typed atom"))?;
    let s = core::str::from_utf8(text).map_err(|_| Error::Invalid("utf8 atom"))?;
    Ok(SExpr::Atom(match tag {
        b'S' => Atom::Symbol(s.into()),
        b'K' => Atom::Keyword(s.into()),
        b'Q' => Atom::Str(s.into()),
        b'N' => Atom::Num(s.parse().map_err(|_| Error::Invalid("number atom"))?),
        b'B' => match s {
            "t" => Atom::Bool(true),
            "f" => Atom::Bool(false),
            _ => return Err(Error::Invalid("bool atom")),
        },
        _ => return Err(Error::Invalid("atom tag")),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_native_roundtrip_and_hostile_lengths() {
        let m = cbcl_parser::parse_message(
            &cbcl_parser::parse("(tell @a :x 12 :thread \"t\")").unwrap(),
        )
        .unwrap();
        let b = message_bytes(&m);
        assert_eq!(decode_message(&b).unwrap(), m);
        let mut trailing = b.clone();
        trailing.push(0);
        assert!(decode_message(&trailing).is_err());
        assert!(decode_message(b"999999999999999999999999999999999999:").is_err());
        assert!(decode_message(b"(2:Sx").is_err());
        assert!(decode_message(b"(03:Stt)").is_err());
    }
}
