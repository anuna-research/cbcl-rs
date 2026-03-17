//! S-expression data types.
//!
//! Mirrors `SExpr.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::str::FromStr;

/// Atomic values in S-expressions (REQ-001).
///
/// Mirrors `CBCL.Atom` in `SExpr.lean:14–19`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Atom {
    Symbol(String),
    Str(String),
    Num(i64),
    Bool(bool),
    Keyword(String),
}

/// S-expression: either an atom or a list (REQ-002).
///
/// Mirrors `CBCL.SExpr` in `SExpr.lean:24–27`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SExpr {
    Atom(Atom),
    List(Vec<SExpr>),
}

impl SExpr {
    /// Number of nodes in the S-expression tree (REQ-004).
    pub fn size(&self) -> usize {
        match self {
            SExpr::Atom(_) => 1,
            SExpr::List(items) => 1 + items.iter().map(|e| e.size()).sum::<usize>(),
        }
    }

    /// Approximate byte size of the S-expression (REQ-004).
    pub fn byte_size(&self) -> usize {
        match self {
            SExpr::Atom(a) => match a {
                Atom::Symbol(s) | Atom::Str(s) | Atom::Keyword(s) => s.len(),
                Atom::Num(_) => core::mem::size_of::<i64>(),
                Atom::Bool(_) => 1,
            },
            SExpr::List(items) => items.iter().map(|e| e.byte_size()).sum(),
        }
    }

    /// Maximum nesting depth (REQ-004).
    pub fn depth(&self) -> usize {
        match self {
            SExpr::Atom(_) => 0,
            SExpr::List(items) => 1 + items.iter().map(|e| e.depth()).max().unwrap_or(0),
        }
    }

    /// Check if this is a symbol with the given name (REQ-005).
    pub fn is_symbol(&self, name: &str) -> bool {
        matches!(self, SExpr::Atom(Atom::Symbol(s)) if s == name)
    }
}

// ---------------------------------------------------------------------------
// Display
// ---------------------------------------------------------------------------

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Symbol(s) => f.write_str(s),
            Atom::Str(s) => {
                f.write_str("\"")?;
                for ch in s.chars() {
                    match ch {
                        '"' => f.write_str("\\\"")?,
                        '\\' => f.write_str("\\\\")?,
                        '\n' => f.write_str("\\n")?,
                        '\r' => f.write_str("\\r")?,
                        '\t' => f.write_str("\\t")?,
                        c => fmt::Write::write_char(f, c)?,
                    }
                }
                f.write_str("\"")
            }
            Atom::Num(n) => write!(f, "{n}"),
            Atom::Bool(b) => f.write_str(if *b { "#t" } else { "#f" }),
            Atom::Keyword(k) => {
                f.write_str(":")?;
                f.write_str(k)
            }
        }
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Atom(a) => fmt::Display::fmt(a, f),
            SExpr::List(items) => {
                f.write_str("(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    fmt::Display::fmt(item, f)?;
                }
                f.write_str(")")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// FromStr
// ---------------------------------------------------------------------------

/// Error returned when parsing an S-expression from a string fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseSExprError(String);

impl fmt::Display for ParseSExprError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl FromStr for SExpr {
    type Err = ParseSExprError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let input = s.trim();
        if input.is_empty() {
            return Err(ParseSExprError(String::from("empty input")));
        }
        let (expr, rest) = parse_one(input)?;
        if !rest.trim().is_empty() {
            return Err(ParseSExprError(alloc::format!(
                "trailing input: {}",
                rest.trim()
            )));
        }
        Ok(expr)
    }
}

/// Parse a single S-expression from the front of `input`, returning the
/// parsed expression and the remaining unconsumed input.
fn parse_one(input: &str) -> Result<(SExpr, &str), ParseSExprError> {
    let input = skip_ws(input);
    if input.is_empty() {
        return Err(ParseSExprError(String::from("unexpected end of input")));
    }
    match input.as_bytes()[0] {
        b'(' => parse_list(input),
        b'"' => parse_string(input),
        b'#' => parse_bool(input),
        b':' => parse_keyword(input),
        _ => parse_num_or_symbol(input),
    }
}

fn skip_ws(s: &str) -> &str {
    s.trim_start()
}

fn parse_list(input: &str) -> Result<(SExpr, &str), ParseSExprError> {
    debug_assert!(input.starts_with('('));
    let mut rest = &input[1..];
    let mut items = Vec::new();
    loop {
        rest = skip_ws(rest);
        if rest.is_empty() {
            return Err(ParseSExprError(String::from("unclosed list")));
        }
        if rest.starts_with(')') {
            rest = &rest[1..];
            break;
        }
        let (item, r) = parse_one(rest)?;
        items.push(item);
        rest = r;
    }
    Ok((SExpr::List(items), rest))
}

fn parse_string(input: &str) -> Result<(SExpr, &str), ParseSExprError> {
    debug_assert!(input.starts_with('"'));
    let bytes = input.as_bytes();
    let mut i = 1;
    let mut s = String::new();
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                return Ok((SExpr::Atom(Atom::Str(s)), &input[i + 1..]));
            }
            b'\\' => {
                i += 1;
                if i >= bytes.len() {
                    return Err(ParseSExprError(String::from("unterminated string escape")));
                }
                match bytes[i] {
                    b'"' => s.push('"'),
                    b'\\' => s.push('\\'),
                    b'n' => s.push('\n'),
                    b'r' => s.push('\r'),
                    b't' => s.push('\t'),
                    other => {
                        s.push('\\');
                        s.push(other as char);
                    }
                }
            }
            _ => {
                // Safety: we index byte-by-byte but push char-by-char.
                // For valid UTF-8 input this is correct; for multi-byte
                // chars we need to decode properly.
                let ch_start = i;
                let ch = &input[ch_start..];
                if let Some(c) = ch.chars().next() {
                    s.push(c);
                    i += c.len_utf8() - 1; // the loop will add 1
                }
            }
        }
        i += 1;
    }
    Err(ParseSExprError(String::from("unterminated string")))
}

fn parse_bool(input: &str) -> Result<(SExpr, &str), ParseSExprError> {
    if let Some(rest) = input.strip_prefix("#t") {
        // Make sure #t is not part of a longer token like #true (accept #true too)
        if rest.is_empty() || is_delimiter(rest.as_bytes()[0]) {
            return Ok((SExpr::Atom(Atom::Bool(true)), rest));
        }
        if let Some(rest2) = rest.strip_prefix("rue") {
            if rest2.is_empty() || is_delimiter(rest2.as_bytes()[0]) {
                return Ok((SExpr::Atom(Atom::Bool(true)), rest2));
            }
        }
    }
    if let Some(rest) = input.strip_prefix("#f") {
        if rest.is_empty() || is_delimiter(rest.as_bytes()[0]) {
            return Ok((SExpr::Atom(Atom::Bool(false)), rest));
        }
        if let Some(rest2) = rest.strip_prefix("alse") {
            if rest2.is_empty() || is_delimiter(rest2.as_bytes()[0]) {
                return Ok((SExpr::Atom(Atom::Bool(false)), rest2));
            }
        }
    }
    Err(ParseSExprError(alloc::format!(
        "invalid boolean: {}",
        &input[..input.len().min(10)]
    )))
}

fn parse_keyword(input: &str) -> Result<(SExpr, &str), ParseSExprError> {
    debug_assert!(input.starts_with(':'));
    let rest = &input[1..];
    let end = rest
        .find(|c: char| c.is_ascii_whitespace() || c == '(' || c == ')' || c == '"')
        .unwrap_or(rest.len());
    if end == 0 {
        return Err(ParseSExprError(String::from("empty keyword")));
    }
    Ok((
        SExpr::Atom(Atom::Keyword(String::from(&rest[..end]))),
        &rest[end..],
    ))
}

fn parse_num_or_symbol(input: &str) -> Result<(SExpr, &str), ParseSExprError> {
    let end = input
        .find(|c: char| c.is_ascii_whitespace() || c == '(' || c == ')' || c == '"')
        .unwrap_or(input.len());
    if end == 0 {
        return Err(ParseSExprError(String::from("unexpected character")));
    }
    let token = &input[..end];
    let rest = &input[end..];

    // Try to parse as integer
    if let Ok(n) = token.parse::<i64>() {
        return Ok((SExpr::Atom(Atom::Num(n)), rest));
    }

    Ok((SExpr::Atom(Atom::Symbol(String::from(token))), rest))
}

fn is_delimiter(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')' | b'"')
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;

    // -- Existing tests --

    #[test]
    fn atom_size_is_one() {
        let a = SExpr::Atom(Atom::Num(42));
        assert_eq!(a.size(), 1);
    }

    #[test]
    fn list_size() {
        let l = SExpr::List(vec![SExpr::Atom(Atom::Num(1)), SExpr::Atom(Atom::Num(2))]);
        assert_eq!(l.size(), 3);
    }

    #[test]
    fn atom_depth_is_zero() {
        assert_eq!(SExpr::Atom(Atom::Bool(true)).depth(), 0);
    }

    #[test]
    fn nested_depth() {
        let inner = SExpr::List(vec![SExpr::Atom(Atom::Num(1))]);
        let outer = SExpr::List(vec![inner]);
        assert_eq!(outer.depth(), 2);
    }

    #[test]
    fn is_symbol_match() {
        let s = SExpr::Atom(Atom::Symbol("tell".into()));
        assert!(s.is_symbol("tell"));
        assert!(!s.is_symbol("ask"));
    }

    // -- Display tests --

    #[test]
    fn display_symbol() {
        assert_eq!(Atom::Symbol("hello".into()).to_string(), "hello");
        assert_eq!(SExpr::Atom(Atom::Symbol("tell".into())).to_string(), "tell");
    }

    #[test]
    fn display_string() {
        assert_eq!(Atom::Str("hi".into()).to_string(), "\"hi\"");
        assert_eq!(
            Atom::Str("a\"b\\c\n".into()).to_string(),
            "\"a\\\"b\\\\c\\n\""
        );
    }

    #[test]
    fn display_num() {
        assert_eq!(Atom::Num(42).to_string(), "42");
        assert_eq!(Atom::Num(-7).to_string(), "-7");
    }

    #[test]
    fn display_bool() {
        assert_eq!(Atom::Bool(true).to_string(), "#t");
        assert_eq!(Atom::Bool(false).to_string(), "#f");
    }

    #[test]
    fn display_keyword() {
        assert_eq!(Atom::Keyword("key".into()).to_string(), ":key");
    }

    #[test]
    fn display_list() {
        let l = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Str("hi".into())),
        ]);
        assert_eq!(l.to_string(), "(tell \"hi\")");
    }

    #[test]
    fn display_empty_list() {
        assert_eq!(SExpr::List(vec![]).to_string(), "()");
    }

    #[test]
    fn display_nested() {
        let inner = SExpr::List(vec![SExpr::Atom(Atom::Num(1))]);
        let outer = SExpr::List(vec![SExpr::Atom(Atom::Symbol("x".into())), inner]);
        assert_eq!(outer.to_string(), "(x (1))");
    }

    // -- FromStr tests --

    #[test]
    fn parse_symbol() {
        let e: SExpr = "hello".parse().unwrap();
        assert_eq!(e, SExpr::Atom(Atom::Symbol("hello".into())));
    }

    #[test]
    fn parse_number() {
        assert_eq!("42".parse::<SExpr>().unwrap(), SExpr::Atom(Atom::Num(42)));
        assert_eq!("-7".parse::<SExpr>().unwrap(), SExpr::Atom(Atom::Num(-7)));
    }

    #[test]
    fn parse_bool() {
        assert_eq!(
            "#t".parse::<SExpr>().unwrap(),
            SExpr::Atom(Atom::Bool(true))
        );
        assert_eq!(
            "#f".parse::<SExpr>().unwrap(),
            SExpr::Atom(Atom::Bool(false))
        );
        assert_eq!(
            "#true".parse::<SExpr>().unwrap(),
            SExpr::Atom(Atom::Bool(true))
        );
        assert_eq!(
            "#false".parse::<SExpr>().unwrap(),
            SExpr::Atom(Atom::Bool(false))
        );
    }

    #[test]
    fn parse_string() {
        assert_eq!(
            "\"hello\"".parse::<SExpr>().unwrap(),
            SExpr::Atom(Atom::Str("hello".into()))
        );
        assert_eq!(
            "\"a\\\"b\\\\c\\n\"".parse::<SExpr>().unwrap(),
            SExpr::Atom(Atom::Str("a\"b\\c\n".into()))
        );
    }

    #[test]
    fn parse_keyword() {
        assert_eq!(
            ":key".parse::<SExpr>().unwrap(),
            SExpr::Atom(Atom::Keyword("key".into()))
        );
    }

    #[test]
    fn parse_empty_list() {
        assert_eq!("()".parse::<SExpr>().unwrap(), SExpr::List(vec![]));
    }

    #[test]
    fn parse_simple_list() {
        let expected = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Str("hi".into())),
        ]);
        assert_eq!("(tell \"hi\")".parse::<SExpr>().unwrap(), expected);
    }

    #[test]
    fn parse_nested_list() {
        let expected = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("x".into())),
            SExpr::List(vec![SExpr::Atom(Atom::Num(1))]),
        ]);
        assert_eq!("(x (1))".parse::<SExpr>().unwrap(), expected);
    }

    #[test]
    fn parse_error_empty() {
        assert!("".parse::<SExpr>().is_err());
    }

    #[test]
    fn parse_error_unclosed_list() {
        assert!("(a b".parse::<SExpr>().is_err());
    }

    #[test]
    fn parse_error_unterminated_string() {
        assert!("\"abc".parse::<SExpr>().is_err());
    }

    #[test]
    fn parse_error_trailing() {
        assert!("a b".parse::<SExpr>().is_err());
    }

    // -- Round-trip tests --

    #[test]
    fn round_trip_atoms() {
        let cases = vec![
            SExpr::Atom(Atom::Symbol("tell".into())),
            SExpr::Atom(Atom::Num(42)),
            SExpr::Atom(Atom::Num(-7)),
            SExpr::Atom(Atom::Bool(true)),
            SExpr::Atom(Atom::Bool(false)),
            SExpr::Atom(Atom::Keyword("key".into())),
            SExpr::Atom(Atom::Str("hello world".into())),
            SExpr::Atom(Atom::Str("a\"b\\c\n".into())),
        ];
        for expr in cases {
            let s = expr.to_string();
            let parsed: SExpr = s.parse().unwrap();
            assert_eq!(parsed, expr, "round-trip failed for: {s}");
        }
    }

    #[test]
    fn round_trip_lists() {
        let cases = vec![
            SExpr::List(vec![]),
            SExpr::List(vec![
                SExpr::Atom(Atom::Symbol("tell".into())),
                SExpr::Atom(Atom::Str("hi".into())),
                SExpr::Atom(Atom::Num(42)),
            ]),
            SExpr::List(vec![
                SExpr::Atom(Atom::Symbol("x".into())),
                SExpr::List(vec![
                    SExpr::Atom(Atom::Num(1)),
                    SExpr::List(vec![SExpr::Atom(Atom::Bool(true))]),
                ]),
            ]),
        ];
        for expr in cases {
            let s = expr.to_string();
            let parsed: SExpr = s.parse().unwrap();
            assert_eq!(parsed, expr, "round-trip failed for: {s}");
        }
    }

    #[test]
    fn parse_sexpr_error_display() {
        let err = "".parse::<SExpr>().unwrap_err();
        assert!(!err.to_string().is_empty());
    }

    // -- Metrics on complex expressions --

    #[test]
    fn byte_size_string() {
        let e = SExpr::Atom(Atom::Str("hello".into()));
        assert_eq!(e.byte_size(), 5);
    }

    #[test]
    fn byte_size_list() {
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("ab".into())),
            SExpr::Atom(Atom::Num(1)),
        ]);
        assert_eq!(e.byte_size(), 2 + core::mem::size_of::<i64>());
    }

    #[test]
    fn depth_flat_list() {
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Num(1)),
            SExpr::Atom(Atom::Num(2)),
            SExpr::Atom(Atom::Num(3)),
        ]);
        assert_eq!(e.depth(), 1);
    }

    #[test]
    fn size_nested() {
        // (a (b c))  => list(a, list(b, c)) => 1 + 1 + (1 + 1 + 1) = 5
        let e = SExpr::List(vec![
            SExpr::Atom(Atom::Symbol("a".into())),
            SExpr::List(vec![
                SExpr::Atom(Atom::Symbol("b".into())),
                SExpr::Atom(Atom::Symbol("c".into())),
            ]),
        ]);
        assert_eq!(e.size(), 5);
    }
}
