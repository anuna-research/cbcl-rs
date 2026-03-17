//! Hand-rolled recursive-descent S-expression parser.
//!
//! O(n) time complexity, no backtracking, fuel-bounded (ADR-001).
//! Mirrors `Parser.lean` from the Lean 4 proof library.

#![forbid(unsafe_code)]

use alloc::string::String;
use alloc::vec::Vec;
use cbcl_core::sexpr::{Atom, SExpr};
use core::fmt;

/// Parser errors with source location (ADR-002).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedChar {
        offset: usize,
        found: char,
        expected: &'static str,
    },
    UnexpectedEof {
        offset: usize,
        expected: &'static str,
    },
    FuelExhausted {
        offset: usize,
    },
    InvalidEscape {
        offset: usize,
        sequence: char,
    },
    IntegerOverflow {
        offset: usize,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedChar {
                offset,
                found,
                expected,
            } => {
                write!(
                    f,
                    "at byte {offset}: unexpected '{found}', expected {expected}"
                )
            }
            ParseError::UnexpectedEof { offset, expected } => {
                write!(
                    f,
                    "at byte {offset}: unexpected end of input, expected {expected}"
                )
            }
            ParseError::FuelExhausted { offset } => {
                write!(f, "at byte {offset}: fuel exhausted")
            }
            ParseError::InvalidEscape { offset, sequence } => {
                write!(
                    f,
                    "at byte {offset}: invalid escape sequence '\\{sequence}'"
                )
            }
            ParseError::IntegerOverflow { offset } => {
                write!(f, "at byte {offset}: integer overflow")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {}

/// Parse an S-expression from input text (REQ-040).
///
/// `fuel` defaults to input byte length if `None`.
pub fn parse(input: &str) -> Result<SExpr, ParseError> {
    parse_with_fuel(input, None)
}

/// Parse with explicit fuel limit (REQ-043).
pub fn parse_with_fuel(input: &str, fuel: Option<usize>) -> Result<SExpr, ParseError> {
    #[cfg(feature = "tracing")]
    let _span = tracing::info_span!("parse_duration_ms", input_len = input.len()).entered();

    let mut state = ParserState::new(input, fuel);
    state.skip_whitespace();
    let expr = state.parse_expr()?;
    state.skip_whitespace();
    if state.pos < state.input.len() {
        return Err(ParseError::UnexpectedChar {
            offset: state.pos,
            found: state.input[state.pos..].chars().next().unwrap(),
            expected: "end of input",
        });
    }
    Ok(expr)
}

struct ParserState<'a> {
    input: &'a str,
    pos: usize,
    fuel: usize,
}

impl<'a> ParserState<'a> {
    fn new(input: &'a str, fuel: Option<usize>) -> Self {
        Self {
            input,
            pos: 0,
            fuel: fuel.unwrap_or(input.len().max(1)),
        }
    }

    fn consume_fuel(&mut self) -> Result<(), ParseError> {
        if self.fuel == 0 {
            return Err(ParseError::FuelExhausted { offset: self.pos });
        }
        self.fuel -= 1;
        Ok(())
    }

    fn peek(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_ascii_whitespace() {
                self.advance();
            } else if ch == ';' {
                // Skip line comments
                while let Some(c) = self.advance() {
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn parse_expr(&mut self) -> Result<SExpr, ParseError> {
        self.consume_fuel()?;
        self.skip_whitespace();

        match self.peek() {
            None => Err(ParseError::UnexpectedEof {
                offset: self.pos,
                expected: "expression",
            }),
            Some('(') => self.parse_list(),
            Some('"') => self.parse_string(),
            Some('#') => self.parse_bool(),
            Some(':') => self.parse_keyword(),
            Some(ch) if ch == '-' || ch.is_ascii_digit() => self.parse_number_or_symbol(),
            Some(_) => self.parse_symbol(),
        }
    }

    fn parse_list(&mut self) -> Result<SExpr, ParseError> {
        self.advance(); // consume '('
        let mut items = Vec::new();
        loop {
            self.skip_whitespace();
            match self.peek() {
                None => {
                    return Err(ParseError::UnexpectedEof {
                        offset: self.pos,
                        expected: "')'",
                    })
                }
                Some(')') => {
                    self.advance();
                    return Ok(SExpr::List(items));
                }
                _ => items.push(self.parse_expr()?),
            }
        }
    }

    fn parse_string(&mut self) -> Result<SExpr, ParseError> {
        self.advance(); // consume opening '"'
        let mut s = String::new();
        loop {
            match self.advance() {
                None => {
                    return Err(ParseError::UnexpectedEof {
                        offset: self.pos,
                        expected: "closing '\"'",
                    })
                }
                Some('"') => return Ok(SExpr::Atom(Atom::Str(s))),
                Some('\\') => {
                    let offset = self.pos;
                    match self.advance() {
                        Some('n') => s.push('\n'),
                        Some('r') => s.push('\r'),
                        Some('t') => s.push('\t'),
                        Some('\\') => s.push('\\'),
                        Some('"') => s.push('"'),
                        Some(c) => {
                            return Err(ParseError::InvalidEscape {
                                offset,
                                sequence: c,
                            })
                        }
                        None => {
                            return Err(ParseError::UnexpectedEof {
                                offset,
                                expected: "escape character",
                            })
                        }
                    }
                }
                Some(c) => s.push(c),
            }
        }
    }

    fn parse_bool(&mut self) -> Result<SExpr, ParseError> {
        let offset = self.pos;
        self.advance(); // consume '#'
        match self.advance() {
            Some('t') => Ok(SExpr::Atom(Atom::Bool(true))),
            Some('f') => Ok(SExpr::Atom(Atom::Bool(false))),
            Some(c) => Err(ParseError::UnexpectedChar {
                offset: offset + 1,
                found: c,
                expected: "'t' or 'f'",
            }),
            None => Err(ParseError::UnexpectedEof {
                offset: offset + 1,
                expected: "'t' or 'f'",
            }),
        }
    }

    fn parse_keyword(&mut self) -> Result<SExpr, ParseError> {
        self.advance(); // consume ':'
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if is_symbol_char(ch) {
                self.advance();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(ParseError::UnexpectedEof {
                offset: start,
                expected: "keyword name",
            });
        }
        Ok(SExpr::Atom(Atom::Keyword(String::from(
            &self.input[start..self.pos],
        ))))
    }

    fn parse_number_or_symbol(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        let offset = self.pos;

        // Check for negative number: '-' followed by digit
        if self.peek() == Some('-') {
            let next_start = self.pos + 1;
            if next_start < self.input.len() {
                let next_ch = self.input[next_start..].chars().next();
                if let Some(c) = next_ch {
                    if c.is_ascii_digit() {
                        return self.parse_integer(start, offset);
                    }
                }
            }
            // Just a '-' symbol or '-' followed by non-digit
            return self.parse_symbol();
        }

        self.parse_integer(start, offset)
    }

    fn parse_integer(&mut self, start: usize, offset: usize) -> Result<SExpr, ParseError> {
        // Consume all valid integer chars
        while let Some(ch) = self.peek() {
            if ch == '-' || ch.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }
        let text = &self.input[start..self.pos];
        match text.parse::<i64>() {
            Ok(n) => Ok(SExpr::Atom(Atom::Num(n))),
            Err(_) => Err(ParseError::IntegerOverflow { offset }),
        }
    }

    fn parse_symbol(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if is_symbol_char(ch) {
                self.advance();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(ParseError::UnexpectedChar {
                offset: self.pos,
                found: self.peek().unwrap_or('\0'),
                expected: "symbol",
            });
        }
        Ok(SExpr::Atom(Atom::Symbol(String::from(
            &self.input[start..self.pos],
        ))))
    }
}

fn is_symbol_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric()
        || ch == '_'
        || ch == '-'
        || ch == '.'
        || ch == '/'
        || ch == '!'
        || ch == '?'
        || ch == '+'
        || ch == '*'
        || ch == '<'
        || ch == '>'
        || ch == '='
        || ch == '@'
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn parse_integer() {
        assert_eq!(parse("42"), Ok(SExpr::Atom(Atom::Num(42))));
        assert_eq!(parse("-7"), Ok(SExpr::Atom(Atom::Num(-7))));
    }

    #[test]
    fn parse_symbol() {
        assert_eq!(
            parse("hello"),
            Ok(SExpr::Atom(Atom::Symbol("hello".into())))
        );
    }

    #[test]
    fn parse_string() {
        assert_eq!(parse("\"hi\""), Ok(SExpr::Atom(Atom::Str("hi".into()))));
    }

    #[test]
    fn parse_string_escapes() {
        assert_eq!(
            parse("\"a\\nb\""),
            Ok(SExpr::Atom(Atom::Str("a\nb".into())))
        );
    }

    #[test]
    fn parse_bool() {
        assert_eq!(parse("#t"), Ok(SExpr::Atom(Atom::Bool(true))));
        assert_eq!(parse("#f"), Ok(SExpr::Atom(Atom::Bool(false))));
    }

    #[test]
    fn parse_keyword() {
        assert_eq!(parse(":key"), Ok(SExpr::Atom(Atom::Keyword("key".into()))));
    }

    #[test]
    fn parse_list() {
        assert_eq!(
            parse("(tell \"hi\")"),
            Ok(SExpr::List(vec![
                SExpr::Atom(Atom::Symbol("tell".into())),
                SExpr::Atom(Atom::Str("hi".into())),
            ]))
        );
    }

    #[test]
    fn parse_nested_list() {
        assert_eq!(
            parse("(a (b c))"),
            Ok(SExpr::List(vec![
                SExpr::Atom(Atom::Symbol("a".into())),
                SExpr::List(vec![
                    SExpr::Atom(Atom::Symbol("b".into())),
                    SExpr::Atom(Atom::Symbol("c".into())),
                ]),
            ]))
        );
    }

    #[test]
    fn parse_empty_list() {
        assert_eq!(parse("()"), Ok(SExpr::List(vec![])));
    }

    #[test]
    fn fuel_exhaustion() {
        let result = parse_with_fuel("(a b c d e f g h)", Some(3));
        assert!(matches!(result, Err(ParseError::FuelExhausted { .. })));
    }

    #[test]
    fn round_trip() {
        let input = "(tell \"hello world\" 42 #t :key)";
        let expr = parse(input).unwrap();
        let serialized = cbcl_core::serializer::serialize(&expr);
        let reparsed = parse(&serialized).unwrap();
        assert_eq!(expr, reparsed);
    }
}
