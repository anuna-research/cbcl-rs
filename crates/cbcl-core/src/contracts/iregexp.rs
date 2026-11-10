//! Checking recognizer for RFC 9485 Figure 1, adapted to a bounded Thompson VM.
use super::{MAX_DEPTH, MAX_INPUT_BYTES, MAX_NFA_BYTES, MAX_PATTERN_BYTES, MAX_STATES};
use alloc::{
    format,
    string::{String, ToString},
    sync::Arc,
};
use regex_automata::nfa::thompson::{self, pikevm::PikeVM};
#[derive(Debug, Clone)]
pub(super) struct Pattern {
    vm: Arc<PikeVM>,
    states: usize,
}
impl Pattern {
    pub fn compile(source: &str) -> Result<Self, String> {
        if source.len() > MAX_PATTERN_BYTES {
            return Err("resource-limit: pattern bytes".into());
        }
        let mut p = Recognizer {
            chars: source.chars().collect(),
            pos: 0,
        };
        let translated = p.regexp(0)?;
        if p.pos != p.chars.len() {
            return Err("invalid I-Regexp trailing syntax".into());
        }
        let hir = regex_syntax::ParserBuilder::new()
            .nest_limit((MAX_DEPTH * 4) as u32)
            .build()
            .parse(&format!(r"\A(?:{translated})\z"))
            .map_err(|_| "invalid I-Regexp range or repetition")?;
        let nfa = thompson::Compiler::new()
            .configure(thompson::Config::new().nfa_size_limit(Some(MAX_NFA_BYTES * 64)))
            .build_from_hir(&hir)
            .map_err(|_| "resource-limit: compiled pattern")?;
        // Fixed-width accounting is part of the profile. Native allocation layout
        // (notably usize width) must never decide profile conformance.
        use thompson::State;
        let portable_cost: usize = nfa
            .states()
            .iter()
            .map(|state| match state {
                State::Sparse(s) => 16 + 8 * s.transitions.len(),
                State::Dense(s) => 16 + 4 * s.transitions.len(),
                State::Union { alternates } => 16 + 4 * alternates.len(),
                State::Fail | State::Match { .. } => 16,
                _ => 32,
            })
            .sum();
        if portable_cost > MAX_NFA_BYTES {
            return Err("resource-limit: portable compiled cost".into());
        }
        let states = nfa.states().len();
        if states > MAX_STATES {
            return Err("resource-limit: compiled states".into());
        }
        let vm = PikeVM::new_from_nfa(nfa).map_err(|_| "unsupported regex capability")?;
        Ok(Self {
            vm: Arc::new(vm),
            states,
        })
    }
    pub fn work(&self) -> u64 {
        (self.states as u64 + 1) * (MAX_INPUT_BYTES as u64 + 1) * 16
    }
    pub fn is_match(&self, text: &str) -> bool {
        let mut cache = self.vm.create_cache();
        self.vm.is_match(&mut cache, text)
    }
}
struct Recognizer {
    chars: alloc::vec::Vec<char>,
    pos: usize,
}
impl Recognizer {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }
    fn take(&mut self) -> Result<char, String> {
        let c = self.peek().ok_or("incomplete I-Regexp")?;
        self.pos += 1;
        Ok(c)
    }
    fn expect(&mut self, c: char) -> Result<(), String> {
        if self.take()? == c {
            Ok(())
        } else {
            Err("invalid I-Regexp delimiter".into())
        }
    }
    fn literal(c: char) -> String {
        format!(r"\x{{{:x}}}", c as u32)
    }
    fn regexp(&mut self, depth: usize) -> Result<String, String> {
        if depth > MAX_DEPTH {
            return Err("resource-limit: pattern nesting".into());
        }
        let mut out = String::new();
        while let Some(c) = self.peek() {
            if c == ')' {
                break;
            }
            if c == '|' {
                self.pos += 1;
                out.push('|');
                continue;
            }
            let atom = match c {
                '(' => {
                    self.pos += 1;
                    let inside = self.regexp(depth + 1)?;
                    self.expect(')')?;
                    format!("(?:{inside})")
                }
                '[' => self.class()?,
                '.' => {
                    self.pos += 1;
                    String::from(r"[^\n\r]")
                }
                '\\' => self.escape(true)?,
                '*' | '+' | '?' | '{' | '}' | ']' => return Err("invalid I-Regexp atom".into()),
                _ => {
                    self.pos += 1;
                    Self::literal(c)
                }
            };
            out.push_str(&atom);
            match self.peek() {
                Some('*' | '+' | '?') => out.push(self.take()?),
                Some('{') => {
                    self.pos += 1;
                    let lo = self.count()?;
                    out.push('{');
                    out.push_str(&lo.to_string());
                    if self.peek() == Some(',') {
                        self.pos += 1;
                        out.push(',');
                        if self.peek() != Some('}') {
                            let hi = self.count()?;
                            if hi < lo {
                                return Err("invalid repetition bounds".into());
                            }
                            out.push_str(&hi.to_string())
                        }
                    }
                    self.expect('}')?;
                    out.push('}');
                }
                _ => {}
            }
        }
        Ok(out)
    }
    fn count(&mut self) -> Result<u32, String> {
        let mut n = 0u32;
        let start = self.pos;
        while let Some(c @ '0'..='9') = self.peek() {
            self.pos += 1;
            n = n
                .checked_mul(10)
                .and_then(|n| n.checked_add(c as u32 - '0' as u32))
                .ok_or("resource-limit: repetition count")?;
        }
        if self.pos == start {
            return Err("missing repetition count".into());
        }
        Ok(n)
    }
    fn escape(&mut self, property: bool) -> Result<String, String> {
        self.expect('\\')?;
        let c = self.take()?;
        if property && (c == 'p' || c == 'P') {
            self.expect('{')?;
            let mut cat = String::new();
            while self.peek() != Some('}') {
                cat.push(self.take()?);
                if cat.len() > 2 {
                    return Err("unsupported Unicode property".into());
                }
            }
            self.expect('}')?;
            if !matches!(
                cat.as_str(),
                "L" | "Ll"
                    | "Lm"
                    | "Lo"
                    | "Lt"
                    | "Lu"
                    | "M"
                    | "Mc"
                    | "Me"
                    | "Mn"
                    | "N"
                    | "Nd"
                    | "Nl"
                    | "No"
                    | "P"
                    | "Pc"
                    | "Pd"
                    | "Pe"
                    | "Pf"
                    | "Pi"
                    | "Po"
                    | "Ps"
                    | "Z"
                    | "Zl"
                    | "Zp"
                    | "Zs"
                    | "S"
                    | "Sc"
                    | "Sk"
                    | "Sm"
                    | "So"
                    | "C"
                    | "Cc"
                    | "Cf"
                    | "Cn"
                    | "Co"
            ) {
                return Err("unsupported Unicode category".into());
            }
            return Ok(format!("\\{c}{{{cat}}}"));
        }
        let decoded = match c {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '(' | ')' | '*' | '+' | '-' | '.' | '?' | '[' | '\\' | ']' | '^' | '{' | '|' | '}' => c,
            _ => return Err("invalid I-Regexp escape".into()),
        };
        Ok(Self::literal(decoded))
    }
    fn ccchar(&mut self) -> Result<String, String> {
        match self.peek() {
            Some('\\') => self.escape(false),
            Some('-' | '[' | ']') | None => Err("invalid I-Regexp class character".into()),
            Some(c) => {
                self.pos += 1;
                Ok(Self::literal(c))
            }
        }
    }
    fn class(&mut self) -> Result<String, String> {
        self.expect('[')?;
        let mut out = String::from("[");
        if self.peek() == Some('^') {
            self.pos += 1;
            out.push('^')
        }
        let mut count = 0;
        if self.peek() == Some('-') {
            self.pos += 1;
            out.push_str(&Self::literal('-'));
            count += 1
        }
        while self.peek() != Some(']') {
            if self.peek().is_none() {
                return Err("unclosed I-Regexp class".into());
            }
            if self.peek() == Some('-') && self.chars.get(self.pos + 1) == Some(&']') {
                self.pos += 1;
                out.push_str(&Self::literal('-'));
                count += 1;
                break;
            }
            if self.peek() == Some('\\') && matches!(self.chars.get(self.pos + 1), Some('p' | 'P'))
            {
                out.push_str(&self.escape(true)?);
                count += 1;
                continue;
            }
            out.push_str(&self.ccchar()?);
            count += 1;
            if self.peek() == Some('-') && self.chars.get(self.pos + 1) != Some(&']') {
                self.pos += 1;
                out.push('-');
                out.push_str(&self.ccchar()?)
            }
        }
        self.expect(']')?;
        if count == 0 {
            return Err("empty I-Regexp class".into());
        }
        out.push(']');
        Ok(out)
    }
}
