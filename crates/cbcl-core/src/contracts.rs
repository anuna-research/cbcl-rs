//! SPEC-040: pure, bounded, representation-preserving flat contracts.
use crate::{
    sexpr::{Atom, SExpr},
    shape::{ShapeRule, TypeConstraint},
};
use alloc::{collections::BTreeMap, format, string::String, sync::Arc, vec::Vec};
use core::{
    cmp::Ordering,
    hash::{Hash, Hasher},
};
use num_bigint::BigInt;

pub const PROFILE: &str = "cbcl-flat-v1-unicode16";
pub const MAX_TYPES: usize = 128;
pub const MAX_NODES: usize = 512;
pub const MAX_DEPTH: usize = 32;
pub const MAX_PATTERN_BYTES: usize = 1024;
pub const MAX_INPUT_BYTES: usize = 65536;
pub const MAX_NUMERIC_BYTES: usize = 4096;
pub const MAX_LITERAL_BYTES: usize = 65536;
pub const MAX_MEMBERS: usize = 256;
pub const MAX_NFA_BYTES: usize = 262144;
pub const MAX_STATES: usize = 16384;
pub const DEFAULT_WORK: u64 = 1 << 35;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckError {
    Violation(String),
    ResourceLimit,
    InvalidDefinition(String),
}
impl core::fmt::Display for CheckError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Violation(s) => write!(f, "contract violation: {s}"),
            Self::ResourceLimit => f.write_str("resource-limit"),
            Self::InvalidDefinition(s) => write!(f, "invalid contract: {s}"),
        }
    }
}

/// Source is signed; derived programs are private, rebuilt at installation after parsing or deserialization.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Contract {
    source: SExpr,
    #[cfg_attr(feature = "serde", serde(skip))]
    compiled: Option<Arc<Node>>,
}
impl PartialEq for Contract {
    fn eq(&self, other: &Self) -> bool {
        self.source == other.source
    }
}
impl Eq for Contract {}
impl Hash for Contract {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.source.hash(h)
    }
}
impl Contract {
    pub fn unresolved(source: SExpr) -> Self {
        Self {
            source,
            compiled: None,
        }
    }
    pub fn source(&self) -> &SExpr {
        &self.source
    }
    pub fn representation(&self) -> Option<TypeConstraint> {
        self.compiled.as_ref().and_then(|n| n.representation())
    }
    pub fn representations(&self) -> u16 {
        self.compiled.as_ref().map_or(0, |n| n.mask)
    }
    pub fn check(&self, value: &SExpr, available_work: u64) -> Result<(), CheckError> {
        let n = self
            .compiled
            .as_ref()
            .ok_or_else(|| CheckError::InvalidDefinition("not installed".into()))?;
        // Reserve the entire worst-case bound before running any branch.
        if available_work < n.work || !input_fits(value) {
            return Err(CheckError::ResourceLimit);
        }
        n.check(value)
    }
    pub fn required_work(&self) -> Option<u64> {
        self.compiled.as_ref().map(|n| n.work)
    }
}
#[derive(Debug)]
struct Node {
    mask: u16,
    work: u64,
    height: usize,
    kind: Kind,
}
#[derive(Debug)]
enum Kind {
    Builtin(TypeConstraint),
    Named(String, Arc<Node>),
    All(Vec<Arc<Node>>),
    Any(Vec<Arc<Node>>),
    Enum(Vec<Atom>),
    Refined(TypeConstraint, Vec<Predicate>),
}
#[derive(Debug)]
enum Predicate {
    Bound(Op, Atom),
    Length(Vec<(Op, i64)>),
    Pattern(crate::contracts::iregexp::Pattern),
}
#[derive(Debug, Clone, Copy)]
enum Op {
    Gt,
    Ge,
    Lt,
    Le,
}
impl Op {
    fn parse(s: &str) -> Option<Self> {
        Some(match s {
            ">" => Self::Gt,
            ">=" => Self::Ge,
            "<" => Self::Lt,
            "<=" => Self::Le,
            _ => return None,
        })
    }
    fn accepts(self, o: Ordering) -> bool {
        match self {
            Self::Gt => o.is_gt(),
            Self::Ge => !o.is_lt(),
            Self::Lt => o.is_lt(),
            Self::Le => !o.is_gt(),
        }
    }
}
fn symbol(e: &SExpr) -> Option<&str> {
    if let SExpr::Atom(Atom::Symbol(s)) = e {
        Some(s)
    } else {
        None
    }
}
fn list(e: &SExpr) -> Result<&[SExpr], String> {
    if let SExpr::List(v) = e {
        Ok(v)
    } else {
        Err("expected contract list".into())
    }
}
fn mask(t: &TypeConstraint) -> u16 {
    match t {
        TypeConstraint::Integer | TypeConstraint::Nonnegative => 1,
        TypeConstraint::Float => 2,
        TypeConstraint::Decimal => 4,
        TypeConstraint::Number => 7,
        TypeConstraint::String | TypeConstraint::Hlc => 8,
        TypeConstraint::Bool => 16,
        TypeConstraint::Symbol => 32,
        TypeConstraint::Keyword => 64,
        TypeConstraint::List => 128,
        TypeConstraint::Contract(c) => c.compiled.as_ref().map_or(0, |n| n.mask),
    }
}
fn mask_type(m: u16) -> Option<TypeConstraint> {
    Some(match m {
        1 => TypeConstraint::Integer,
        2 => TypeConstraint::Float,
        4 => TypeConstraint::Decimal,
        7 | 3 | 5 | 6 => TypeConstraint::Number,
        8 => TypeConstraint::String,
        16 => TypeConstraint::Bool,
        32 => TypeConstraint::Symbol,
        64 => TypeConstraint::Keyword,
        128 => TypeConstraint::List,
        _ => return None,
    })
}
fn atom_mask(a: &Atom) -> u16 {
    match a {
        Atom::Num(_) => 1,
        Atom::Float(_) => 2,
        Atom::Decimal(_) => 4,
        Atom::Str(_) => 8,
        Atom::Bool(_) => 16,
        Atom::Symbol(_) => 32,
        Atom::Keyword(_) => 64,
    }
}
pub(crate) fn input_fits(e: &SExpr) -> bool {
    fn size(e: &SExpr, depth: usize, left: &mut usize) -> bool {
        if depth > MAX_DEPTH {
            return false;
        }
        let bytes = match e {
            SExpr::Atom(Atom::Str(s) | Atom::Symbol(s) | Atom::Keyword(s)) => s.len() + 1,
            SExpr::Atom(Atom::Decimal(d)) => {
                if d.as_str().len() > MAX_NUMERIC_BYTES {
                    return false;
                }
                d.as_str().len() + 1
            }
            SExpr::Atom(_) => 32,
            SExpr::List(v) => {
                if v.len() > MAX_INPUT_BYTES {
                    return false;
                }
                for x in v {
                    if !size(x, depth + 1, left) {
                        return false;
                    }
                }
                1
            }
        };
        if bytes > *left {
            false
        } else {
            *left -= bytes;
            true
        }
    }
    size(e, 0, &mut { MAX_INPUT_BYTES })
}
impl Node {
    fn representation(&self) -> Option<TypeConstraint> {
        match &self.kind {
            Kind::Builtin(t) => Some(t.clone()),
            Kind::Named(_, n) => n.representation(),
            _ => mask_type(self.mask),
        }
    }
    fn check(&self, v: &SExpr) -> Result<(), CheckError> {
        self.check_cached(v, &mut BTreeMap::new())
    }
    fn check_cached(
        &self,
        v: &SExpr,
        memo: &mut BTreeMap<usize, Result<(), CheckError>>,
    ) -> Result<(), CheckError> {
        let key = self as *const Node as usize;
        if let Some(result) = memo.get(&key) {
            return result.clone();
        }
        let result = self.evaluate(v, memo);
        memo.insert(key, result.clone());
        result
    }
    fn evaluate(
        &self,
        v: &SExpr,
        memo: &mut BTreeMap<usize, Result<(), CheckError>>,
    ) -> Result<(), CheckError> {
        let fail = || CheckError::Violation("value does not satisfy declared rule".into());
        match &self.kind {
            Kind::Builtin(t) => {
                if t.matches_builtin(v) {
                    Ok(())
                } else {
                    Err(fail())
                }
            }
            Kind::Named(name, n) => n.check_cached(v, memo).map_err(|e| match e {
                CheckError::Violation(rule) => CheckError::Violation(format!("{name}: {rule}")),
                e => e,
            }),
            Kind::All(ns) => {
                for n in ns {
                    n.check_cached(v, memo)?
                }
                Ok(())
            }
            Kind::Any(ns) => {
                let mut first = None;
                for n in ns {
                    match n.check_cached(v, memo) {
                        Ok(()) => return Ok(()),
                        Err(e @ CheckError::Violation(_)) => {
                            if first.is_none() {
                                first = Some(e)
                            }
                        }
                        Err(e) => return Err(e),
                    }
                }
                Err(first.unwrap_or_else(fail))
            }
            Kind::Enum(xs) => {
                if matches!(v,SExpr::Atom(a) if xs.contains(a)) {
                    Ok(())
                } else {
                    Err(CheckError::Violation("one-of".into()))
                }
            }
            Kind::Refined(t, ps) => {
                if !t.matches_builtin(v) {
                    return Err(fail());
                }
                for p in ps {
                    let ok = match p {
                        Predicate::Bound(op, b) => {
                            if let SExpr::Atom(a) = v {
                                op.accepts(compare_numeric(a, b).ok_or_else(fail)?)
                            } else {
                                false
                            }
                        }
                        Predicate::Length(bs) => {
                            let n = match v {
                                SExpr::Atom(Atom::Str(s)) => s.chars().count(),
                                SExpr::List(xs) => xs.len(),
                                _ => return Err(fail()),
                            };
                            bs.iter().all(|(op, b)| op.accepts((n as i64).cmp(b)))
                        }
                        Predicate::Pattern(p) => {
                            if let SExpr::Atom(Atom::Str(s)) = v {
                                p.is_match(s)
                            } else {
                                false
                            }
                        }
                    };
                    if !ok {
                        return Err(CheckError::Violation(match p {
                            Predicate::Bound(op, b) => format!("numeric bound {op:?} {b}"),
                            Predicate::Length(_) => "length".into(),
                            Predicate::Pattern(_) => "matches".into(),
                        }));
                    }
                }
                Ok(())
            }
        }
    }
}

/// Compare exact mathematical values, including the exact rational binary64 value.
pub fn compare_numeric(a: &Atom, b: &Atom) -> Option<Ordering> {
    fn rational(a: &Atom) -> Option<(BigInt, BigInt)> {
        match a {
            Atom::Num(n) => Some((BigInt::from(*n), BigInt::from(1))),
            Atom::Decimal(d) => {
                let s = d.as_str();
                let scale = s.split_once('.').map_or(0, |(_, f)| f.len());
                let digits = s.replace('.', "");
                Some((
                    BigInt::parse_bytes(digits.as_bytes(), 10)?,
                    BigInt::from(10).pow(scale.try_into().ok()?),
                ))
            }
            Atom::Float(f) => {
                let bits = f.get().to_bits();
                let exp = ((bits >> 52) & 2047) as i32;
                let mant = (bits & ((1u64 << 52) - 1)) | if exp == 0 { 0 } else { 1u64 << 52 };
                let shift = if exp == 0 { -1074 } else { exp - 1023 - 52 };
                let mut n = BigInt::from(mant);
                if bits >> 63 != 0 {
                    n = -n
                }
                Some(if shift >= 0 {
                    (n << (shift as usize), BigInt::from(1))
                } else {
                    (n, BigInt::from(1) << ((-shift) as usize))
                })
            }
            _ => None,
        }
    }
    let (an, ad) = rational(a)?;
    let (bn, bd) = rational(b)?;
    Some((an * bd).cmp(&(bn * ad)))
}

struct Compiler<'a> {
    definitions: &'a BTreeMap<String, SExpr>,
    ready: BTreeMap<String, Arc<Node>>,
    visiting: Vec<String>,
    nodes: usize,
    literal_bytes: usize,
    patterns: BTreeMap<String, crate::contracts::iregexp::Pattern>,
}
impl<'a> Compiler<'a> {
    fn new(definitions: &'a BTreeMap<String, SExpr>) -> Self {
        Self {
            definitions,
            ready: BTreeMap::new(),
            visiting: Vec::new(),
            nodes: 0,
            literal_bytes: 0,
            patterns: BTreeMap::new(),
        }
    }
    fn named(&mut self, name: &str, depth: usize) -> Result<Arc<Node>, String> {
        if let Some(n) = self.ready.get(name) {
            if depth + n.height > MAX_DEPTH {
                return Err("resource-limit: dependency depth".into());
            }
            return Ok(n.clone());
        }
        if self.visiting.iter().any(|n| n == name) {
            return Err(format!("cyclic type {name}"));
        }
        let source = self
            .definitions
            .get(name)
            .ok_or_else(|| format!("unknown type {name}"))?;
        if !input_fits(source) {
            return Err("resource-limit: contract source".into());
        }
        let source = source.clone();
        self.visiting.push(name.into());
        let node = self.compile(&source, depth + 1)?;
        self.visiting.pop();
        self.ready.insert(name.into(), node.clone());
        Ok(node)
    }
    fn compile(&mut self, e: &SExpr, depth: usize) -> Result<Arc<Node>, String> {
        if !input_fits(e) {
            return Err("resource-limit: contract source".into());
        }
        self.nodes += 1;
        if depth > MAX_DEPTH || self.nodes > MAX_NODES {
            return Err("resource-limit: contract depth/nodes".into());
        }
        if let Some(name) = symbol(e) {
            if let Some(t) = TypeConstraint::from_str(name) {
                return Ok(Arc::new(Node {
                    mask: mask(&t),
                    work: 1,
                    height: 1,
                    kind: Kind::Builtin(t),
                }));
            }
            let target = self.named(name, depth)?;
            return Ok(Arc::new(Node {
                mask: target.mask,
                work: target
                    .work
                    .checked_add(1)
                    .ok_or("resource-limit: work bound")?,
                height: target.height + 1,
                kind: Kind::Named(name.into(), target),
            }));
        }
        let xs = list(e)?;
        let head = xs.first().and_then(symbol).ok_or("missing contract head")?;
        if head == "and" || head == "or" {
            if xs.len() < 3 {
                return Err("and/or require at least two operands".into());
            }
            let mut ns = Vec::new();
            let mut m = if head == "and" { 255 } else { 0 };
            let mut work = 1u64;
            for x in &xs[1..] {
                let n = self.compile(x, depth + 1)?;
                if head == "and" {
                    m &= n.mask
                } else {
                    m |= n.mask
                }
                work = work
                    .checked_add(n.work)
                    .ok_or("resource-limit: work bound")?;
                ns.push(n)
            }
            if m == 0 {
                return Err("disjoint base representations".into());
            }
            return Ok(Arc::new(Node {
                mask: m,
                work,
                height: ns.iter().map(|n| n.height).max().unwrap_or(0) + 1,
                kind: if head == "and" {
                    Kind::All(ns)
                } else {
                    Kind::Any(ns)
                },
            }));
        }
        if head == "one-of" {
            if xs.len() < 2 {
                return Err("empty enumeration".into());
            }
            if xs.len() > MAX_MEMBERS + 1 {
                return Err("resource-limit: enumeration members".into());
            }
            let mut atoms = Vec::new();
            let mut m = 0;
            for x in &xs[1..] {
                let SExpr::Atom(a) = x else {
                    return Err("enumeration requires scalar literals".into());
                };
                if atoms.contains(a) {
                    return Err("duplicate enumeration member".into());
                }
                m |= atom_mask(a);
                atoms.push(a.clone());
            }
            self.add_literals(e)?;
            return Ok(Arc::new(Node {
                mask: m,
                work: (MAX_INPUT_BYTES * atoms.len() + 1) as u64,
                height: 1,
                kind: Kind::Enum(atoms),
            }));
        }
        let t = TypeConstraint::from_str(head).ok_or("unsupported refinement head")?;
        if !matches!(
            t,
            TypeConstraint::String
                | TypeConstraint::List
                | TypeConstraint::Number
                | TypeConstraint::Integer
                | TypeConstraint::Float
                | TypeConstraint::Decimal
        ) || xs.len() < 2
        {
            return Err("invalid refinement domain or arity".into());
        }
        let mut ps = Vec::new();
        let mut all_lengths = Vec::new();
        let mut bounds = Vec::new();
        let mut work = 1u64;
        for x in &xs[1..] {
            let clause = list(x)?;
            let op = clause
                .first()
                .and_then(symbol)
                .ok_or("missing refinement operator")?;
            if op == "matches" && t == TypeConstraint::String {
                let [_, SExpr::Atom(Atom::Str(pattern))] = clause else {
                    return Err("matches requires one string".into());
                };
                let p = if let Some(p) = self.patterns.get(pattern) {
                    p.clone()
                } else {
                    let p = iregexp::Pattern::compile(pattern)?;
                    self.patterns.insert(pattern.clone(), p.clone());
                    p
                };
                work = work
                    .checked_add(p.work())
                    .ok_or("resource-limit: pattern work")?;
                ps.push(Predicate::Pattern(p));
            } else if op == "length" && matches!(t, TypeConstraint::String | TypeConstraint::List) {
                if clause.len() < 2 {
                    return Err("length requires bounds".into());
                }
                let mut bs = Vec::new();
                for b in &clause[1..] {
                    let bslice = list(b)?;
                    let [h, SExpr::Atom(Atom::Num(n))] = bslice else {
                        return Err("length bound requires nonnegative integer".into());
                    };
                    let o = symbol(h)
                        .and_then(Op::parse)
                        .ok_or("invalid length comparator")?;
                    if *n < 0 {
                        return Err("negative length bound".into());
                    }
                    bs.push((o, *n));
                }
                all_lengths.extend(bs.iter().copied());
                work += MAX_INPUT_BYTES as u64 * (bs.len() as u64 + 1);
                ps.push(Predicate::Length(bs));
            } else if mask(&t) & 7 != 0 {
                let o = Op::parse(op).ok_or("invalid numeric comparator")?;
                let [_, SExpr::Atom(a)] = clause else {
                    return Err("bound requires numeric literal".into());
                };
                if atom_mask(a) & 7 == 0 {
                    return Err("bound requires numeric literal".into());
                }
                bounds.push((o, a.clone()));
                ps.push(Predicate::Bound(o, a.clone()));
                work += (MAX_NUMERIC_BYTES * MAX_NUMERIC_BYTES * 16) as u64;
            } else {
                return Err("invalid refinement clause".into());
            }
        }
        validate_bounds(&bounds)?;
        if !all_lengths.is_empty() {
            let mut lo = 0i128;
            let mut hi = i64::MAX as i128;
            for (op, n) in all_lengths {
                match op {
                    Op::Ge => lo = lo.max(n as i128),
                    Op::Gt => lo = lo.max(n as i128 + 1),
                    Op::Le => hi = hi.min(n as i128),
                    Op::Lt => hi = hi.min(n as i128 - 1),
                }
            }
            if lo > hi {
                return Err("empty length domain".into());
            }
        }
        self.add_literals(e)?;
        Ok(Arc::new(Node {
            mask: mask(&t),
            work,
            height: 1,
            kind: Kind::Refined(t, ps),
        }))
    }
    fn add_literals(&mut self, e: &SExpr) -> Result<(), String> {
        let bytes = crate::canonical::canonical_encode(e).len();
        if bytes > MAX_INPUT_BYTES {
            return Err("resource-limit: literal input".into());
        }
        self.literal_bytes += bytes;
        if self.literal_bytes > MAX_LITERAL_BYTES {
            return Err("resource-limit: literal bytes".into());
        }
        Ok(())
    }
}
fn validate_bounds(bs: &[(Op, Atom)]) -> Result<(), String> {
    for (lo, l) in bs {
        if !matches!(lo, Op::Gt | Op::Ge) {
            continue;
        }
        for (hi, h) in bs {
            if !matches!(hi, Op::Lt | Op::Le) {
                continue;
            }
            let c = compare_numeric(l, h).ok_or("invalid bound")?;
            if c.is_gt() || (c.is_eq() && (matches!(lo, Op::Gt) || matches!(hi, Op::Lt))) {
                return Err("empty or reversed numeric interval".into());
            }
        }
    }
    Ok(())
}

/// Installation rebuilds every program from signed source, including unused named definitions.
pub fn install(d: &mut crate::dialect::Dialect) -> Result<(), String> {
    if d.types.len() > MAX_TYPES {
        return Err("resource-limit: type declarations".into());
    }
    for name in d.types.keys() {
        if name.is_empty()
            || name.len() > 48
            || !name.as_bytes()[0].is_ascii_lowercase()
            || !name
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
            || TypeConstraint::from_str(name).is_some()
            || matches!(
                name.as_str(),
                "and" | "or" | "matches" | "length" | "one-of" | "type" | "default"
            )
        {
            return Err(format!("invalid or reserved type name {name}"));
        }
    }
    let mut compiler = Compiler::new(&d.types);
    for name in d.types.keys() {
        compiler.named(name, 0)?;
    }
    fn rules(rs: &mut [ShapeRule], compiler: &mut Compiler<'_>) -> Result<(), String> {
        for r in rs {
            match r {
                ShapeRule::Require {
                    type_constraint,
                    children,
                    ..
                }
                | ShapeRule::Optional {
                    type_constraint,
                    children,
                    ..
                } => {
                    if let Some(TypeConstraint::Contract(c)) = type_constraint {
                        c.compiled = Some(compiler.compile(&c.source, 0)?)
                    }
                    rules(children, compiler)?;
                }
                ShapeRule::MaxDepth(_) => {}
            }
            if let ShapeRule::Optional {
                type_constraint,
                default: Some(v),
                children,
                ..
            } = r
            {
                if let Some(t) = type_constraint {
                    t.check(v, DEFAULT_WORK).map_err(|e| {
                        if e == CheckError::ResourceLimit {
                            "resource-limit: default checking".into()
                        } else {
                            format!("invalid default: {e}")
                        }
                    })?;
                }
                for child in children {
                    crate::shape::check_rule(child, v, DEFAULT_WORK).map_err(|e| {
                        if e.rule == "resource-limit" {
                            "resource-limit: default child checking".into()
                        } else {
                            format!("invalid default child: {e}")
                        }
                    })?;
                }
            }
        }
        Ok(())
    }
    for shape in &mut d.shapes {
        rules(&mut shape.rules, &mut compiler)?;
    }
    Ok(())
}

mod iregexp;

/// The finite conservative representation set for a type (SPEC-040 schema surface).
pub fn representation_names(t: &TypeConstraint) -> Vec<&'static str> {
    let m = mask(t);
    [
        (1, "integer"),
        (2, "float"),
        (4, "decimal"),
        (8, "string"),
        (16, "bool"),
        (32, "symbol"),
        (64, "keyword"),
        (128, "list"),
    ]
    .into_iter()
    .filter_map(|(bit, name)| if m & bit != 0 { Some(name) } else { None })
    .collect()
}
pub fn type_schema(
    d: &crate::dialect::Dialect,
) -> Result<Vec<(String, SExpr, Vec<&'static str>)>, String> {
    let mut compiler = Compiler::new(&d.types);
    let mut out = Vec::new();
    for (name, source) in &d.types {
        let n = compiler.named(name, 0)?;
        let names = [
            (1, "integer"),
            (2, "float"),
            (4, "decimal"),
            (8, "string"),
            (16, "bool"),
            (32, "symbol"),
            (64, "keyword"),
            (128, "list"),
        ]
        .into_iter()
        .filter_map(|(b, s)| if n.mask & b != 0 { Some(s) } else { None })
        .collect();
        out.push((name.clone(), source.clone(), names));
    }
    Ok(out)
}
