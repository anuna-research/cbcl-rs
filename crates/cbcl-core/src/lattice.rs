//! The state kernel as lattice terms (SPEC-038 CON-3800, first slice).
//!
//! Every shipped R7 rule head except `progress` and `bounded-counter` is a
//! *lift*: a per-act contribution `g` joined over the selected accepted acts,
//! followed by a post-map to the displayed value. The join half is a
//! join-homomorphism from `(℘(A), ⊆)` — `σ(A₁ ∪ A₂) = σ(A₁) ⊔ σ(A₂)` — which is
//! why the fold is a set function and why replicas merge by union only. The
//! post-map is where monotonicity ends: `size` and membership are monotone,
//! a winner's value or a difference is a revisable snapshot (SPEC-038 REQ-3805).
//!
//! This module does not replace [`crate::state::fold`]; it *denotes* each rule
//! as a term and is checked against the fold differentially (TEST-3800). The
//! two closure heads return `None` from [`factor`] not because the join law
//! fails — with the identity contribution every head is a morphism into the
//! set of acts under union — but because no *summarising* carrier exists for
//! them: an act's protocol position or an operation's validity depends on its
//! cited ancestors, so their post-map is a least fixed point over citations
//! and nothing smaller than the act set can be joined per contribution
//! (SPEC-038 REQ-3808).
//!
//! Supersession fits the algebra by carrying two grow-only halves: `W`, the
//! writes keyed by their group, and `R`, the `(group, address)` pairs a
//! replacer of the same group names in `:replaces`. `current = W \ R` is a
//! projection, not a join.
//!
//! The morphism law is stated on causally closed accepted sets (SPEC-038
//! REQ-3800): a domain selector reads the opener's `initial` field, so two
//! halves that separate the opener from the acts it governs are not both
//! histories. Admission only ever produces closed sets.

#![forbid(unsafe_code)]

use crate::hlc::Hlc;
use crate::sexpr::{Atom, SExpr};
use crate::state::{Act, Rule, StateClause, Value, RESERVED_REPLACES};
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

/// The arbitration key of a clocked write: HLC, then signer, then address
/// (SPEC-035). A chain: its join is `max`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Key {
    pub hlc: Hlc,
    pub signer: String,
    pub address: String,
}

/// The `initial` carrier: no opener, exactly one, or a conflict with evidence
/// (SPEC-038 ADR-3803). `⊥ ⊔ x = x`; two different openers join to ⊤.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sole {
    Bot,
    One(String, Option<Value>),
    Top(BTreeSet<String>),
}

/// Lattice carriers. Every variant is a join-semilattice with a bottom; joins
/// are only defined between the same variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum L {
    /// Boolean under `or`.
    Bool(bool),
    /// Addresses under union.
    Addrs(BTreeSet<String>),
    /// Distinct values keyed by their canonical rendering, under union.
    Vals(BTreeMap<String, Value>),
    /// Address → contribution (`events`), under union.
    Entries(BTreeMap<String, Value>),
    /// Address → integer amount, under union.
    Amounts(BTreeMap<String, i128>),
    /// The greatest clocked candidate.
    Chain(Option<(Key, Option<Value>)>),
    /// Writes: address → group rendering.
    Writes(BTreeMap<String, String>),
    /// Replaced: (group rendering, address).
    Replaced(BTreeSet<(String, String)>),
    /// The unique-opener carrier.
    Sole(Sole),
    Pair(Box<L>, Box<L>),
}

impl L {
    /// The join. Mismatched variants join to the left operand; `factor` never
    /// produces them.
    pub fn join(self, other: L) -> L {
        match (self, other) {
            (L::Bool(a), L::Bool(b)) => L::Bool(a || b),
            (L::Addrs(mut a), L::Addrs(b)) => {
                a.extend(b);
                L::Addrs(a)
            }
            (L::Vals(mut a), L::Vals(b)) => {
                a.extend(b);
                L::Vals(a)
            }
            (L::Entries(mut a), L::Entries(b)) => {
                a.extend(b);
                L::Entries(a)
            }
            (L::Amounts(mut a), L::Amounts(b)) => {
                a.extend(b);
                L::Amounts(a)
            }
            (L::Chain(a), L::Chain(b)) => L::Chain(match (a, b) {
                (None, x) | (x, None) => x,
                (Some(x), Some(y)) => Some(if y.0 > x.0 { y } else { x }),
            }),
            (L::Writes(mut a), L::Writes(b)) => {
                a.extend(b);
                L::Writes(a)
            }
            (L::Replaced(mut a), L::Replaced(b)) => {
                a.extend(b);
                L::Replaced(a)
            }
            (L::Sole(a), L::Sole(b)) => L::Sole(match (a, b) {
                (Sole::Bot, x) | (x, Sole::Bot) => x,
                (Sole::One(a, v), Sole::One(b, w)) => {
                    if a == b && v == w {
                        Sole::One(a, v)
                    } else {
                        Sole::Top([a, b].into_iter().collect())
                    }
                }
                (Sole::Top(mut t), Sole::One(a, _)) | (Sole::One(a, _), Sole::Top(mut t)) => {
                    t.insert(a);
                    Sole::Top(t)
                }
                (Sole::Top(mut t), Sole::Top(u)) => {
                    t.extend(u);
                    Sole::Top(t)
                }
            }),
            (L::Pair(a, b), L::Pair(c, d)) => L::Pair(Box::new(a.join(*c)), Box::new(b.join(*d))),
            (left, _) => left,
        }
    }
}

/// How writes are grouped for supersession and for keyed displays.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Group {
    None,
    Signer,
    Field(String),
}

/// A per-act contribution into a carrier (CON-3800 `contribute`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Contribute {
    Flag,
    Address,
    Field(String),
    Entry(String),
    Amount(String),
    Clocked { value: String, clock: String },
    Write(Group),
    Replaced(Group),
    Sole(String),
}

/// Which accepted acts a lift ranges over. `raw` skips domain filters, as the
/// `initial` head does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Select {
    pub verb: String,
    pub raw: bool,
}

/// A term of the algebra (CON-3800 `term`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Lift(Vec<Select>, Contribute),
    Pair(Box<Term>, Box<Term>),
    /// Reads an earlier field of the same clause; no lattice of its own.
    Earlier(String),
}

/// The post-map from a carrier to the displayed value (CON-3800 `post`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Post {
    Identity,
    Size,
    Difference,
    Current(Box<Post>),
    GroupBy(Group, Box<Post>),
    PickLww { value: String, clock: String },
    Distinct(String),
    Histogram,
    Sum,
}

/// A factored rule: a term and its post-map.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factored {
    pub term: Term,
    pub post: Post,
}

fn sel(verb: &str) -> Select {
    Select {
        verb: String::from(verb),
        raw: false,
    }
}

/// The denotation of a shipped head as a term (SPEC-038 ADR-3804). `None`
/// for the two closure heads (REQ-3808).
pub fn factor(rule: &Rule) -> Option<Factored> {
    let lift = |verbs: Vec<Select>, c: Contribute| Term::Lift(verbs, c);
    let pair = |a: Term, b: Term| Term::Pair(Box::new(a), Box::new(b));
    let f = |term, post| Some(Factored { term, post });
    match rule {
        Rule::BoundedCounter(_) | Rule::Progress { .. } => None,
        Rule::Exists { verb } => f(
            lift(alloc::vec![sel(verb)], Contribute::Flag),
            Post::Identity,
        ),
        Rule::Count { verb } => f(
            lift(alloc::vec![sel(verb)], Contribute::Address),
            Post::Size,
        ),
        Rule::Events { verb, key } => f(
            lift(alloc::vec![sel(verb)], Contribute::Entry(key.clone())),
            Post::Identity,
        ),
        Rule::SetUnion { verb, key } => f(
            lift(alloc::vec![sel(verb)], Contribute::Field(key.clone())),
            Post::Identity,
        ),
        Rule::Values { verb, key } => f(
            pair(
                lift(alloc::vec![sel(verb)], Contribute::Write(Group::None)),
                lift(alloc::vec![sel(verb)], Contribute::Replaced(Group::None)),
            ),
            Post::Current(Box::new(Post::Distinct(key.clone()))),
        ),
        Rule::ValuesPerKey {
            verb,
            key,
            value,
            delete,
        } => {
            let mut replacers = alloc::vec![sel(verb)];
            if let Some(d) = delete {
                replacers.push(sel(d));
            }
            f(
                pair(
                    lift(
                        alloc::vec![sel(verb)],
                        Contribute::Write(Group::Field(key.clone())),
                    ),
                    lift(replacers, Contribute::Replaced(Group::Field(key.clone()))),
                ),
                Post::Current(Box::new(Post::GroupBy(
                    Group::Field(key.clone()),
                    Box::new(Post::Distinct(value.clone())),
                ))),
            )
        }
        Rule::ObservedSet { add, remove, key } => f(
            pair(
                lift(
                    alloc::vec![sel(add)],
                    Contribute::Write(Group::Field(key.clone())),
                ),
                lift(
                    alloc::vec![sel(add), sel(remove)],
                    Contribute::Replaced(Group::Field(key.clone())),
                ),
            ),
            Post::Current(Box::new(Post::Distinct(key.clone()))),
        ),
        Rule::Counter { inc, dec, key } => f(
            pair(
                lift(alloc::vec![sel(inc)], Contribute::Amount(key.clone())),
                lift(alloc::vec![sel(dec)], Contribute::Amount(key.clone())),
            ),
            Post::Difference,
        ),
        Rule::Histogram { field } => f(Term::Earlier(field.clone()), Post::Histogram),
        Rule::Sum { field } => f(Term::Earlier(field.clone()), Post::Sum),
        Rule::LwwRegister { verb, key, clock } => f(
            lift(
                alloc::vec![sel(verb)],
                Contribute::Clocked {
                    value: key.clone(),
                    clock: clock.clone(),
                },
            ),
            Post::Identity,
        ),
        Rule::LwwPerSigner { verb, key, clock } => f(
            pair(
                lift(alloc::vec![sel(verb)], Contribute::Write(Group::Signer)),
                lift(alloc::vec![sel(verb)], Contribute::Replaced(Group::Signer)),
            ),
            Post::Current(Box::new(Post::GroupBy(
                Group::Signer,
                Box::new(Post::PickLww {
                    value: key.clone(),
                    clock: clock.clone(),
                }),
            ))),
        ),
        Rule::LwwMap {
            verb,
            key,
            value,
            clock,
            delete,
        } => {
            let mut replacers = alloc::vec![sel(verb)];
            if let Some(d) = delete {
                replacers.push(sel(d));
            }
            f(
                pair(
                    lift(
                        alloc::vec![sel(verb)],
                        Contribute::Write(Group::Field(key.clone())),
                    ),
                    lift(replacers, Contribute::Replaced(Group::Field(key.clone()))),
                ),
                Post::Current(Box::new(Post::GroupBy(
                    Group::Field(key.clone()),
                    Box::new(Post::PickLww {
                        value: value.clone(),
                        clock: clock.clone(),
                    }),
                ))),
            )
        }
        Rule::Initial { verb, key } => f(
            lift(
                alloc::vec![Select {
                    verb: verb.clone(),
                    raw: true,
                }],
                Contribute::Sole(key.clone()),
            ),
            Post::Identity,
        ),
    }
}

/// The accepted acts, unique by address, with the clause's domain filters
/// resolved (SPEC-019 ADR-1909: domains read list-valued opener fields).
pub struct Ctx<'a> {
    acts: BTreeMap<String, &'a Act>,
    domains: Vec<(String, String, Vec<Value>)>,
}

impl<'a> Ctx<'a> {
    pub fn new(clause: &StateClause, acts: &'a [Act]) -> Ctx<'a> {
        let mut unique: BTreeMap<String, &Act> = BTreeMap::new();
        for a in acts {
            unique.entry(a.address.clone()).or_insert(a);
        }
        let bare = Ctx {
            acts: unique.clone(),
            domains: Vec::new(),
        };
        let mut domains = Vec::new();
        for (verb, key, field) in clause.domains() {
            let allowed = match clause.rule_of(field).and_then(factor) {
                Some(fd) => match bare.display(&fd, &[]) {
                    Value::List(items) | Value::Set(items) => items,
                    _ => Vec::new(),
                },
                None => Vec::new(),
            };
            domains.push((String::from(verb), String::from(key), allowed));
        }
        Ctx {
            acts: unique,
            domains,
        }
    }

    fn field(act: &Act, key: &str) -> Option<Value> {
        act.fields.get(key).map(Value::from_sexpr)
    }

    fn in_domain(&self, act: &Act) -> bool {
        self.domains.iter().all(|(v, key, allowed)| {
            if *v != act.verb {
                return true;
            }
            match Self::field(act, key) {
                Some(val) => {
                    let r = val.render();
                    allowed.iter().any(|x| x.render() == r)
                }
                None => false,
            }
        })
    }

    fn selected(&self, s: &Select) -> impl Iterator<Item = &'a Act> + '_ {
        let verb = s.verb.clone();
        let raw = s.raw;
        self.acts
            .values()
            .copied()
            .filter(move |a| a.verb == verb && (raw || self.in_domain(a)))
    }

    fn group_key(act: &Act, group: &Group) -> String {
        match group {
            Group::None => String::new(),
            Group::Signer => act.signer.clone(),
            Group::Field(k) => Self::field(act, k).map(|v| v.render()).unwrap_or_default(),
        }
    }

    fn bottom(c: &Contribute) -> L {
        match c {
            Contribute::Flag => L::Bool(false),
            Contribute::Address => L::Addrs(BTreeSet::new()),
            Contribute::Field(_) => L::Vals(BTreeMap::new()),
            Contribute::Entry(_) => L::Entries(BTreeMap::new()),
            Contribute::Amount(_) => L::Amounts(BTreeMap::new()),
            Contribute::Clocked { .. } => L::Chain(None),
            Contribute::Write(_) => L::Writes(BTreeMap::new()),
            Contribute::Replaced(_) => L::Replaced(BTreeSet::new()),
            Contribute::Sole(_) => L::Sole(Sole::Bot),
        }
    }

    /// `g(a)`: one act's contribution.
    fn contribute(act: &Act, c: &Contribute) -> L {
        match c {
            Contribute::Flag => L::Bool(true),
            Contribute::Address => L::Addrs([act.address.clone()].into_iter().collect()),
            Contribute::Field(k) => L::Vals(
                Self::field(act, k)
                    .map(|v| [(v.render(), v)].into_iter().collect())
                    .unwrap_or_default(),
            ),
            Contribute::Entry(k) => L::Entries(
                Self::field(act, k)
                    .map(|v| {
                        [(
                            act.address.clone(),
                            Value::Pair {
                                by: act.signer.clone(),
                                value: Box::new(v),
                            },
                        )]
                        .into_iter()
                        .collect()
                    })
                    .unwrap_or_default(),
            ),
            Contribute::Amount(k) => L::Amounts(
                Self::field(act, k)
                    .and_then(|v| v.as_int())
                    .map(|n| [(act.address.clone(), n)].into_iter().collect())
                    .unwrap_or_default(),
            ),
            Contribute::Clocked { value, clock } => L::Chain(match act.fields.get(clock) {
                Some(SExpr::Atom(Atom::Str(text))) => Hlc::parse(text).map(|hlc| {
                    (
                        Key {
                            hlc,
                            signer: act.signer.clone(),
                            address: act.address.clone(),
                        },
                        Self::field(act, value),
                    )
                }),
                _ => None,
            }),
            Contribute::Write(g) => L::Writes(
                [(act.address.clone(), Self::group_key(act, g))]
                    .into_iter()
                    .collect(),
            ),
            Contribute::Replaced(g) => L::Replaced(match act.fields.get(RESERVED_REPLACES) {
                Some(SExpr::List(items)) => {
                    let k = Self::group_key(act, g);
                    items
                        .iter()
                        .filter_map(|i| match i {
                            SExpr::Atom(Atom::Symbol(a)) | SExpr::Atom(Atom::Str(a)) => {
                                Some((k.clone(), a.clone()))
                            }
                            _ => None,
                        })
                        .collect()
                }
                _ => BTreeSet::new(),
            }),
            Contribute::Sole(k) => L::Sole(Sole::One(act.address.clone(), Self::field(act, k))),
        }
    }

    /// The join half of a term over this context's accepted acts.
    pub fn eval(&self, term: &Term) -> L {
        match term {
            Term::Lift(selects, c) => selects
                .iter()
                .flat_map(|s| self.selected(s))
                .fold(Self::bottom(c), |acc, a| acc.join(Self::contribute(a, c))),
            Term::Pair(a, b) => L::Pair(Box::new(self.eval(a)), Box::new(self.eval(b))),
            Term::Earlier(_) => L::Bool(false),
        }
    }

    /// The displayed value: the post-map applied to the join.
    pub fn display(&self, f: &Factored, done: &[(String, Value)]) -> Value {
        match &f.term {
            Term::Earlier(field) => {
                let earlier = done.iter().find(|(n, _)| n == field).map(|(_, v)| v);
                match &f.post {
                    Post::Histogram => histogram(earlier),
                    Post::Sum => Value::Int(match earlier {
                        Some(Value::Map(entries)) => {
                            entries.iter().filter_map(|(_, v)| v.as_int()).sum()
                        }
                        _ => 0,
                    }),
                    _ => Value::Absent,
                }
            }
            _ => self.post(&self.eval(&f.term), &f.post),
        }
    }

    fn post(&self, l: &L, post: &Post) -> Value {
        match (post, l) {
            (Post::Identity, L::Bool(b)) => Value::Bool(*b),
            (Post::Identity, L::Vals(m)) => Value::Set(m.values().cloned().collect()),
            (Post::Identity, L::Entries(m)) => Value::Map(
                m.iter()
                    .map(|(a, v)| (Value::Str(a.clone()), v.clone()))
                    .collect(),
            ),
            (Post::Identity, L::Chain(c)) => c
                .as_ref()
                .and_then(|(_, v)| v.clone())
                .unwrap_or(Value::Absent),
            (Post::Identity, L::Sole(s)) => match s {
                Sole::One(_, v) => v.clone().unwrap_or(Value::Absent),
                Sole::Bot | Sole::Top(_) => Value::Absent,
            },
            (Post::Size, L::Addrs(s)) => Value::Int(s.len() as i128),
            (Post::Difference, L::Pair(a, b)) => match (&**a, &**b) {
                (L::Amounts(x), L::Amounts(y)) => {
                    Value::Int(x.values().sum::<i128>() - y.values().sum::<i128>())
                }
                _ => Value::Absent,
            },
            (Post::Current(then), L::Pair(w, r)) => match (&**w, &**r) {
                (L::Writes(writes), L::Replaced(replaced)) => {
                    let current: Vec<&Act> = writes
                        .iter()
                        .filter(|(addr, group)| {
                            !replaced.contains(&((*group).clone(), (*addr).clone()))
                        })
                        .filter_map(|(addr, _)| self.acts.get(addr).copied())
                        .collect();
                    self.over_acts(&current, then)
                }
                _ => Value::Absent,
            },
            _ => Value::Absent,
        }
    }

    fn over_acts(&self, acts: &[&Act], post: &Post) -> Value {
        match post {
            Post::Distinct(key) => {
                let mut m: BTreeMap<String, Value> = BTreeMap::new();
                for a in acts {
                    if let Some(v) = Self::field(a, key) {
                        m.insert(v.render(), v);
                    }
                }
                Value::Set(m.into_values().collect())
            }
            Post::PickLww { value, clock } => acts
                .iter()
                .filter_map(|a| match a.fields.get(clock) {
                    Some(SExpr::Atom(Atom::Str(text))) => Hlc::parse(text).map(|hlc| {
                        (
                            Key {
                                hlc,
                                signer: a.signer.clone(),
                                address: a.address.clone(),
                            },
                            *a,
                        )
                    }),
                    _ => None,
                })
                .max_by(|(x, _), (y, _)| x.cmp(y))
                .map(|(_, a)| Self::field(a, value).unwrap_or(Value::Absent))
                .unwrap_or(Value::Absent),
            Post::GroupBy(group, then) => {
                let mut groups: BTreeMap<Vec<u8>, (Value, Vec<&Act>)> = BTreeMap::new();
                for a in acts {
                    let k = match group {
                        Group::Signer => Value::Str(a.signer.clone()),
                        Group::Field(key) => match Self::field(a, key) {
                            Some(v) => v,
                            None => continue,
                        },
                        Group::None => Value::Str(String::new()),
                    };
                    groups
                        .entry(k.render().into_bytes())
                        .or_insert_with(|| (k.clone(), Vec::new()))
                        .1
                        .push(a);
                }
                Value::Map(
                    groups
                        .into_values()
                        .map(|(k, t)| (k, self.over_acts(&t, then)))
                        .collect(),
                )
            }
            _ => Value::Absent,
        }
    }
}

fn histogram(earlier: Option<&Value>) -> Value {
    let mut counts: BTreeMap<Vec<u8>, (Value, i128)> = BTreeMap::new();
    if let Some(Value::Map(entries)) = earlier {
        for (_, v) in entries {
            let v = match v {
                Value::Pair { value, .. } => (**value).clone(),
                other => other.clone(),
            };
            if v == Value::Absent {
                continue;
            }
            counts
                .entry(v.render().into_bytes())
                .or_insert_with(|| (v.clone(), 0))
                .1 += 1;
        }
    }
    Value::Map(
        counts
            .into_values()
            .map(|(v, n)| (v, Value::Int(n)))
            .collect(),
    )
}

/// Every factored field of a clause, displayed in clause order; closure heads
/// are reported as `None` so a caller can fall back to the shipped fold.
pub fn display_clause(
    clause: &StateClause,
    acts: &[Act],
    fallback: &[(String, Value)],
) -> Vec<(String, Option<Value>)> {
    let ctx = Ctx::new(clause, acts);
    let mut done: Vec<(String, Value)> = Vec::new();
    let mut out = Vec::new();
    for (name, rule) in clause.fields() {
        let v = factor(rule).map(|f| ctx.display(&f, &done));
        let for_done = v.clone().or_else(|| {
            fallback
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| v.clone())
        });
        if let Some(v) = for_done {
            done.push((String::from(name), v));
        }
        out.push((String::from(name), v));
    }
    out
}
