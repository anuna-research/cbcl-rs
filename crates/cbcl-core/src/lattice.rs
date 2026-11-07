//! The state kernel as lattice terms (SPEC-038 CON-3800, first slice).
//!
//! Vocabulary (SPEC-038 § Vocabulary): a *contribution* `g` is what one act
//! adds to a *carrier* `L`; the *lift* `A ↦ ⋁ g(a)` is the unique
//! join-homomorphism out of the free join-semilattice on acts; a *display* is
//! the post-map from the carrier to the rendered value; the R7 *fold* is the
//! lift followed by a display, and keeps that name only as the API of
//! [`crate::state::fold`].
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
//! Domain-governed terms retain raw accepted acts under union. Initializer
//! evidence and contributions remain present even when a later opener
//! conflicts. Filtering is a read operation; conflicts propagate to dependent
//! displays and thresholds (SPEC-038 ADR-3805).

#![forbid(unsafe_code)]

use crate::hlc::Hlc;
use crate::sexpr::{Atom, SExpr};
use crate::state::{Act, Rule, StateClause, Value, RESERVED_REPLACES};
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::sync::Arc;
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
    Finite {
        table: Arc<crate::finite::Table>,
        index: usize,
        evidence: BTreeSet<String>,
    },
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
    /// Domain-governed contributions retain raw evidence; filtering is a
    /// read/display operation (SPEC-038 ADR-3805).
    History(BTreeMap<String, Act>),
    Pair(Box<L>, Box<L>),
}

impl L {
    /// The join. Mismatched variants join to the left operand; `factor` never
    /// produces them.
    pub fn join(self, other: L) -> L {
        match (self, other) {
            (
                L::Finite {
                    table,
                    index: a,
                    mut evidence,
                },
                L::Finite {
                    table: other,
                    index: b,
                    evidence: right,
                },
            ) => {
                if table.name != other.name {
                    return L::Finite {
                        table,
                        index: a,
                        evidence,
                    };
                }
                evidence.extend(right);
                let index = table.merge(a, b);
                L::Finite {
                    table,
                    index,
                    evidence,
                }
            }
            (L::Bool(a), L::Bool(b)) => L::Bool(a || b),
            (L::History(mut a), L::History(b)) => {
                a.extend(b);
                L::History(a)
            }
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
    Finite {
        table: Arc<crate::finite::Table>,
        rows: Vec<crate::finite::Row>,
    },
    Flag,
    Address,
    Field(String),
    Entry(String),
    Amount(String),
    Clocked {
        value: String,
        clock: String,
    },
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
    Finite(Option<crate::finite::Projection>),
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
        Rule::Lift(lift) => {
            let table = Arc::new((**lift.table.as_ref()?).clone());
            f(
                Term::Lift(
                    alloc::vec![sel(&lift.verb)],
                    Contribute::Finite {
                        table,
                        rows: lift.rows.clone(),
                    },
                ),
                Post::Finite(lift.projection.clone()),
            )
        }
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
    domain_faults: Vec<(String, Value)>,
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
            domain_faults: Vec::new(),
        };
        let mut domains = Vec::new();
        let mut domain_faults = Vec::new();
        for (verb, key, field) in clause.domains() {
            let allowed = match clause.rule_of(field).and_then(factor) {
                Some(fd) => {
                    let value = bare.display(&fd, &[]);
                    if value.fault_evidence().is_some() {
                        domain_faults.push((String::from(verb), value.clone()));
                    }
                    match value {
                        Value::List(items) | Value::Set(items) => items,
                        _ => Vec::new(),
                    }
                }
                None => Vec::new(),
            };
            domains.push((String::from(verb), String::from(key), allowed));
        }
        Ctx {
            acts: unique,
            domains,
            domain_faults,
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
            Contribute::Finite { table, .. } => L::Finite {
                table: table.clone(),
                index: table.bottom,
                evidence: BTreeSet::new(),
            },
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
            Contribute::Finite { table, rows } => {
                let index = rows
                    .iter()
                    .filter(|row| act.fields.get(&row.key) == Some(&row.value))
                    .filter_map(|row| table.index(&row.element))
                    .fold(table.bottom, |a, b| table.merge(a, b));
                let evidence = if index == table.bottom {
                    BTreeSet::new()
                } else {
                    [act.address.clone()].into_iter().collect()
                };
                L::Finite {
                    table: table.clone(),
                    index,
                    evidence,
                }
            }
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
        if self.domain_governed(term) {
            return L::History(
                self.acts
                    .iter()
                    .map(|(addr, act)| (addr.clone(), (*act).clone()))
                    .collect(),
            );
        }
        self.read_carrier(term)
    }

    fn domain_governed(&self, term: &Term) -> bool {
        match term {
            Term::Lift(selects, _) => selects
                .iter()
                .any(|s| !s.raw && self.domains.iter().any(|(verb, _, _)| *verb == s.verb)),
            Term::Pair(a, b) => self.domain_governed(a) || self.domain_governed(b),
            Term::Earlier(_) => false,
        }
    }

    /// The successful read of retained evidence after resolving domains.
    /// Callers check dependency faults before interpreting this carrier.
    pub fn read_carrier(&self, term: &Term) -> L {
        match term {
            Term::Lift(selects, c) => selects
                .iter()
                .flat_map(|s| self.selected(s))
                .fold(Self::bottom(c), |acc, a| acc.join(Self::contribute(a, c))),
            Term::Pair(a, b) => L::Pair(
                Box::new(self.read_carrier(a)),
                Box::new(self.read_carrier(b)),
            ),
            Term::Earlier(_) => L::Bool(false),
        }
    }

    /// The displayed value: the post-map applied to the join.
    pub fn display(&self, f: &Factored, done: &[(String, Value)]) -> Value {
        if let Some(fault) = self.term_fault(&f.term) {
            return fault;
        }
        match &f.term {
            Term::Earlier(field) => {
                let earlier = done.iter().find(|(n, _)| n == field).map(|(_, v)| v);
                if let Some(value) = earlier.filter(|v| v.fault_evidence().is_some()) {
                    return value.clone();
                }
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
            _ => self.post(&self.read_carrier(&f.term), &f.post),
        }
    }

    fn term_fault(&self, term: &Term) -> Option<Value> {
        let mut evidence = BTreeSet::new();
        self.collect_term_faults(term, &mut evidence);
        (!evidence.is_empty()).then(|| {
            crate::state::conflict_top("initializer conflict", evidence.into_iter().collect())
        })
    }

    fn collect_term_faults(&self, term: &Term, evidence: &mut BTreeSet<String>) {
        match term {
            Term::Lift(selects, _) => {
                for s in selects.iter().filter(|s| !s.raw) {
                    for (_, fault) in self
                        .domain_faults
                        .iter()
                        .filter(|(verb, _)| *verb == s.verb)
                    {
                        if let Some(addresses) = fault.fault_evidence() {
                            evidence.extend(addresses);
                        }
                    }
                }
            }
            Term::Pair(a, b) => {
                self.collect_term_faults(a, evidence);
                self.collect_term_faults(b, evidence);
            }
            Term::Earlier(_) => {}
        }
    }

    pub fn rule_fault(&self, rule: &Rule) -> Option<Value> {
        if let Some(f) = factor(rule) {
            return self.term_fault(&f.term);
        }
        let verbs = rule.verbs();
        let mut evidence = BTreeSet::new();
        for (_, fault) in self
            .domain_faults
            .iter()
            .filter(|(verb, _)| verbs.contains(&verb.as_str()))
        {
            if let Some(addresses) = fault.fault_evidence() {
                evidence.extend(addresses);
            }
        }
        (!evidence.is_empty()).then(|| {
            crate::state::conflict_top("initializer conflict", evidence.into_iter().collect())
        })
    }

    fn post(&self, l: &L, post: &Post) -> Value {
        match (post, l) {
            (
                Post::Finite(projection),
                L::Finite {
                    table,
                    index,
                    evidence,
                },
            ) => {
                if *index == table.top {
                    crate::state::conflict_top(
                        "finite lattice conflict",
                        evidence.iter().cloned().collect(),
                    )
                } else {
                    crate::finite::project(projection, table, *index)
                }
            }
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
                Sole::Bot => Value::Absent,
                // ⊤ renders as a fault with its evidence (SPEC-038 REQ-3804).
                Sole::Top(t) => {
                    crate::state::conflict_top("opener fork", t.iter().cloned().collect())
                }
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

// ---------------------------------------------------------------------------
// Threshold reads (SPEC-038 REQ-3802, CON-3801)
// ---------------------------------------------------------------------------

/// The carrier a field's term lifts into, named for typing a threshold
/// element against it (SPEC-038 REQ-3802: typed against the carrier, never
/// the display). The two closure heads have no summarising carrier
/// (REQ-3808); they are named by their closure so that `progress n` and a
/// resource `fault` can be typed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Carrier {
    Finite(Arc<crate::finite::Table>, Option<crate::finite::Projection>),
    Bool,
    Addrs,
    Vals,
    Entries,
    Amounts,
    Chain,
    Writes,
    Replaced,
    Sole,
    Pair(Box<Carrier>, Box<Carrier>),
    /// The act set under the `progress` closure.
    Progress,
    /// The act set under the `bounded-counter` closure.
    Resource,
}

impl Carrier {
    /// The carrier's name in the wire grammar of CON-3801.
    pub fn name(&self) -> String {
        match self {
            Carrier::Finite(table, _) => alloc::format!("finite:{}", table.name),
            Carrier::Bool => String::from("bool"),
            Carrier::Addrs => String::from("addrs"),
            Carrier::Vals => String::from("vals"),
            Carrier::Entries => String::from("entries"),
            Carrier::Amounts => String::from("amounts"),
            Carrier::Chain => String::from("chain"),
            Carrier::Writes => String::from("writes"),
            Carrier::Replaced => String::from("replaced"),
            Carrier::Sole => String::from("sole"),
            Carrier::Pair(a, b) => alloc::format!("({} × {})", a.name(), b.name()),
            Carrier::Progress => String::from("progress"),
            Carrier::Resource => String::from("resource"),
        }
    }
}

fn carrier_of_term(term: &Term) -> Option<Carrier> {
    match term {
        Term::Lift(_, c) => Some(match c {
            Contribute::Finite { table, .. } => Carrier::Finite(table.clone(), None),
            Contribute::Flag => Carrier::Bool,
            Contribute::Address => Carrier::Addrs,
            Contribute::Field(_) => Carrier::Vals,
            Contribute::Entry(_) => Carrier::Entries,
            Contribute::Amount(_) => Carrier::Amounts,
            Contribute::Clocked { .. } => Carrier::Chain,
            Contribute::Write(_) => Carrier::Writes,
            Contribute::Replaced(_) => Carrier::Replaced,
            Contribute::Sole(_) => Carrier::Sole,
        }),
        Term::Pair(a, b) => Some(Carrier::Pair(
            Box::new(carrier_of_term(a)?),
            Box::new(carrier_of_term(b)?),
        )),
        Term::Earlier(_) => None,
    }
}

/// The carrier of a rule: that of its factored term, or the closure for the
/// two closure heads. `None` for a derived field (`histogram`, `sum`), which
/// is a display over an earlier field and has no carrier of its own.
pub fn carrier_of(rule: &Rule) -> Option<Carrier> {
    match rule {
        Rule::Lift(lift) => lift
            .table
            .as_ref()
            .map(|t| Carrier::Finite(Arc::new((**t).clone()), lift.projection.clone())),
        Rule::Progress { .. } => Some(Carrier::Progress),
        Rule::BoundedCounter(_) => Some(Carrier::Resource),
        _ => factor(rule).and_then(|f| carrier_of_term(&f.term)),
    }
}

/// A threshold element (CON-3801 `element`): a named element of a carrier
/// that a threshold read observes being reached.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Element {
    /// A bare scalar; only `#t` against `bool` is admitted.
    Scalar(Value),
    /// `(count n)`: at least `n` addresses, against `addrs`.
    Count(i64),
    /// `(member x)`: `x` present, against `vals` or `entries`.
    Member(Value),
    /// `(sum n)`: grow-only numeric events sum to at least `n`. Installation
    /// requires a mandatory nonnegative shape on their writer.
    Sum(i64),
    /// `(progress n)`: the progress closure has reached position `n`.
    Progress(i64),
}

impl Element {
    /// The wire spelling of the element, for diagnostics.
    pub fn wire(&self) -> String {
        match self {
            Element::Scalar(Value::Bool(true)) => String::from("#t"),
            Element::Scalar(Value::Bool(false)) => String::from("#f"),
            Element::Scalar(v) => v.render(),
            Element::Count(n) => alloc::format!("(count {n})"),
            Element::Member(v) => alloc::format!("(member {})", v.render()),
            Element::Sum(n) => alloc::format!("(sum {n})"),
            Element::Progress(n) => alloc::format!("(progress {n})"),
        }
    }

    /// The element as a state value that round-trips the wire form:
    /// `{"count":2}`, `{"member":"x"}`, `{"sum":10}`, `{"progress":3}`,
    /// `"fault"`, `true`.
    pub fn render(&self) -> Value {
        let keyed = |k: &str, v: Value| Value::Map(alloc::vec![(Value::Str(String::from(k)), v)]);
        match self {
            Element::Scalar(v) => v.clone(),
            Element::Count(n) => keyed("count", Value::Int(*n as i128)),
            Element::Member(v) => keyed("member", v.clone()),
            Element::Sum(n) => keyed("sum", Value::Int(*n as i128)),
            Element::Progress(n) => keyed("progress", Value::Int(*n as i128)),
        }
    }

    /// The element in the canonical encoding of the clause.
    pub fn to_sexpr(&self) -> SExpr {
        fn scalar(v: &Value) -> SExpr {
            match v {
                Value::Str(s) => SExpr::Atom(Atom::Str(s.clone())),
                Value::Int(n) => SExpr::Atom(Atom::Num(*n as i64)),
                Value::Bool(b) => SExpr::Atom(Atom::Bool(*b)),
                other => SExpr::Atom(Atom::Str(other.render())),
            }
        }
        let sym = |x: &str| SExpr::Atom(Atom::Symbol(String::from(x)));
        let num = |n: i64| SExpr::Atom(Atom::Num(n));
        match self {
            Element::Scalar(v) => scalar(v),
            Element::Count(n) => SExpr::List(alloc::vec![sym("count"), num(*n)]),
            Element::Member(v) => SExpr::List(alloc::vec![sym("member"), scalar(v)]),
            Element::Sum(n) => SExpr::List(alloc::vec![sym("sum"), num(*n)]),
            Element::Progress(n) => SExpr::List(alloc::vec![sym("progress"), num(*n)]),
        }
    }

    /// Whether the carrier admits this element (the typing table of
    /// CON-3801): `count n` against `addrs`; `member x` against `vals` or
    /// `entries`; `sum n` against nonnegative numeric `entries` (the writer
    /// shape is checked at installation); `progress n` against progress;
    /// a bare `#t` against `bool`. Faults are separate outcomes.
    pub fn admitted_by(&self, carrier: &Carrier) -> bool {
        match (self, carrier) {
            (Element::Scalar(Value::Str(name)), Carrier::Finite(table, _)) => {
                table.index(name).is_some_and(|i| i != table.top)
            }
            (Element::Scalar(Value::Int(_)), Carrier::Finite(_, Some(project))) => {
                project.stable
                    && project
                        .rows
                        .iter()
                        .all(|(_, v)| matches!(v, SExpr::Atom(Atom::Num(_))))
            }
            (Element::Scalar(Value::Bool(true)), Carrier::Finite(_, Some(project))) => {
                project.stable
                    && project
                        .rows
                        .iter()
                        .all(|(_, v)| matches!(v, SExpr::Atom(Atom::Bool(_))))
            }
            (Element::Scalar(Value::Bool(true)), Carrier::Bool) => true,
            (Element::Count(n), Carrier::Addrs) => *n >= 0,
            (Element::Member(v), Carrier::Vals | Carrier::Entries) => {
                matches!(v, Value::Str(_) | Value::Int(_) | Value::Bool(_))
            }
            (Element::Sum(_), Carrier::Entries) => true,
            (Element::Progress(n), Carrier::Progress) => *n >= 0,
            _ => false,
        }
    }

    /// `self ≤ σ`: the element is reached by a carrier element.
    pub fn le(&self, l: &L) -> bool {
        match (self, l) {
            (_, L::Finite { table, index, .. }) => self.finite_read(table, *index, &None),
            (Element::Scalar(Value::Bool(true)), L::Bool(b)) => *b,
            (Element::Count(n), L::Addrs(s)) => s.len() as i64 >= *n,
            (Element::Member(v), L::Vals(m)) => m.contains_key(&v.render()),
            (Element::Member(v), L::Entries(m)) => {
                let want = v.render();
                m.values().any(|e| match e {
                    Value::Pair { value, .. } => value.render() == want,
                    other => other.render() == want,
                })
            }
            (Element::Sum(n), L::Amounts(m)) => m.values().sum::<i128>() >= *n as i128,
            (Element::Sum(n), L::Entries(m)) => {
                m.values().filter_map(Value::as_int).sum::<i128>() >= *n as i128
            }
            _ => false,
        }
    }

    pub fn finite_read(
        &self,
        table: &crate::finite::Table,
        index: usize,
        projection: &Option<crate::finite::Projection>,
    ) -> bool {
        if index == table.top {
            return false;
        }
        match self {
            Element::Scalar(Value::Str(name)) => {
                table.index(name).is_some_and(|i| table.le(i, index))
            }
            Element::Scalar(Value::Int(n)) if projection.as_ref().is_some_and(|p| p.stable) => {
                matches!(crate::finite::project(projection,table,index), Value::Int(value) if value >= *n)
            }
            Element::Scalar(Value::Bool(true)) if projection.as_ref().is_some_and(|p| p.stable) => {
                matches!(
                    crate::finite::project(projection, table, index),
                    Value::Bool(true)
                )
            }
            _ => false,
        }
    }

    pub fn le_with_post(&self, l: &L, post: &Post) -> bool {
        if let (L::Finite { table, index, .. }, Post::Finite(projection)) = (l, post) {
            self.finite_read(table, *index, projection)
        } else {
            self.le(l)
        }
    }

    /// The element is reached by a closure head's display (REQ-3808): the
    /// progress integer has reached `n`. Faults are checked separately.
    /// The closure heads have no summarising carrier, so their ⊤ and their
    /// position are read from the display, which is monotone as proved in
    /// SPEC-034 and SPEC-019 CON-1908.
    pub fn le_display(&self, shown: &Value) -> bool {
        match (self, shown) {
            (Element::Progress(n), Value::Int(i)) => *i >= *n as i128,
            _ => false,
        }
    }
}

/// How two elements of one threshold set relate (REQ-3802): `None` when
/// they are incompatible (no element other than ⊤ lies above both),
/// `Some("duplicate")` when equal, `Some("compatible")` otherwise. On the
/// chains (`count`, `sum`, `progress`) any two elements are comparable, hence
/// compatible; two members are compatible, since the set of both lies above
/// each. A numeric event member and its sum can also be reached together.
pub fn relation(a: &Element, b: &Element) -> Option<&'static str> {
    if a == b {
        return Some("duplicate");
    }
    match (a, b) {
        (Element::Count(_), Element::Count(_))
        | (Element::Sum(_), Element::Sum(_))
        | (Element::Progress(_), Element::Progress(_))
        | (Element::Member(_), Element::Member(_))
        | (Element::Member(_), Element::Sum(_))
        | (Element::Sum(_), Element::Member(_))
        | (Element::Scalar(_), Element::Scalar(_)) => Some("compatible"),
        _ => None,
    }
}

/// Some element other than ⊤ lies above both.
pub fn compatible(a: &Element, b: &Element) -> bool {
    relation(a, b).is_some()
}

/// The pairwise-incompatibility check of a threshold set in `O(k²)`
/// comparisons (NFR-3800): the first pair `rel` reports as related, as
/// `(i, j, why)`, or `Ok`.
pub fn pairwise(
    elements: &[Element],
    mut rel: impl FnMut(&Element, &Element) -> Option<&'static str>,
) -> Result<(), (usize, usize, &'static str)> {
    for i in 0..elements.len() {
        for j in (i + 1)..elements.len() {
            if let Some(why) = rel(&elements[i], &elements[j]) {
                return Err((i, j, why));
            }
        }
    }
    Ok(())
}
