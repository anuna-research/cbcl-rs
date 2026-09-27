//! Property tests for the SPEC-019 state layer (TEST-1940 … TEST-1946).
//!
//! Each property names the theorem of `lean-cbcl/LeanCbcl/State.lean`
//! (REQ-1930) it mirrors. The Lean model proves the property of the
//! kernel; these tests check that `cbcl_core::state::fold` and
//! `cbcl_core::intend::intend` have it too, on random accepted sets.
//!
//! TEST-1945 (address order equals the retired interpreter's
//! depth-then-hash order) is a migration test that lives with the
//! interpreter it compares against, not here.

use std::collections::{BTreeMap, BTreeSet};

use cbcl_core::dialect::{Dialect, PerformativeDef, ResourceBounds};
use cbcl_core::intend::{intend, Instance, Reject};
use cbcl_core::message::{CausedBy, Message, Performative, Recipients};
use cbcl_core::protocol::{verify_causal, CausalProtocol, NodeRef, StepDecl, VerificationResult};
use cbcl_core::r7::{insert_replaces, r7_violations, verify_state_shape};
use cbcl_core::role::AgentKey;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::shape::{ShapeConstraint, ShapeRule, TypeConstraint};
use cbcl_core::state::{
    fold, render_json, Act, Entry, Rule, StateClause, Value, RESERVED_REPLACES,
};
use cbcl_core::store::ThreadId;
use proptest::prelude::*;

// ===========================================================================
// A dialect exercising every rule head, and its acts
// ===========================================================================

const SIGNERS: &[&str] = &["@a", "@b", "@c"];
const ITEMS: &[&str] = &["a", "b", "c"];
const TAGS: &[&str] = &["x", "y", "z"];
const OPS: &[&str] = &["op1", "op2", "op3", "op4"];
const CHOICES: &[&str] = &["P", "S", "T"];

fn sym(s: &str) -> SExpr {
    SExpr::Atom(Atom::Symbol(String::from(s)))
}
fn kw(s: &str) -> SExpr {
    SExpr::Atom(Atom::Keyword(String::from(s)))
}
fn str_(s: &str) -> SExpr {
    SExpr::Atom(Atom::Str(String::from(s)))
}
fn num(n: i64) -> SExpr {
    SExpr::Atom(Atom::Num(n))
}
fn boolean(b: bool) -> SExpr {
    SExpr::Atom(Atom::Bool(b))
}
fn addr_list(addrs: &[String]) -> SExpr {
    SExpr::List(addrs.iter().map(|a| sym(a)).collect())
}

fn field_entry(name: &str, rule: Rule) -> Entry {
    Entry::Field {
        name: String::from(name),
        rule,
    }
}

/// The state clause under test: one field per rule head.
fn clause() -> StateClause {
    let s = String::from;
    StateClause {
        entries: vec![
            field_entry(
                "title",
                Rule::Last {
                    verb: s("open"),
                    key: s("title"),
                },
            ),
            field_entry(
                "items",
                Rule::RegisterPerKey {
                    verb: s("check"),
                    key: s("item"),
                    value: s("done"),
                    delete: Some(s("drop")),
                },
            ),
            field_entry(
                "item-values",
                Rule::ValuesPerKey {
                    verb: s("check"),
                    key: s("item"),
                    value: s("done"),
                    delete: Some(s("drop")),
                },
            ),
            field_entry(
                "per-item",
                Rule::LatestPerKey {
                    verb: s("check"),
                    key: s("item"),
                    value: s("done"),
                },
            ),
            field_entry(
                "any-check",
                Rule::Exists { verb: s("check") },
            ),
            field_entry(
                "tags",
                Rule::ObservedSet {
                    add: s("add"),
                    remove: s("remove"),
                    key: s("tag"),
                },
            ),
            field_entry(
                "seen",
                Rule::SetUnion {
                    verb: s("add"),
                    key: s("tag"),
                },
            ),
            field_entry(
                "ops",
                Rule::Values {
                    verb: s("add"),
                    key: s("op"),
                },
            ),
            field_entry("adds", Rule::Count { verb: s("add") }),
            field_entry(
                "credits",
                Rule::Events {
                    verb: s("credit"),
                    key: s("amount"),
                },
            ),
            field_entry("total", Rule::Sum { field: s("credits") }),
            field_entry(
                "balance",
                Rule::Counter {
                    inc: s("credit"),
                    dec: s("debit"),
                    key: s("amount"),
                },
            ),
            field_entry(
                "ballots",
                Rule::LatestPerSigner {
                    verb: s("vote"),
                    key: s("choice"),
                },
            ),
            field_entry(
                "tally",
                Rule::Histogram {
                    field: s("ballots"),
                },
            ),
        ],
    }
}

/// What an act says, before it has an address or a `:replaces` list.
#[derive(Debug, Clone)]
enum Spec {
    Open { title: String },
    Check { item: String, done: bool, rep: u64 },
    Drop { item: String, rep: u64 },
    Add { tag: String, op: String },
    Remove { tag: String, rep: u64 },
    Credit { amount: i64, op: String },
    Debit { amount: i64, op: String },
    Vote { choice: String },
}

#[derive(Debug, Clone)]
struct Raw {
    addr: u64,
    signer: usize,
    spec: Spec,
}

fn one_of(xs: &'static [&'static str]) -> impl Strategy<Value = String> {
    (0..xs.len()).prop_map(move |i| String::from(xs[i]))
}

fn arb_spec() -> impl Strategy<Value = Spec> {
    prop_oneof![
        1 => one_of(&["Launch", "Plan"]).prop_map(|title| Spec::Open { title }),
        4 => (one_of(ITEMS), any::<bool>(), any::<u64>())
            .prop_map(|(item, done, rep)| Spec::Check { item, done, rep }),
        2 => (one_of(ITEMS), any::<u64>()).prop_map(|(item, rep)| Spec::Drop { item, rep }),
        3 => (one_of(TAGS), one_of(OPS)).prop_map(|(tag, op)| Spec::Add { tag, op }),
        2 => (one_of(TAGS), any::<u64>()).prop_map(|(tag, rep)| Spec::Remove { tag, rep }),
        2 => (-50i64..50, one_of(OPS)).prop_map(|(amount, op)| Spec::Credit { amount, op }),
        2 => (-50i64..50, one_of(OPS)).prop_map(|(amount, op)| Spec::Debit { amount, op }),
        2 => one_of(CHOICES).prop_map(|choice| Spec::Vote { choice }),
    ]
}

fn arb_raw() -> impl Strategy<Value = Raw> {
    (any::<u64>(), 0..SIGNERS.len(), arb_spec()).prop_map(|(addr, signer, spec)| Raw {
        addr,
        signer,
        spec,
    })
}

/// Build one act. The address is synthetic (the fold reads `Act.address`
/// and nothing else about identity), spelled like a wire address.
fn mk_act(addr: &str, verb: &str, signer: &str, preds: &[&str], fields: &[(&str, SExpr)]) -> Act {
    let mut params = Vec::new();
    for (k, v) in fields {
        params.push(kw(k));
        params.push(v.clone());
    }
    let message = Message::Simple {
        performative: Performative::Custom(String::from(verb)),
        recipient: Some(Recipients::One(String::from("@list"))),
        content: SExpr::List(Vec::new()),
        params,
        thread: Some(String::from("t")),
        sender: None,
        caused_by: Some(if preds.is_empty() {
            CausedBy::Begin
        } else {
            CausedBy::Single(String::from(preds[0]))
        }),
    };
    let mut a = Act::from_message(message, signer).expect("a simple message is an act");
    a.address = String::from(addr);
    a
}

fn render_field(a: &Act, key: &str) -> Option<String> {
    a.fields.get(key).map(|v| Value::from_sexpr(v).render())
}

/// Choose, by the bits of `rep`, which earlier acts a `:replaces` list
/// names, plus (sometimes) an address that resolves to nothing.
fn choose_replaces(rep: u64, candidates: &[&Act]) -> Vec<String> {
    let mut out: Vec<String> = candidates
        .iter()
        .enumerate()
        .filter(|(i, _)| (rep >> (i % 64)) & 1 == 1)
        .map(|(_, a)| a.address.clone())
        .collect();
    if rep % 7 == 0 {
        out.push(format!("sha256-{}", "f".repeat(64)));
    }
    out.sort();
    out.dedup();
    out
}

/// Realise the specs as acts: distinct addresses (a collision drops the
/// later spec), `:replaces` lists drawn from earlier acts of the same key.
fn build(raws: &[Raw]) -> Vec<Act> {
    let mut acts: Vec<Act> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for raw in raws {
        let addr = format!("sha256-{:064x}", raw.addr);
        if !seen.insert(addr.clone()) {
            continue;
        }
        let signer = SIGNERS[raw.signer % SIGNERS.len()];
        let same_key = |verbs: &[&str], key: &str, value: &str| -> Vec<&Act> {
            acts.iter()
                .filter(|a| verbs.contains(&a.verb.as_str()))
                .filter(|a| render_field(a, key).as_deref() == Some(&Value::Str(String::from(value)).render()))
                .collect()
        };
        let act = match &raw.spec {
            Spec::Open { title } => mk_act(&addr, "open", signer, &[], &[("title", str_(title))]),
            Spec::Check { item, done, rep } => {
                let reps = choose_replaces(*rep, &same_key(&["check", "drop"], "item", item));
                mk_act(
                    &addr,
                    "check",
                    signer,
                    &[],
                    &[
                        ("item", str_(item)),
                        ("done", boolean(*done)),
                        (RESERVED_REPLACES, addr_list(&reps)),
                    ],
                )
            }
            Spec::Drop { item, rep } => {
                let reps = choose_replaces(*rep, &same_key(&["check", "drop"], "item", item));
                mk_act(
                    &addr,
                    "drop",
                    signer,
                    &[],
                    &[("item", str_(item)), (RESERVED_REPLACES, addr_list(&reps))],
                )
            }
            Spec::Add { tag, op } => mk_act(
                &addr,
                "add",
                signer,
                &[],
                &[("tag", str_(tag)), ("op", str_(op))],
            ),
            Spec::Remove { tag, rep } => {
                let reps = choose_replaces(*rep, &same_key(&["add"], "tag", tag));
                mk_act(
                    &addr,
                    "remove",
                    signer,
                    &[],
                    &[("tag", str_(tag)), (RESERVED_REPLACES, addr_list(&reps))],
                )
            }
            Spec::Credit { amount, op } => mk_act(
                &addr,
                "credit",
                signer,
                &[],
                &[("amount", num(*amount)), ("op", str_(op))],
            ),
            Spec::Debit { amount, op } => mk_act(
                &addr,
                "debit",
                signer,
                &[],
                &[("amount", num(*amount)), ("op", str_(op))],
            ),
            Spec::Vote { choice } => mk_act(&addr, "vote", signer, &[], &[("choice", str_(choice))]),
        };
        acts.push(act);
    }
    acts
}

fn arb_acts() -> impl Strategy<Value = Vec<Act>> {
    prop::collection::vec(arb_raw(), 0..32).prop_map(|raws| build(&raws))
}

// ===========================================================================
// Reading a state
// ===========================================================================

fn field<'a>(state: &'a [(String, Value)], name: &str) -> &'a Value {
    &state
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("field {name} present"))
        .1
}

fn as_int(v: &Value) -> i128 {
    match v {
        Value::Int(n) => *n,
        other => panic!("expected an integer, found {other:?}"),
    }
}

fn as_bool(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        other => panic!("expected a bool, found {other:?}"),
    }
}

/// A map or set as rendered keys → rendered values (a set's values are `""`).
fn entries(v: &Value) -> BTreeMap<String, String> {
    match v {
        Value::Map(es) => es.iter().map(|(k, x)| (k.render(), x.render())).collect(),
        Value::Set(xs) => xs.iter().map(|x| (x.render(), String::new())).collect(),
        other => panic!("expected a map or set, found {other:?}"),
    }
}

// ===========================================================================
// The register, computed independently (SPEC-019 R.2 `current`)
// ===========================================================================

/// `current writer key delete`: the writes of `writer` that no accepted
/// write or deletion of the same key names in `:replaces`. First
/// occurrence per address, as the store would hold it.
fn current_writes<'a>(acts: &'a [Act], writer: &str, key: &str, delete: Option<&str>) -> Vec<&'a Act> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let set: Vec<&Act> = acts
        .iter()
        .filter(|a| seen.insert(a.address.as_str()))
        .collect();
    let mut replaced: BTreeSet<(String, String)> = BTreeSet::new();
    for r in set
        .iter()
        .filter(|a| a.verb == writer || Some(a.verb.as_str()) == delete)
    {
        let k = render_field(r, key).unwrap_or_default();
        if let Some(SExpr::List(items)) = r.fields.get(RESERVED_REPLACES) {
            for item in items {
                if let SExpr::Atom(Atom::Symbol(x)) | SExpr::Atom(Atom::Str(x)) = item {
                    replaced.insert((k.clone(), x.clone()));
                }
            }
        }
    }
    set.into_iter()
        .filter(|w| w.verb == writer)
        .filter(|w| {
            let k = render_field(w, key).unwrap_or_default();
            !replaced.contains(&(k, w.address.clone()))
        })
        .collect()
}

/// `register-per-key` from `current`: per key, the greatest-address
/// current write's value (`registerPerKey_from_current`).
fn register_oracle(acts: &[Act]) -> BTreeMap<String, String> {
    let mut best: BTreeMap<String, &Act> = BTreeMap::new();
    for w in current_writes(acts, "check", "item", Some("drop")) {
        let Some(k) = render_field(w, "item") else {
            continue;
        };
        match best.get(&k) {
            Some(b) if b.address.as_bytes() >= w.address.as_bytes() => {}
            _ => {
                best.insert(k, w);
            }
        }
    }
    best.into_iter()
        .filter_map(|(k, w)| render_field(w, "done").map(|v| (k, v)))
        .collect()
}

/// Every address some accepted act names in `:replaces`.
fn named_anywhere(acts: &[Act]) -> BTreeSet<String> {
    acts.iter()
        .filter_map(|a| a.fields.get(RESERVED_REPLACES))
        .filter_map(|v| match v {
            SExpr::List(items) => Some(items),
            _ => None,
        })
        .flatten()
        .filter_map(|x| match x {
            SExpr::Atom(Atom::Symbol(s)) | SExpr::Atom(Atom::Str(s)) => Some(s.clone()),
            _ => None,
        })
        .collect()
}

// ===========================================================================
// TEST-1940 … TEST-1944: the fold
// ===========================================================================

proptest! {
    /// TEST-1940. Mirrors `fold_perm_invariant` and `fold_dedup_invariant`
    /// (State.lean): the fold is a function of the accepted set, invariant
    /// under permutation and under duplicate delivery of the slice itself.
    #[test]
    fn prop_fold_permutation_and_duplication_invariant(
        (acts, shuffled) in arb_acts().prop_flat_map(|a| (Just(a.clone()), Just(a).prop_shuffle())),
        dup in any::<prop::sample::Index>(),
        at in any::<prop::sample::Index>(),
    ) {
        let c = clause();
        let base = render_json(&fold(&c, None, &acts));
        prop_assert_eq!(render_json(&fold(&c, None, &shuffled)), base.clone());

        let mut twice = acts.clone();
        twice.extend(acts.iter().cloned());
        prop_assert_eq!(render_json(&fold(&c, None, &twice)), base.clone());

        if !acts.is_empty() {
            let d = acts[dup.index(acts.len())].clone();
            let mut with_dup = acts.clone();
            with_dup.insert(at.index(acts.len() + 1), d);
            prop_assert_eq!(render_json(&fold(&c, None, &with_dup)), base);
        }
    }

    /// TEST-1941. Mirrors `acts_mono`, `count_mono`, `has_mono`,
    /// `exists_mono`, `setUnion_mono` (State.lean): under store growth,
    /// `count` does not decrease, `exists` is not withdrawn, `set-union`
    /// and `events` only grow.
    #[test]
    fn prop_monotone_rules_under_append(
        acts in arb_acts(),
        cut in any::<prop::sample::Index>(),
    ) {
        let c = clause();
        let k = cut.index(acts.len() + 1);
        let before = fold(&c, None, &acts[..k]);
        let after = fold(&c, None, &acts);

        prop_assert!(as_int(field(&before, "adds")) <= as_int(field(&after, "adds")));
        if as_bool(field(&before, "any-check")) {
            prop_assert!(as_bool(field(&after, "any-check")));
        }
        let seen_before = entries(field(&before, "seen"));
        let seen_after = entries(field(&after, "seen"));
        for k in seen_before.keys() {
            prop_assert!(seen_after.contains_key(k), "set-union lost {k}");
        }
        let ev_before = entries(field(&before, "credits"));
        let ev_after = entries(field(&after, "credits"));
        for (k, v) in &ev_before {
            prop_assert_eq!(ev_after.get(k), Some(v), "events lost or changed {}", k);
        }
    }

    /// TEST-1942. Mirrors `mem_current_iff` and
    /// `registerPerKey_from_current` (State.lean): `register-per-key` is,
    /// per key, the greatest-address member of `current`, where a write is
    /// current iff it is a write of the verb that no accepted write or
    /// deletion of the same key names in `:replaces`.
    #[test]
    fn prop_register_equals_current_oracle(acts in arb_acts()) {
        let st = fold(&clause(), None, &acts);
        prop_assert_eq!(entries(field(&st, "items")), register_oracle(&acts));
    }

    /// TEST-1943. Mirrors `replaced_never_current` and `unnamed_is_current`
    /// (State.lean): a write named in an accepted `:replaces` for its key
    /// never wins; a write no accepted act names is current whatever else
    /// is accepted, so its value is held by `values-per-key`; and a key
    /// whose every write is replaced is absent.
    #[test]
    fn prop_replaced_never_wins_and_unnamed_is_current(acts in arb_acts()) {
        let st = fold(&clause(), None, &acts);
        let items = entries(field(&st, "items"));
        let item_values = field(&st, "item-values");
        let named = named_anywhere(&acts);
        let current: BTreeSet<String> = current_writes(&acts, "check", "item", Some("drop"))
            .iter()
            .map(|a| a.address.clone())
            .collect();

        let mut keys_with_writes: BTreeSet<String> = BTreeSet::new();
        for w in acts.iter().filter(|a| a.verb == "check") {
            let Some(k) = render_field(w, "item") else { continue };
            keys_with_writes.insert(k.clone());
            if !named.contains(&w.address) {
                // Unnamed ⇒ current ⇒ its value is in the key's multi-value register.
                prop_assert!(current.contains(&w.address), "unnamed write {} is not current", w.address);
                let vals = match item_values {
                    Value::Map(es) => es
                        .iter()
                        .find(|(kk, _)| kk.render() == k)
                        .map(|(_, v)| entries(v))
                        .unwrap_or_default(),
                    other => panic!("expected a map, found {other:?}"),
                };
                let done = render_field(w, "done").unwrap();
                prop_assert!(vals.contains_key(&done), "unnamed write's value {done} missing under {k}");
            }
        }
        for k in &keys_with_writes {
            let current_for_key: Vec<&Act> = current_writes(&acts, "check", "item", Some("drop"))
                .into_iter()
                .filter(|w| render_field(w, "item").as_deref() == Some(k))
                .collect();
            match items.get(k) {
                None => prop_assert!(current_for_key.is_empty(), "key {k} absent though a write is current"),
                Some(v) => {
                    // The winner is a current write: a replaced write never wins.
                    let winner = current_for_key
                        .iter()
                        .max_by(|a, b| a.address.as_bytes().cmp(b.address.as_bytes()))
                        .expect("a present key has a current write");
                    prop_assert!(!named.contains(&winner.address) || current.contains(&winner.address));
                    let winner_done = render_field(winner, "done");
                    prop_assert_eq!(winner_done.as_deref(), Some(v.as_str()));
                }
            }
        }
    }

    /// TEST-1944. Mirrors `sumField_insert` (State.lean): `sum` and
    /// `counter` change by exactly one act's amount per new address and
    /// by zero per re-delivered address.
    #[test]
    fn prop_sum_once_per_address(
        acts in arb_acts(),
        amount in -50i64..50,
        fresh in any::<u64>(),
        dup in any::<prop::sample::Index>(),
    ) {
        let c = clause();
        let base = fold(&c, None, &acts);
        let total0 = as_int(field(&base, "total"));
        let balance0 = as_int(field(&base, "balance"));

        let addr = format!("sha256-{fresh:064x}");
        if acts.iter().all(|a| a.address != addr) {
            let credit = mk_act(&addr, "credit", "@a", &[], &[("amount", num(amount)), ("op", str_("op1"))]);
            let mut with = acts.clone();
            with.push(credit);
            let st = fold(&c, None, &with);
            prop_assert_eq!(as_int(field(&st, "total")), total0 + i128::from(amount));
            prop_assert_eq!(as_int(field(&st, "balance")), balance0 + i128::from(amount));

            let debit = mk_act(&addr, "debit", "@a", &[], &[("amount", num(amount)), ("op", str_("op1"))]);
            let mut with = acts.clone();
            with.push(debit);
            let st = fold(&c, None, &with);
            prop_assert_eq!(as_int(field(&st, "total")), total0);
            prop_assert_eq!(as_int(field(&st, "balance")), balance0 - i128::from(amount));
        }

        if !acts.is_empty() {
            let mut again = acts.clone();
            again.push(acts[dup.index(acts.len())].clone());
            let st = fold(&c, None, &again);
            prop_assert_eq!(as_int(field(&st, "total")), total0);
            prop_assert_eq!(as_int(field(&st, "balance")), balance0);
        }
    }
}

// ===========================================================================
// TEST-1946: the binder on a role-free inline dialect
// ===========================================================================

const THREAD: &str = "list-1";

fn require(keyword: &str, t: TypeConstraint) -> ShapeRule {
    ShapeRule::Require {
        keyword: String::from(keyword),
        type_constraint: Some(t),
        children: Vec::new(),
    }
}

fn step(verb: &str, preds: &[&str], succs: &[&str]) -> (String, StepDecl) {
    (
        String::from(verb),
        StepDecl {
            performative: String::from(verb),
            predecessors: preds.iter().map(|p| NodeRef::Single(String::from(*p))).collect(),
            successors: succs.iter().map(|p| NodeRef::Single(String::from(*p))).collect(),
        },
    )
}

fn perf(name: &str, params: &[&str]) -> PerformativeDef {
    let mut template = vec![sym("tell"), sym("to")];
    for p in params.iter().skip(1) {
        template.push(kw(p));
        template.push(sym(p));
    }
    PerformativeDef {
        name: String::from(name),
        params: params.iter().map(|p| sym(p)).collect(),
        template: SExpr::List(template),
        role: None,
    }
}

/// The checklist of `dialects/checklist.cbcl` without its roles, built
/// in place: `open` opens, `check` writes the register keyed by `:item`,
/// `drop` deletes a key. Installation inserts `:replaces`.
fn checklist() -> Dialect {
    let s = String::from;
    let mut d = Dialect {
        name: s("checklist"),
        extends: Vec::new(),
        author: Some(s("@anuna")),
        performatives: vec![
            perf("open", &["to", "title"]),
            perf("check", &["to", "item", "done"]),
            perf("drop", &["to", "item"]),
        ],
        resources: ResourceBounds {
            max_depth: 16,
            max_expansion_size: 4096,
            verification_time_ms: 1000,
        },
        examples: Vec::new(),
        signature: None,
        hash: None,
        protocol: None,
        causal_protocol: Some(CausalProtocol {
            steps: [
                step("open", &["begin"], &["check", "drop"]),
                step("check", &["open"], &[]),
                step("drop", &["open"], &[]),
            ]
            .into_iter()
            .collect(),
        }),
        shapes: vec![
            ShapeConstraint {
                performative: s("open"),
                rules: vec![require("title", TypeConstraint::String)],
            },
            ShapeConstraint {
                performative: s("check"),
                rules: vec![
                    require("item", TypeConstraint::String),
                    require("done", TypeConstraint::Bool),
                ],
            },
            ShapeConstraint {
                performative: s("drop"),
                rules: vec![require("item", TypeConstraint::String)],
            },
        ],
        roles: Vec::new(),
        causal_locality: Default::default(),
        state: Some(StateClause {
            entries: vec![
                field_entry(
                    "title",
                    Rule::Last {
                        verb: s("open"),
                        key: s("title"),
                    },
                ),
                field_entry(
                    "items",
                    Rule::RegisterPerKey {
                        verb: s("check"),
                        key: s("item"),
                        value: s("done"),
                        delete: Some(s("drop")),
                    },
                ),
            ],
        }),
        state_bounds: None,
    };
    insert_replaces(&mut d);
    d
}

/// The accepted opener, with a real content address.
fn opener(d: &Dialect) -> Act {
    let inner = Message::Simple {
        performative: Performative::Custom(String::from("open")),
        recipient: Some(Recipients::Set(SIGNERS.iter().map(|s| String::from(*s)).collect())),
        content: SExpr::List(Vec::new()),
        params: vec![kw("title"), str_("Launch"), kw("from"), sym("@a")],
        thread: Some(String::from(THREAD)),
        sender: None,
        caused_by: Some(CausedBy::Begin),
    };
    let message = Message::Dialect {
        dialect_name: d.name.clone(),
        inner: Box::new(inner),
    };
    Act::from_message(message, "@a").expect("the opener is an act")
}

#[derive(Debug, Clone)]
enum Intent {
    Check { item: String, done: bool },
    Drop { item: String },
}

fn arb_intent() -> impl Strategy<Value = (usize, Intent)> {
    (
        0..SIGNERS.len(),
        prop_oneof![
            3 => (one_of(ITEMS), any::<bool>()).prop_map(|(item, done)| Intent::Check { item, done }),
            1 => one_of(ITEMS).prop_map(|item| Intent::Drop { item }),
        ],
    )
}

fn intent_fields(i: &Intent) -> (&'static str, String, BTreeMap<String, SExpr>) {
    let mut f = BTreeMap::new();
    match i {
        Intent::Check { item, done } => {
            f.insert(String::from("item"), str_(item));
            f.insert(String::from("done"), boolean(*done));
            ("check", item.clone(), f)
        }
        Intent::Drop { item } => {
            f.insert(String::from("item"), str_(item));
            ("drop", item.clone(), f)
        }
    }
}

/// The `:replaces` the binder must produce for `verb` on `item` (R.5
/// step 4): the current writes for the key, plus, for a writer with a
/// delete verb, the current deletions for the key.
fn expected_replaces(acts: &[Act], verb: &str, item: &str) -> Vec<String> {
    let key = Value::Str(String::from(item)).render();
    let mut out: Vec<String> = current_writes(acts, "check", "item", Some("drop"))
        .into_iter()
        .filter(|w| render_field(w, "item").as_deref() == Some(&key))
        .map(|w| w.address.clone())
        .collect();
    if verb == "check" {
        out.extend(
            current_writes(acts, "drop", "item", Some("check"))
                .into_iter()
                .filter(|w| render_field(w, "item").as_deref() == Some(&key))
                .map(|w| w.address.clone()),
        );
    }
    out.sort();
    out.dedup();
    out
}

fn replaces_of(a: &Act) -> Vec<String> {
    match a.fields.get(RESERVED_REPLACES) {
        Some(SExpr::List(items)) => items
            .iter()
            .filter_map(|x| match x {
                SExpr::Atom(Atom::Symbol(s)) => Some(s.clone()),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

proptest! {
    /// TEST-1946. Mirrors `intend_pred_valid`, `intend_replaces_current`,
    /// `intend_supersedes`, `intend_current_after` (State.lean): on a
    /// role-free dialect, every act the binder returns verifies `Valid`
    /// against the accepted set plus itself, names as predecessor an
    /// accepted act of an admitted type, carries exactly the current
    /// writes for its key in `:replaces`, and once accepted is the
    /// register's current value; re-binding the key names it.
    #[test]
    fn prop_intend_sound(script in prop::collection::vec(arb_intent(), 0..16)) {
        let d = checklist();
        prop_assert!(r7_violations(&d).is_empty(), "{:?}", r7_violations(&d));
        let protocol = d.causal_protocol.as_ref().unwrap();
        let thread = ThreadId(String::from(THREAD));
        let mut acts: Vec<Act> = vec![opener(&d)];
        let opener_addr = acts[0].address.clone();

        for (who, intent) in &script {
            let signer = AgentKey(String::from(SIGNERS[*who]));
            let (verb, item, fields) = intent_fields(intent);
            let expected = expected_replaces(&acts, verb, &item);
            let inst = Instance::new(&d, thread.clone(), &acts).unwrap();
            let result = intend(&inst, &signer, verb, fields.clone());

            let message = match result {
                Err(Reject::NothingToDelete) => {
                    prop_assert_eq!(verb, "drop");
                    prop_assert!(expected.is_empty(), "NothingToDelete with current writes {:?}", expected);
                    continue;
                }
                Err(other) => {
                    prop_assert!(false, "intend rejected {verb} on {item}: {other:?}");
                    unreachable!()
                }
                Ok(m) => m,
            };

            // The act is shape-valid and its :replaces is exactly the current writes.
            prop_assert!(verify_state_shape(&d, &message).is_ok());
            let act = Act::from_message(message.clone(), &signer.0).unwrap();
            prop_assert_eq!(act.verb.as_str(), verb);
            prop_assert_eq!(replaces_of(&act), expected);
            // intend_pred_valid: the predecessor is an accepted act of an admitted type.
            prop_assert_eq!(act.predecessors.clone(), vec![opener_addr.clone()]);

            // Valid against acc ∪ {act}.
            acts.push(act.clone());
            let inst = Instance::new(&d, thread.clone(), &acts).unwrap();
            let verdict = verify_causal(
                verb,
                act.simple().caused_by(),
                &inst.store(),
                protocol,
                &thread,
            );
            prop_assert_eq!(verdict, VerificationResult::Valid);

            // intend_current_after: the register reflects the act.
            let st = fold(d.state.as_ref().unwrap(), Some(protocol), &acts);
            let items = entries(field(&st, "items"));
            let key = Value::Str(item.clone()).render();
            match intent {
                Intent::Check { done, .. } => {
                    let want = Value::Bool(*done).render();
                    prop_assert_eq!(items.get(&key), Some(&want));
                }
                Intent::Drop { .. } => {
                    prop_assert!(!items.contains_key(&key), "dropped key {key} still present");
                }
            }

            // intend_supersedes: re-binding the key names this act.
            let (_, _, again) = intent_fields(&Intent::Check { item: item.clone(), done: true });
            let rebound = intend(&inst, &signer, "check", again).unwrap();
            let rebound = Act::from_message(rebound, &signer.0).unwrap();
            prop_assert!(replaces_of(&rebound).contains(&act.address), "re-binding did not name {}", act.address);
            if matches!(intent, Intent::Drop { .. }) {
                let (_, _, del) = intent_fields(&Intent::Drop { item: item.clone() });
                prop_assert!(matches!(intend(&inst, &signer, "drop", del), Err(Reject::NothingToDelete)));
            }
        }
    }
}
