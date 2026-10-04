//! SPEC-019 TEST-1914: admission never reads state (REQ-1914, ADR-1909).
//!
//! Stratification is the promise that keeps acceptance inside the regular
//! trace languages of SPEC-014 (`storeTrace_regular`): a verdict is a
//! function of the dialect's static footprint, the message, and the causal
//! structure of the accepted set, never of what the state rules compute from
//! it. If a verdict read the fold, acceptance would inherit the fold's
//! counters and data comparisons, and a verdict could change when a
//! concurrent act moved a field.
//!
//! The check is behavioural. Each corpus dialect gets a *footprint twin*: the
//! same dialect with every state rule swapped for one that reads the same
//! verbs and fields, inserts `:replaces` on the same verbs, and keeps the same
//! bounds, but computes something else. Domains are dropped where the field
//! stays read, which is the case ADR-1909 settled. Everything admission may
//! read statically is then equal and the fold is not, so admission must give
//! every message the same verdict under both, against any accepted set.
//!
//! A mutation test keeps the check honest: an admission that enforces domains
//! (the pre-ADR-1909 behaviour, which reads the fold) must fail it. A static
//! scan adds a second line for paths the corpus may not exercise.

use cbcl_core::dialect::Dialect;
use cbcl_core::r7::r7_violations;
use cbcl_core::state::{fold, render_json, Act, Entry, Rule, StateClause, Value};
use cbcl_core::store::ThreadId;
use cbcl_parser::state_exports::{self, Admission};
use cbcl_parser::{parse, parse_dialect, parse_message};
use proptest::prelude::*;
use serde_json::Value as Json;
use std::collections::BTreeSet;
use std::path::PathBuf;

fn repo_path(rel: &str) -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../..")).join(rel)
}

struct Vector {
    id: String,
    dialect: Dialect,
    thread: ThreadId,
    acts: Vec<Act>,
}

fn vectors() -> Vec<Vector> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(repo_path("test-vectors/state"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no state corpus vectors");
    paths
        .iter()
        .map(|path| {
            let v: Json = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
            let id = v["id"].as_str().unwrap().to_string();
            let dialect = parse_dialect(&parse(v["contract"].as_str().unwrap()).unwrap())
                .unwrap_or_else(|e| panic!("{id}: contract: {e}"));
            let acts = v["messages"]
                .as_array()
                .unwrap()
                .iter()
                .map(|m| {
                    let message =
                        parse_message(&parse(m["canonical"].as_str().unwrap()).unwrap()).unwrap();
                    Act::from_message(message, m["signer"].as_str().unwrap()).unwrap()
                })
                .collect();
            let thread = ThreadId(v["thread"].as_str().unwrap_or("t").to_string());
            Vector {
                id,
                dialect,
                thread,
                acts,
            }
        })
        .collect()
}

type Footprint = (
    BTreeSet<String>,
    BTreeSet<String>,
    BTreeSet<(String, String)>,
);

/// Everything admission may read from a state clause (R.4): the verbs whose
/// field sets are closed, the verbs that carry `:replaces`, and the fields a
/// rule or domain bounds. The bounds clause is shared by both twins.
fn footprint(c: &StateClause) -> Footprint {
    let own = |s: BTreeSet<&str>| s.into_iter().map(String::from).collect();
    (
        own(c.state_bearing_verbs()),
        own(c.replaces_verbs()),
        c.data_fields()
            .into_iter()
            .map(|(v, k)| (v.to_string(), k.to_string()))
            .collect(),
    )
}

/// A rule over the same verbs and fields, with the same `:replaces` verbs,
/// that computes something else. `None` when the sugar has no such sibling.
fn sibling(rule: &Rule) -> Option<Rule> {
    Some(match rule.clone() {
        Rule::Last { verb, key } => Rule::LatestPerSigner { verb, key },
        Rule::LatestPerSigner { verb, key } => Rule::SetUnion { verb, key },
        Rule::SetUnion { verb, key } => Rule::Last { verb, key },
        Rule::Events { verb, key } => Rule::Last { verb, key },
        Rule::LatestPerKey { verb, key, value } if key != value => Rule::LatestPerKey {
            verb,
            key: value,
            value: key,
        },
        Rule::RegisterPerKey {
            verb,
            key,
            value,
            delete,
        } => Rule::ValuesPerKey {
            verb,
            key,
            value,
            delete,
        },
        Rule::ValuesPerKey {
            verb,
            key,
            value,
            delete,
        } => Rule::RegisterPerKey {
            verb,
            key,
            value,
            delete,
        },
        Rule::Exists { verb } => Rule::Count { verb },
        Rule::Count { verb } => Rule::Exists { verb },
        Rule::Counter { inc, dec, key } => Rule::Counter {
            inc: dec,
            dec: inc,
            key,
        },
        _ => return None,
    })
}

/// The footprint twin: each swap and each domain drop is kept only if the
/// twin still installs (R7) with the same footprint, so a swap that breaks a
/// `sum` or `histogram` over the field is skipped.
fn twin(d: &Dialect) -> Dialect {
    let clause = d.state.as_ref().expect("state clause");
    let print = footprint(clause);
    let mut out = d.clone();
    for entry in &clause.entries {
        let mut candidate = out.clone();
        let entries = &mut candidate.state.as_mut().unwrap().entries;
        let at = entries.iter().position(|e| e == entry).unwrap();
        match entry {
            Entry::Field { name, rule } => match sibling(rule) {
                Some(rule) => {
                    entries[at] = Entry::Field {
                        name: name.clone(),
                        rule,
                    }
                }
                None => continue,
            },
            Entry::Domain { .. } => {
                entries.remove(at);
            }
        }
        if r7_violations(&candidate).is_empty()
            && footprint(candidate.state.as_ref().unwrap()) == print
        {
            out = candidate;
        }
    }
    out
}

/// Admission as `state_exports::admit` judges it, or a stand-in under test.
type AdmitFn = dyn Fn(&Dialect, &ThreadId, &[Act], &Act) -> Admission;

/// The accepted set of a forward run with pending retries, as a consumer
/// builds it.
fn accepted(admit: &AdmitFn, d: &Dialect, thread: &ThreadId, acts: &[Act]) -> Vec<Act> {
    let mut out: Vec<Act> = Vec::new();
    let mut open: Vec<&Act> = acts.iter().collect();
    loop {
        let before = open.len();
        open.retain(|a| match admit(d, thread, &out, a) {
            Admission::Accepted => {
                if !out.iter().any(|x| x.address == a.address) {
                    out.push((*a).clone());
                }
                false
            }
            Admission::Rejected(_) => false,
            Admission::Pending => true,
        });
        if open.len() == before {
            return out;
        }
    }
}

/// TEST-1914's judgement: under `admit`, a dialect and its footprint twin
/// give every message the same verdict against `base`, and the twin's fold
/// differs. `Err` names the first message where they part.
fn same_verdicts(
    admit: &AdmitFn,
    v: &Vector,
    a: &Dialect,
    b: &Dialect,
    base: &[Act],
) -> Result<(), String> {
    for act in &v.acts {
        let (x, y) = (
            admit(a, &v.thread, base, act),
            admit(b, &v.thread, base, act),
        );
        if x != y {
            return Err(format!(
                "{}: {} judged {x:?} under the dialect, {y:?} under its twin",
                v.id, act.address
            ));
        }
    }
    Ok(())
}

fn real_admit(d: &Dialect, t: &ThreadId, acc: &[Act], act: &Act) -> Admission {
    state_exports::admit(d, t, acc, act)
}

#[test]
fn every_twin_keeps_the_footprint_and_moves_the_fold() {
    for v in vectors() {
        let b = twin(&v.dialect);
        assert_eq!(
            footprint(v.dialect.state.as_ref().unwrap()),
            footprint(b.state.as_ref().unwrap()),
            "{}",
            v.id
        );
        assert!(r7_violations(&b).is_empty(), "{}: twin must install", v.id);
        assert_ne!(v.dialect.state, b.state, "{}: no rule had a sibling", v.id);
        let acc = accepted(&real_admit, &v.dialect, &v.thread, &v.acts);
        let fold_of = |d: &Dialect| {
            render_json(&fold(
                d.state.as_ref().unwrap(),
                d.causal_protocol.as_ref(),
                &acc,
            ))
        };
        assert_ne!(
            fold_of(&v.dialect),
            fold_of(&b),
            "{}: the twin must compute something else",
            v.id
        );
    }
}

#[test]
fn admission_gives_a_dialect_and_its_twin_the_same_verdicts() {
    for v in vectors() {
        let b = twin(&v.dialect);
        let full = accepted(&real_admit, &v.dialect, &v.thread, &v.acts);
        assert_eq!(
            accepted(&real_admit, &b, &v.thread, &v.acts)
                .iter()
                .map(|a| &a.address)
                .collect::<Vec<_>>(),
            full.iter().map(|a| &a.address).collect::<Vec<_>>(),
            "{}: the accepted set",
            v.id
        );
        let mut reversed = v.acts.clone();
        reversed.reverse();
        assert_eq!(
            accepted(&real_admit, &b, &v.thread, &reversed).len(),
            accepted(&real_admit, &v.dialect, &v.thread, &reversed).len(),
            "{}: reversed",
            v.id
        );
        // Every prefix of the accepted set, including the empty one.
        for n in 0..=full.len() {
            same_verdicts(&real_admit, &v, &v.dialect, &b, &full[..n]).unwrap();
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]
    /// Any subset of the accepted set, causally closed or not, in any order.
    #[test]
    fn admission_ignores_the_fold_on_any_accepted_subset(pick in any::<u64>(), seed in any::<u64>()) {
        for v in vectors() {
            let b = twin(&v.dialect);
            let full = accepted(&real_admit, &v.dialect, &v.thread, &v.acts);
            let mut base: Vec<Act> = full.iter().enumerate().filter(|(i, _)| pick >> (i % 64) & 1 == 1).map(|(_, a)| a.clone()).collect();
            let mut s = seed;
            for i in (1..base.len()).rev() {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                base.swap(i, (s >> 33) as usize % (i + 1));
            }
            if let Err(e) = same_verdicts(&real_admit, &v, &v.dialect, &b, &base) {
                prop_assert!(false, "{}", e);
            }
        }
    }
}

/// The pre-ADR-1909 admission: it enforced opener-drawn domains, which
/// means reading the fold. TEST-1914 must reject it.
fn domain_enforcing_admit(d: &Dialect, t: &ThreadId, acc: &[Act], act: &Act) -> Admission {
    let verdict = state_exports::admit(d, t, acc, act);
    if verdict != Admission::Accepted {
        return verdict;
    }
    let clause = d.state.as_ref().unwrap();
    let state = fold(clause, d.causal_protocol.as_ref(), acc);
    let bare = |s: &str| s.trim_start_matches(':').to_string();
    for (verb, key, field) in clause.domains() {
        if verb != act.verb {
            continue;
        }
        let allowed = state
            .iter()
            .find(|(n, _)| n == field)
            .map(|(_, v)| v.clone());
        let given = act
            .fields
            .iter()
            .find(|(k, _)| bare(k) == bare(key))
            .map(|(_, v)| Value::from_sexpr(v));
        if let (Some(Value::List(allowed)), Some(given)) = (allowed, given) {
            if !allowed.contains(&given) {
                return Admission::Rejected(String::from("domain"));
            }
        }
    }
    verdict
}

#[test]
fn an_admission_that_reads_the_fold_fails_test_1914() {
    let mut caught = Vec::new();
    for v in vectors() {
        let b = twin(&v.dialect);
        let full = accepted(&real_admit, &v.dialect, &v.thread, &v.acts);
        if (0..=full.len()).any(|n| {
            same_verdicts(&domain_enforcing_admit, &v, &v.dialect, &b, &full[..n]).is_err()
        }) {
            caught.push(v.id.clone());
        }
    }
    assert!(
        caught.iter().any(|id| id.contains("lunch-vote")),
        "the domain-enforcing admission went undetected: {caught:?}"
    );
}

// ---- Static line: the admission functions never call the fold -----------

/// The body of `fn <name>` in `source`, by brace matching from its signature.
fn body<'a>(source: &'a str, signature: &str) -> &'a str {
    let start = source
        .find(signature)
        .unwrap_or_else(|| panic!("{signature} not found"));
    let open = start + source[start..].find('{').unwrap();
    let mut depth = 0usize;
    for (i, ch) in source[open..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return &source[open..open + i + 1];
                }
            }
            _ => {}
        }
    }
    panic!("{signature}: unbalanced braces")
}

/// Calls that compute state. Admission may name `state::Act` (a view of a
/// message) and `state::opener`/`root` (which act opens the thread), never
/// a rule's value.
const FOLD_CALLS: &[&str] = &[
    "fold(",
    "fold_str",
    "render_json",
    "current_writes",
    "Kernel",
    "intend(",
    "state_schema",
];

#[test]
fn admission_code_never_calls_the_fold() {
    let read = |rel: &str| std::fs::read_to_string(repo_path(rel)).unwrap();
    let exports = read("crates/cbcl-parser/src/state_exports.rs");
    let r7 = read("crates/cbcl-core/src/r7.rs");
    let intend = read("crates/cbcl-core/src/intend.rs");
    let mut regions: Vec<(String, String)> = vec![
        (
            "state_exports::admit".into(),
            body(&exports, "pub fn admit(").into(),
        ),
        (
            "r7::verify_state_shape".into(),
            body(&r7, "pub fn verify_state_shape(").into(),
        ),
        (
            "intend::cast_of".into(),
            body(&intend, "pub fn cast_of(").into(),
        ),
    ];
    // Instance::new and Instance::store build the store admission reads.
    let instance = body(&intend, "impl<'a> Instance<'a>");
    regions.push(("intend::Instance".into(), instance.into()));
    // The verifier proper: whole files, test modules excluded.
    for rel in [
        "admission.rs",
        "projection.rs",
        "protocol.rs",
        "causal_kernel.rs",
    ] {
        let text = read(&format!("crates/cbcl-core/src/{rel}"));
        let code = text.split("#[cfg(test)]").next().unwrap().to_string();
        regions.push((rel.into(), code));
    }
    for (name, code) in &regions {
        let code: String = code
            .lines()
            .filter(|l| !l.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        for call in FOLD_CALLS {
            assert!(
                !code.contains(call),
                "{name} calls `{call}`: admission must never read state (SPEC-019 REQ-1914)"
            );
        }
    }
}
