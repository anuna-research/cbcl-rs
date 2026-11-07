//! SPEC-038 TEST-3800: every factored rule head is a lift. (a) The term's
//! displayed value equals the shipped fold on every state vector, in forward,
//! reversed and duplicated delivery; (b) the join half is a morphism,
//! `L(A1 ∪ A2) = L(A1) ⊔ L(A2)`, for two partitions of the accepted set;
//! (c) closure heads retain immutable history rather than scalar summaries.
use cbcl_core::lattice::{display_clause_with_protocol, factor, Ctx, Term, L};
use cbcl_core::state::{fold, fold_reference, render_json, Act, Rule};
use cbcl_core::store::ThreadId;
use cbcl_parser::state_exports::{self, Admission};
use cbcl_parser::{parse, parse_dialect, parse_message};
use std::path::PathBuf;

fn corpus() -> Vec<PathBuf> {
    let dir = PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test-vectors/state"
    ));
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map(|x| x == "json").unwrap_or(false))
        .collect();
    v.sort();
    v
}

/// Admit a vector's messages the way the corpus runner does, retrying pending
/// candidates as the accepted set grows.
fn accepted(
    d: &cbcl_core::dialect::Dialect,
    thread: &ThreadId,
    messages: &[(String, String)],
) -> Vec<Act> {
    let acts: Vec<Act> = messages
        .iter()
        .map(|(c, s)| Act::from_message(parse_message(&parse(c).unwrap()).unwrap(), s).unwrap())
        .collect();
    let mut pending: Vec<bool> = vec![true; acts.len()];
    let mut out: Vec<Act> = Vec::new();
    loop {
        let mut progressed = false;
        for i in 0..acts.len() {
            if !pending[i] {
                continue;
            }
            match state_exports::admit(d, thread, &out, &acts[i]) {
                Admission::Accepted => {
                    out.push(acts[i].clone());
                    pending[i] = false;
                    progressed = true;
                }
                Admission::Rejected(_) => pending[i] = false,
                _ => {}
            }
        }
        if !progressed {
            break;
        }
    }
    out
}

struct Loaded {
    id: String,
    dialect: cbcl_core::dialect::Dialect,
    acts: Vec<Act>,
}

fn load() -> Vec<Loaded> {
    corpus()
        .iter()
        .map(|path| {
            let v: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
            let id = v["id"].as_str().unwrap().to_string();
            let d = parse_dialect(&parse(v["contract"].as_str().unwrap()).unwrap()).unwrap();
            let thread = ThreadId(v["thread"].as_str().unwrap_or("t").to_string());
            let messages: Vec<(String, String)> = v["messages"]
                .as_array()
                .unwrap()
                .iter()
                .map(|m| {
                    (
                        m["canonical"].as_str().unwrap().to_string(),
                        m["signer"].as_str().unwrap().to_string(),
                    )
                })
                .collect();
            let acts = accepted(&d, &thread, &messages);
            Loaded {
                id,
                dialect: d,
                acts,
            }
        })
        .collect()
}

fn check_display(l: &Loaded, acts: &[Act], label: &str) -> usize {
    let clause = l.dialect.state.as_ref().unwrap();
    let shipped = fold_reference(clause, l.dialect.causal_protocol.as_ref(), acts);
    assert_eq!(
        render_json(&fold(clause, l.dialect.causal_protocol.as_ref(), acts)),
        render_json(&shipped),
        "{}: shared kernel differs from independent legacy evaluator ({label})",
        l.id
    );
    let ours =
        display_clause_with_protocol(clause, acts, l.dialect.causal_protocol.as_ref(), &shipped);
    let mut compared = 0;
    for (name, got) in &ours {
        let (_, want) = shipped.iter().find(|(n, _)| n == name).unwrap();
        if let Some(got) = got {
            assert_eq!(
                render_json(&[(name.clone(), got.clone())]),
                render_json(&[(name.clone(), want.clone())]),
                "{}: field {name} ({label})",
                l.id
            );
            compared += 1;
        }
    }
    compared
}

#[test]
fn display_equals_the_shipped_fold_in_every_delivery_order() {
    let mut total = 0;
    for l in load() {
        total += check_display(&l, &l.acts, "forward");
        let mut rev = l.acts.clone();
        rev.reverse();
        check_display(&l, &rev, "reversed");
        let mut dup = l.acts.clone();
        dup.extend(l.acts.iter().cloned());
        check_display(&l, &dup, "duplicated");
    }
    assert!(
        total >= 20,
        "expected the corpus to exercise many factored fields, saw {total}"
    );
}

#[test]
fn the_join_half_is_a_morphism_on_two_partitions() {
    let mut checked = 0;
    for l in load() {
        let clause = l.dialect.state.as_ref().unwrap();
        // The law is stated on causally closed accepted sets (SPEC-038
        // REQ-3800): a domain selector reads the opener's `initial` field, so
        // both halves keep the roots and openers and split the rest.
        let openers: std::collections::BTreeSet<&str> = clause
            .fields()
            .filter_map(|(_, r)| match r {
                Rule::Initial { verb, .. } => Some(verb.as_str()),
                _ => None,
            })
            .collect();
        let (base, rest): (Vec<Act>, Vec<Act>) = l
            .acts
            .iter()
            .cloned()
            .partition(|a| a.predecessors.is_empty() || openers.contains(a.verb.as_str()));
        let with_base = |xs: Vec<Act>| -> Vec<Act> { base.iter().cloned().chain(xs).collect() };
        let n = rest.len();
        let partitions: Vec<(Vec<Act>, Vec<Act>)> = vec![
            (
                with_base(rest.iter().step_by(2).cloned().collect()),
                with_base(rest.iter().skip(1).step_by(2).cloned().collect()),
            ),
            (
                with_base(rest[..n / 2].to_vec()),
                with_base(rest[n / 2..].to_vec()),
            ),
        ];
        for (a1, a2) in partitions {
            let whole: Vec<Act> = a1.iter().chain(a2.iter()).cloned().collect();
            let (c1, c2, cw) = (
                Ctx::new(clause, &a1),
                Ctx::new(clause, &a2),
                Ctx::new(clause, &whole),
            );
            for (name, rule) in clause.fields() {
                let Some(f) = factor(rule) else { continue };
                if matches!(f.term, Term::Earlier(_)) {
                    continue;
                }
                let joined: L = c1.eval(&f.term).join(c2.eval(&f.term));
                assert_eq!(
                    joined,
                    cw.eval(&f.term),
                    "{}: field {name} is not a morphism",
                    l.id
                );
                checked += 1;
            }
        }
    }
    assert!(checked >= 20, "checked {checked} morphism instances");
}

#[test]
fn closure_heads_use_history_and_lift_heads_summarize() {
    assert!(factor(&Rule::Progress {
        verb: "tick".into()
    })
    .is_some());
    assert!(matches!(
        factor(&Rule::Progress {
            verb: "tick".into()
        })
        .unwrap()
        .term,
        Term::History(_)
    ));
    assert!(factor(&Rule::Exists {
        verb: "open".into()
    })
    .is_some());
    assert!(factor(&Rule::Initial {
        verb: "open".into(),
        key: "title".into()
    })
    .is_some());
    let mut heads = std::collections::BTreeSet::new();
    for l in load() {
        for (_, rule) in l.dialect.state.as_ref().unwrap().fields() {
            heads.insert(rule.head());
        }
    }
    assert!(heads.len() >= 10, "corpus covers {heads:?}");
}

/// REQ-3800 states the union law on causally closed accepted histories,
/// including histories with different openers. Sharing every opener between
/// partitions (as the corpus check does) does not cover this case.
#[test]
fn domain_lift_obeys_union_law_across_distinct_openers() {
    let source = "(define domain-fork (cbcl) @anuna
      (extend open (to options) (tell to :options options))
      (extend vote (to choice amount) (tell to :choice choice :amount amount))
      (shape open (require :options list))
      (shape vote (require :choice string) (require :amount nonnegative))
      (protocol (then begin open) (then open vote))
      (state (options (initial open :options))
             (domain vote :choice options) (votes (count vote))
             (threshold quorum votes (count 1))
             (amounts (events vote :amount)) (total (sum amounts))))";
    state_exports::parse_and_install_dialect(&parse(source).unwrap()).unwrap();
    let d = parse_dialect(&parse(source).unwrap()).unwrap();
    let thread = ThreadId("t".into());
    let make = |wire: &str, signer: &str| {
        Act::from_message(parse_message(&parse(wire).unwrap()).unwrap(), signer).unwrap()
    };
    let first = make(
        "(lang domain-fork (open @room :options (\"yes\") :caused-by begin :thread \"t\" :from @a))", "@a");
    let second = make(
        "(lang domain-fork (open @room :options (\"no\") :caused-by begin :thread \"t\" :from @b))",
        "@b",
    );
    let vote = make(
        &format!(
            "(lang domain-fork (vote @room :choice \"yes\" :amount 1 :caused-by {} :thread \"t\" :from @a))",
            first.address
        ),
        "@a",
    );
    // Establish that the counterexample uses actual admitted acts rather
    // than an impossible fold input. Both histories are causally closed.
    for act in [&first, &second] {
        assert!(matches!(
            state_exports::admit(&d, &thread, &[], act),
            Admission::Accepted
        ));
    }
    assert!(matches!(
        state_exports::admit(&d, &thread, &[first.clone()], &vote),
        Admission::Accepted
    ));
    assert!(matches!(
        state_exports::admit(&d, &thread, &[first.clone(), vote.clone()], &second),
        Admission::Accepted
    ));
    let left = vec![first, vote];
    let right = vec![second];
    let union: Vec<Act> = left.iter().chain(&right).cloned().collect();
    let clause = d.state.as_ref().unwrap();
    let term = factor(clause.rule_of("votes").unwrap()).unwrap().term;
    let joined = Ctx::new(clause, &left)
        .eval(&term)
        .join(Ctx::new(clause, &right).eval(&term));
    assert_eq!(
        Ctx::new(clause, &union).eval(&term),
        joined,
        "REQ-3800: domains must preserve the lift union law across closed histories"
    );
    let read = |acts: &[Act]| -> serde_json::Value {
        serde_json::from_str(&render_json(&fold(
            clause,
            d.causal_protocol.as_ref(),
            acts,
        )))
        .unwrap()
    };
    assert_eq!(read(&left)["quorum"]["status"], "reached");
    assert_eq!(read(&left)["total"], 1);
    let conflicted = read(&union);
    for field in ["votes", "quorum", "amounts", "total"] {
        assert_eq!(conflicted[field]["status"], "fault", "{field}");
        assert_eq!(
            conflicted[field]["evidence"], conflicted["options"]["evidence"],
            "{field}"
        );
    }
    check_display(
        &Loaded {
            id: "domain-fork".into(),
            dialect: d.clone(),
            acts: union.clone(),
        },
        &union,
        "fault",
    );
    let mut reversed = union.clone();
    reversed.reverse();
    reversed.extend(union);
    assert_eq!(read(&reversed), conflicted);
}
