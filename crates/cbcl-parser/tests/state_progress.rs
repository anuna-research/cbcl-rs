//! Protocol progress counts established positions, not competing messages.
#![allow(clippy::cloned_ref_to_slice_refs)]
use cbcl_core::dialect::{Dialect, DialectRegistry};
use cbcl_core::r7::r7_violations;
use cbcl_core::state::{fold, render_json, render_schema, state_schema, Act};
use cbcl_core::store::ThreadId;
use cbcl_parser::state_exports::{admit, Admission};
use cbcl_parser::{parse, parse_dialect, parse_message};

fn source(body: &str) -> String {
    format!("(define demo (cbcl) @author (extend open (to) (tell to)) (extend tick (to) (tell to)) (extend other (to) (tell to)) (protocol (then begin {body})) (state (number (progress tick)) (messages (count tick))))")
}
fn install(body: &str) -> Dialect {
    let mut registry = DialectRegistry::new();
    registry
        .install(parse_dialect(&parse(&source(body)).unwrap()).unwrap())
        .unwrap();
    registry.iter().last().unwrap().clone()
}
fn act(verb: &str, pred: &str, who: &str) -> Act {
    Act::from_message(
        parse_message(
            &parse(&format!(
                "(lang demo ({verb} @all :caused-by {pred} :thread \"t\" :from {who}))"
            ))
            .unwrap(),
        )
        .unwrap(),
        who,
    )
    .unwrap()
}
fn state(d: &Dialect, history: &[Act]) -> serde_json::Value {
    serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        history,
    )))
    .unwrap()
}
fn accept(d: &Dialect, history: &[Act], a: &Act) {
    assert_eq!(
        admit(d, &ThreadId("t".into()), history, a),
        Admission::Accepted
    );
}

#[test]
fn competing_branches_converge_on_progress_not_message_count() {
    let d = install("(repeat 100 tick)");
    assert_eq!(state(&d, &[]), serde_json::json!({"number":0,"messages":0}));
    let a = act("tick", "begin", "@a");
    let b = act("tick", &a.address, "@b");
    let c = act("tick", &a.address, "@c");
    let next = act("tick", &c.address, "@a");
    accept(&d, &[], &a);
    accept(&d, &[a.clone()], &b);
    accept(&d, &[a.clone(), b.clone()], &c);
    let history = vec![a, b, c];
    assert_eq!(
        state(&d, &history),
        serde_json::json!({"number":2,"messages":3})
    );
    let mut reversed = history.clone();
    reversed.reverse();
    let mut duplicated = reversed.clone();
    duplicated.extend(history.clone());
    assert_eq!(state(&d, &history), state(&d, &reversed));
    assert_eq!(state(&d, &history), state(&d, &duplicated));
    accept(&d, &history, &next);
    let mut advanced = history;
    advanced.push(next);
    assert_eq!(
        state(&d, &advanced),
        serde_json::json!({"number":3,"messages":4})
    );
}

#[test]
fn forks_at_99_reach_100_without_inflating_progress() {
    let d = install("(repeat 100 tick)");
    let mut history = Vec::new();
    for i in 0..99 {
        let parent = history
            .last()
            .map(|a: &Act| a.address.as_str())
            .unwrap_or("begin");
        let a = act("tick", parent, ["@a", "@b", "@c"][i % 3]);
        accept(&d, &history, &a);
        history.push(a);
    }
    assert_eq!(state(&d, &history)["number"], 99);
    let b = act("tick", &history[98].address, "@b");
    let c = act("tick", &history[98].address, "@c");
    accept(&d, &history, &b);
    accept(&d, &history, &c);
    history.push(b.clone());
    history.push(c.clone());
    assert_eq!(
        state(&d, &history),
        serde_json::json!({"number":100,"messages":101})
    );
    for tip in [b, c] {
        let extra = act("tick", &tip.address, "@a");
        assert!(matches!(
            admit(&d, &ThreadId("t".into()), &history, &extra),
            Admission::Rejected(_)
        ));
    }
}

#[test]
fn nested_repeats_and_intervening_other_verbs_have_static_occurrence_ranks() {
    let d = install("open (repeat 2 (repeat 2 tick) other)");
    let mut history = vec![act("open", "begin", "@a")];
    let mut count = 0;
    for verb in ["tick", "tick", "other", "tick", "tick", "other"] {
        let a = act(verb, &history.last().unwrap().address, "@a");
        accept(&d, &history, &a);
        history.push(a);
        if verb == "tick" {
            count += 1;
        }
        assert_eq!(state(&d, &history)["number"], count);
    }
}

#[test]
fn rejects_missing_or_incomparable_positions_and_bad_rule_arity() {
    let mut d = install("(repeat 2 tick)");
    d.causal_protocol
        .as_mut()
        .unwrap()
        .steps
        .retain(|name, _| !name.starts_with("tick"));
    assert!(r7_violations(&d)
        .iter()
        .any(|e| e.to_string().contains("progress")));
    // A typed programmatic DAG with incomparable occurrences must not acquire
    // an arbitrary order merely because BTreeMap keys sort deterministically.
    use cbcl_core::protocol::NodeRef;
    let mut d = install("open (repeat 2 tick)");
    let p = d.causal_protocol.as_mut().unwrap();
    p.steps.get_mut("tick#2").unwrap().predecessors = vec![NodeRef::Single("open".into())];
    p.steps.get_mut("open").unwrap().successors = vec![NodeRef::All(
        ["tick#1".into(), "tick#2".into()].into_iter().collect(),
    )];
    p.steps.get_mut("tick#1").unwrap().successors.clear();
    assert!(r7_violations(&d)
        .iter()
        .any(|e| e.to_string().contains("incomparable")));
    assert!(parse_dialect(
        &parse(&source("(repeat 2 tick)").replace("(progress tick)", "(progress tick other)"))
            .unwrap()
    )
    .is_err());
}

#[test]
fn missing_evidence_and_unrelated_threads_cannot_invent_progress() {
    let d = install("(repeat 3 tick)");
    let a = act("tick", "begin", "@a");
    let b = act("tick", &a.address, "@b");
    assert_eq!(state(&d, &[b.clone()])["number"], 0);
    let other = Act::from_message(
        parse_message(
            &parse(&cbcl_core::intend::canonical_text(&a.message).replace("\"t\"", "\"other\""))
                .unwrap(),
        )
        .unwrap(),
        "@a",
    )
    .unwrap();
    assert_eq!(state(&d, &[other, b])["number"], 1);
}

#[test]
fn progress_is_integer_typed_described_and_content_addressed() {
    let d = install("(repeat 3 tick)");
    let schema = render_schema(&state_schema(d.state.as_ref().unwrap(), &d.shapes));
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&schema).unwrap()["number"]["type"],
        "int"
    );
    let description: serde_json::Value = serde_json::from_str(
        &cbcl_parser::describe::describe_dialect_str(&source("(repeat 3 tick)")).unwrap(),
    )
    .unwrap();
    assert_eq!(
        description["state"]["number"],
        serde_json::json!(["progress", "tick"])
    );
    let changed = parse_dialect(
        &parse(&source("(repeat 3 tick)").replace("(progress tick)", "(count tick)")).unwrap(),
    )
    .unwrap();
    assert_ne!(
        cbcl_core::canonical::dialect_hash(&d),
        cbcl_core::canonical::dialect_hash(&changed)
    );
}

#[test]
#[ignore = "requires lake build LeanCbcl.StateProgress; explicitly run by Lean CI"]
fn native_progress_matches_kernel_reduced_lean() {
    use cbcl_core::message::CausedBy;
    use std::collections::BTreeMap;
    use std::fmt::Write;
    struct Comparisons {
        source: String,
        cases: usize,
    }
    impl Comparisons {
        fn snapshot(&mut self, bound: usize, acts: &[Act]) {
            let d = install(&format!("(repeat {bound} tick)"));
            let actual = state(&d, acts)["number"].as_u64().unwrap();
            let id = self.cases;
            let mut addresses = BTreeMap::new();
            for a in acts {
                let next = addresses.len();
                addresses.entry(a.address.clone()).or_insert(next);
            }
            // Reserve absent-reference IDs after all present addresses. No
            // string/hash equality is guessed by the model transcription.
            for a in acts {
                for h in &a.predecessors {
                    let next = addresses.len();
                    addresses.entry(h.clone()).or_insert(next);
                }
            }
            writeln!(
                self.source,
                "def store{id} : Store := fun h => match h with"
            )
            .unwrap();
            let mut seen = std::collections::BTreeSet::new();
            for a in acts {
                if !seen.insert(&a.address) {
                    continue;
                }
                let h = addresses[&a.address];
                let cause = match a.simple().caused_by() {
                    Some(CausedBy::Begin) => ".begin".to_owned(),
                    Some(CausedBy::Single(p)) => format!(".previous {}", addresses[p]),
                    _ => ".absent".to_owned(),
                };
                assert_eq!(a.verb, "tick", "single-verb comparison boundary");
                assert_eq!(a.simple().thread(), Some("t"));
                writeln!(self.source, "  | {h} => some ⟨0, \"tick\", {cause}⟩").unwrap();
            }
            writeln!(self.source, "  | _ => none").unwrap();
            let hashes = acts
                .iter()
                .map(|a| addresses[&a.address].to_string())
                .collect::<Vec<_>>()
                .join(",");
            writeln!(self.source, "theorem comparison{id} : progress store{id} 0 \"tick\" {bound} [{hashes}] = {actual} := by decide\n#print axioms comparison{id}").unwrap();
            self.cases += 1;
        }
    }
    let mut checks = Comparisons { source: "import LeanCbcl.StateProgress\nopen CBCL.Repeat CBCL.StateProgress\nset_option maxRecDepth 4096\nset_option maxHeartbeats 0\n".into(), cases:0 };
    for bound in [1, 2, 3, 10, 100] {
        let mut history = Vec::new();
        checks.snapshot(bound, &history);
        for i in 0..bound {
            let pred = history
                .last()
                .map(|a: &Act| a.address.as_str())
                .unwrap_or("begin");
            history.push(act("tick", pred, ["@a", "@b", "@c"][i % 3]));
        }
        checks.snapshot(bound, &history[..1]);
        checks.snapshot(bound, &history);
        let pred = if bound == 1 {
            "begin"
        } else {
            history[bound - 2].address.as_str()
        };
        let peer = act("tick", pred, "@peer");
        history.push(peer);
        checks.snapshot(bound, &history);
        checks.snapshot(bound, &history[bound..]);
        history.reverse();
        let mut duplicated = history.clone();
        duplicated.extend(history);
        checks.snapshot(bound, &duplicated);
    }
    let path =
        std::env::temp_dir().join(format!("cbcl-state-progress-{}.lean", std::process::id()));
    std::fs::write(&path, &checks.source).unwrap();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean-cbcl");
    let output = std::process::Command::new("lake")
        .args(["env", "lean"])
        .arg(&path)
        .current_dir(root)
        .output()
        .unwrap();
    let _ = std::fs::remove_file(path);
    let report = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "{report}");
    assert!(
        !report.contains("sorry") && !report.contains("sorryAx"),
        "{report}"
    );
    let audited: Vec<&str> = report
        .lines()
        .filter(|line| line.starts_with("'comparison"))
        .collect();
    assert_eq!(audited.len(), checks.cases, "{report}");
    for line in audited {
        if line.contains("does not depend on any axioms") {
            continue;
        }
        let axioms = line
            .split_once('[')
            .and_then(|(_, tail)| tail.strip_suffix(']'))
            .expect("malformed axiom audit");
        assert!(
            axioms
                .split(',')
                .all(|a| matches!(a.trim(), "propext" | "Classical.choice" | "Quot.sound")),
            "nonstandard comparison axiom: {line}"
        );
    }
}

#[test]
fn domain_filtering_does_not_hide_causal_progress() {
    let text="(define demo (cbcl) @author (extend open (to options) (tell to :options options)) (extend tick (to choice) (tell to :choice choice)) (shape open (require :options list)) (shape tick (require :choice string)) (protocol (then begin open (repeat 3 tick))) (state (options (initial open :options)) (domain tick :choice options) (number (progress tick)) (messages (count tick))))";
    let mut registry = DialectRegistry::new();
    registry
        .install(parse_dialect(&parse(text).unwrap()).unwrap())
        .unwrap();
    let d = registry.iter().last().unwrap();
    let wire = |text: &str| {
        Act::from_message(parse_message(&parse(text).unwrap()).unwrap(), "@a").unwrap()
    };
    let open =
        wire("(lang demo (open @all :options (\"yes\") :caused-by begin :thread \"t\" :from @a))");
    let tick = wire(&format!(
        "(lang demo (tick @all :choice \"no\" :caused-by {} :thread \"t\" :from @a))",
        open.address
    ));
    accept(d, &[], &open);
    accept(d, &[open.clone()], &tick);
    let state = state(d, &[open, tick]);
    assert_eq!(state["number"], 1);
    assert_eq!(state["messages"], 0);
}

#[test]
fn progress_uses_pinned_role_root_and_accepts_competing_members() {
    let source="(define demo (cbcl) @author (:roles ((* member))) (extend tick (to) :from member :to (member) (tell to)) (protocol (then begin (repeat 100 tick))) (state (number (progress tick)) (messages (count tick))))";
    let mut registry = DialectRegistry::new();
    registry
        .install(parse_dialect(&parse(source).unwrap()).unwrap())
        .unwrap();
    let d = registry.iter().last().unwrap();
    let parse_act = |s: &str, who: &str| {
        Act::from_message(parse_message(&parse(s).unwrap()).unwrap(), who).unwrap()
    };
    let root = parse_act(
        "(with-roles ((member @a @b @c)) (signed @a (hello :thread \"t\" :caused-by begin)))",
        "@a",
    );
    let signed = |pred: &str, who: &str| {
        parse_act(&format!("(signed {who} (lang demo (tick (@a @b @c) :caused-by {pred} :thread \"t\" :from {who})))"),who)
    };
    let a = signed(&root.address, "@a");
    let b = signed(&a.address, "@b");
    let c = signed(&a.address, "@c");
    accept(d, &[], &root);
    accept(d, &[root.clone()], &a);
    accept(d, &[root.clone(), a.clone()], &b);
    accept(d, &[root.clone(), a.clone()], &c);
    let mut accepted = vec![root, a, b, c];
    assert_eq!(
        state(d, &accepted),
        serde_json::json!({"number":2,"messages":3})
    );
    accepted.reverse();
    assert_eq!(state(d, &accepted)["number"], 2);
}

#[test]
fn json_authoring_compiles_progress_through_the_same_native_rule() {
    let contract = serde_json::json!({"version":3,"kind":"contract","name":"progress-demo","verbs":{"open":{"after":["begin"],"fields":{}},"tick":{"after":["open"],"fields":{}}},"state":{"number":["progress","tick"]}});
    let compiled: serde_json::Value =
        serde_json::from_str(&cbcl_parser::compile_contract_str(&contract.to_string()).unwrap())
            .unwrap();
    assert!(compiled["dialect"]
        .as_str()
        .unwrap()
        .contains("(number (progress tick))"));
}

#[test]
fn progress_does_not_feed_back_into_acceptance() {
    let progress = install("(repeat 2 tick)");
    let mut registry = DialectRegistry::new();
    registry
        .install(
            parse_dialect(
                &parse(&source("(repeat 2 tick)").replace("(progress tick)", "(count tick)"))
                    .unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
    let counted = registry.iter().last().unwrap();
    let a = act("tick", "begin", "@a");
    let b = act("tick", &a.address, "@b");
    let c = act("tick", &a.address, "@c");
    let history = vec![a, b, c];
    assert_ne!(
        state(&progress, &history)["number"],
        state(counted, &history)["number"]
    );
    for candidate in [
        act("tick", &history[0].address, "@d"),
        act("tick", &history[1].address, "@d"),
    ] {
        assert_eq!(
            admit(&progress, &ThreadId("t".into()), &history, &candidate),
            admit(counted, &ThreadId("t".into()), &history, &candidate)
        );
    }
}

#[test]
fn shipped_counting_dialect_installs_with_progress() {
    let source = include_str!("../../../dialects/count-to-one-hundred.cbcl");
    let mut registry = DialectRegistry::new();
    registry
        .install(parse_dialect(&parse(source).unwrap()).unwrap())
        .unwrap();
    let d = registry.iter().last().unwrap();
    assert_eq!(state(d, &[])["number"], 0);
}
