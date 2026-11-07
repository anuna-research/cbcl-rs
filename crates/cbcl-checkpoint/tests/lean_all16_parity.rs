//! Bounded observational bridge, not extraction/native-admission correctness.
//! Run explicitly after building CheckpointAll and CheckpointAllRustOracle:
//! CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo test -p cbcl-checkpoint \
//!   --test lean_all16_parity -- --ignored --nocapture
//! Native signed inputs are authenticated; the fixture treats these as admitted.
//! Main's lifecycle tests independently exercise full ordinary admission. This
//! bridge compares all sixteen renders at every prefix and every checkpoint cut.
//! Protocol evidence is a recognized single-verb-chain port (opener edge→begin).
//! Resource classifier is an independent bootstrap-only account subset, not the
//! general escrow verifier. No expected resource outcome is passed into Lean.
#![cfg(feature = "std")]
extern crate alloc;
pub use cbcl_checkpoint::*;
#[allow(dead_code)]
#[path = "../src/test_support.rs"]
mod test_support;
use cbcl_checkpoint::{certificate::SignedMessage, summary::Summary};
use cbcl_core::{
    escrow::{self, CounterRule, Ownership},
    hlc::Hlc,
    protocol::{CausalProtocol, NodeRef, StepDecl},
    sexpr::{Atom, SExpr},
    state::{self, Act, Entry, Rule, StateClause},
};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::Command,
};

fn resource_rule() -> CounterRule {
    CounterRule {
        ownership: Ownership::Account,
        certification: Default::default(),
        floor: 0,
        ceiling: Some(20),
        initial_verb: "open".into(),
        initial_key: "alloc".into(),
        headroom_key: Some("room".into()),
        issuer: "issuer".into(),
        increment: ("mint".into(), "amount".into()),
        decrement: ("burn".into(), "amount".into()),
        transfer: Some(("pay".into(), "recipient".into(), "amount".into())),
        transfer_headroom: None,
    }
}
fn clause() -> StateClause {
    let rules = vec![
        Rule::Initial {
            verb: "open".into(),
            key: "title".into(),
        },
        Rule::Values {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::ValuesPerKey {
            verb: "put".into(),
            key: "k".into(),
            value: "v".into(),
            delete: Some("del".into()),
        },
        Rule::ObservedSet {
            add: "put".into(),
            remove: "del".into(),
            key: "k".into(),
        },
        Rule::LwwMap {
            verb: "put".into(),
            key: "k".into(),
            value: "v".into(),
            clock: "clock".into(),
            delete: Some("del".into()),
        },
        Rule::LwwRegister {
            verb: "put".into(),
            key: "v".into(),
            clock: "clock".into(),
        },
        Rule::LwwPerSigner {
            verb: "put".into(),
            key: "v".into(),
            clock: "clock".into(),
        },
        Rule::Exists { verb: "put".into() },
        Rule::Count { verb: "put".into() },
        Rule::Counter {
            inc: "put".into(),
            dec: "down".into(),
            key: "v".into(),
        },
        Rule::SetUnion {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::Events {
            verb: "put".into(),
            key: "v".into(),
        },
        Rule::Histogram { field: "r4".into() },
        Rule::Sum {
            field: "r11".into(),
        },
        Rule::Progress {
            verb: "tick".into(),
        },
        Rule::BoundedCounter(Box::new(resource_rule())),
    ];
    StateClause {
        entries: rules
            .into_iter()
            .enumerate()
            .map(|(i, rule)| Entry::Field {
                name: format!("r{i}"),
                rule,
            })
            .collect(),
    }
}
fn protocol() -> CausalProtocol {
    let mut steps = BTreeMap::new();
    for (verb, parent) in [
        ("begin", None),
        ("open", Some("begin")),
        ("put", Some("open")),
        ("del", Some("open")),
        ("down", Some("open")),
        ("tick#1", Some("open")),
        ("tick#2", Some("tick#1")),
        ("tick#3", Some("tick#2")),
    ] {
        let next: Vec<String> = match verb {
            "begin" => vec!["open".into()],
            "open" => vec!["put".into(), "del".into(), "down".into(), "tick#1".into()],
            "tick#1" => vec!["tick#2".into()],
            "tick#2" => vec!["tick#3".into()],
            _ => vec![],
        };
        steps.insert(
            verb.into(),
            StepDecl {
                performative: verb.into(),
                predecessors: parent
                    .into_iter()
                    .map(|p| NodeRef::Single(p.into()))
                    .collect(),
                successors: if next.len() > 1 {
                    vec![NodeRef::Any(next.into_iter().collect())]
                } else {
                    next.into_iter().map(NodeRef::Single).collect()
                },
            },
        );
    }
    CausalProtocol { steps }
}
fn signed(text: &str, signer: &str) -> Act {
    SignedMessage::sign(test_support::parse(text), signer, &test_support::Keys)
        .unwrap()
        .authenticate(&test_support::Keys)
        .unwrap()
}
fn native_id(a: &Act) -> String {
    a.address.replacen("sha256-", "sha256:", 1)
}
fn wire_id(id: &str) -> String {
    id.replacen("sha256:", "sha256-", 1)
}
// Fixture mirrors independent native edit fields; no production API is introduced.
#[allow(clippy::too_many_arguments)]
fn op(
    verb: &str,
    key: &str,
    value: i64,
    time: u64,
    refs: &[String],
    parent: &Act,
    nonce: usize,
    signer: &str,
) -> Act {
    let replaces = refs
        .iter()
        .map(|s| format!("\"{s}\""))
        .collect::<Vec<_>>()
        .join(" ");
    let data = match verb {
        "put" => format!(
            ":k \"{key}\" :v {value} :clock \"{}\" :replaces ({replaces}) :unused \"{}\"",
            Hlc::new(time, 0).render(),
            "unselected-body-".repeat(64)
        ),
        "del" => format!(":k \"{key}\" :replaces ({replaces})"),
        "down" => format!(":v {value}"),
        _ => String::new(),
    };
    signed(&format!("(lang all16-parity ({verb} (@m0 @m1) \"n{nonce}\" {data} :sender {signer} :thread \"all16-parity\" :caused-by \"{}\"))",native_id(parent)),signer)
}
fn corpus() -> Vec<(String, Vec<Act>)> {
    let root=signed("(with-roles ((issuer @m0) (holder @m0 @m1)) (hello :sender @m0 :thread \"all16-parity\" :caused-by begin))","@m0");
    let open=signed(&format!("(lang all16-parity (open (@m0 @m1) :title \"Drawing\" :alloc ((@m0 10) (@m1 0)) :room ((@m0 5) (@m1 5)) :from @m0 :sender @m0 :thread \"all16-parity\" :caused-by \"{}\"))",native_id(&root)),"@m0");
    let a = op("put", "x", 3, 10, &[], &open, 1, "@m0");
    let b = op("put", "x", 7, 10, &[], &open, 2, "@m1");
    let cross = op(
        "put",
        "y",
        -2,
        9,
        std::slice::from_ref(&a.address),
        &open,
        3,
        "@m1",
    );
    let erase = op(
        "del",
        "x",
        0,
        11,
        std::slice::from_ref(&b.address),
        &open,
        4,
        "@m0",
    );
    let future = op("put", "x", 5, 7, &[], &open, 5, "@m0");
    let early = op(
        "del",
        "x",
        0,
        12,
        std::slice::from_ref(&future.address),
        &open,
        6,
        "@m1",
    );
    let down = op("down", "", 2, 0, &[], &open, 7, "@m0");
    let tick1 = op("tick", "", 0, 0, &[], &open, 8, "@m0");
    let tick2 = op("tick", "", 0, 0, &[], &tick1, 9, "@m0");
    let tick3 = op("tick", "", 0, 0, &[], &tick2, 10, "@m0");
    vec![
        (
            "forks-late-replacement".into(),
            vec![
                root.clone(),
                open.clone(),
                tick1.clone(),
                a.clone(),
                b.clone(),
                cross.clone(),
                erase.clone(),
                early.clone(),
                future.clone(),
                down.clone(),
                tick2.clone(),
                tick3.clone(),
                a.clone(),
            ],
        ),
        (
            "concurrent-order-and-duplicate".into(),
            vec![
                root.clone(),
                open.clone(),
                b.clone(),
                early.clone(),
                a.clone(),
                cross.clone(),
                future.clone(),
                erase.clone(),
                tick1.clone(),
                tick2.clone(),
                down,
                tick3.clone(),
                b,
            ],
        ),
        (
            "causal-chain-checkpoints".into(),
            vec![root, open, tick1, tick2, tick3],
        ),
    ]
}
fn refs(a: &Act) -> Vec<String> {
    match a.fields.get("replaces") {
        Some(SExpr::List(xs)) => xs
            .iter()
            .map(|v| match v {
                SExpr::Atom(Atom::Str(s) | Atom::Symbol(s)) => s.clone(),
                _ => panic!("native refs"),
            })
            .collect(),
        _ => vec![],
    }
}
fn string(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}
fn list(xs: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", xs.into_iter().collect::<Vec<_>>().join(","))
}
fn val(v: &SExpr) -> String {
    match v {
        SExpr::Atom(Atom::Str(s)) => format!("(.str {})", string(s)),
        SExpr::Atom(Atom::Num(n)) => format!("(.int ({n}))"),
        SExpr::Atom(Atom::Bool(b)) => format!("(.bool {b})"),
        _ => panic!("outside bounded scalar corpus"),
    }
}
fn text(v: &SExpr) -> &str {
    match v {
        SExpr::Atom(Atom::Str(s) | Atom::Symbol(s)) => s,
        _ => panic!("text projection"),
    }
}
#[derive(Clone, Copy, PartialEq)]
enum Control {
    None,
    SelectedValue,
    CausalParent,
    ResourceAllocation,
}
fn event(a: &Act, ops: &[Act], ranks: &BTreeMap<String, usize>, control: Control) -> String {
    let id = ranks[&a.address];
    let fields = list(
        a.fields
            .iter()
            .filter(|(k, _)| ["k", "v", "title"].contains(&k.as_str()))
            .map(|(k, v)| {
                let value = if control == Control::SelectedValue && a.verb == "put" {
                    format!(
                        "(.int ({}))",
                        if let SExpr::Atom(Atom::Num(n)) = v {
                            n + 100
                        } else {
                            0
                        }
                    )
                } else {
                    val(v)
                };
                // Only selected v is altered; keys and initial title stay independent.
                format!("({}, {})", string(k), if k == "v" { value } else { val(v) })
            }),
    );
    let predecessors: Vec<_> = a.predecessors.iter().map(|p| ranks[&wire_id(p)]).collect();
    let cause = if a.verb == "tick" {
        let parent = a.predecessors.first().unwrap();
        let p = ops.iter().find(|p| p.address == wire_id(parent)).unwrap();
        if control == Control::CausalParent && p.verb == "tick" {
            ".absent".into()
        } else if p.verb == "open" {
            ".begin".into()
        } else {
            format!("(.previous {})", ranks[&p.address])
        }
    } else {
        ".absent".into()
    };
    let stamp = match a.fields.get("clock") {
        Some(SExpr::Atom(Atom::Str(s))) => {
            let h = Hlc::parse(s).unwrap();
            format!("(some ({},{}))", h.physical_ms, h.logical)
        }
        _ => "none".into(),
    };
    let fact = escrow::project_resource_fact(&resource_rule(), a).unwrap();
    let bindings = if let Some(f) = &fact {
        list(f.bindings.iter().flatten().map(|v| {
            let SExpr::List(xs) = v else { panic!("cast") };
            format!(
                "⟨{},{}⟩",
                string(text(&xs[0])),
                list(xs[1..].iter().map(|v| string(text(v))))
            )
        }))
    } else {
        "[]".into()
    };
    let allocations = |key: &str| {
        if let Some(v) = fact.as_ref().and_then(|f| f.fields.get(key)) {
            let xs = escrow::allocations(v).unwrap();
            list(xs.iter().map(|(account, n)| {
                format!(
                    "({}, ({}))",
                    string(account),
                    if control == Control::ResourceAllocation && key == "alloc" && account == "@m0"
                    {
                        n + 1
                    } else {
                        *n
                    }
                )
            }))
        } else {
            "[]".into()
        }
    };
    format!("{{ act := ⟨{id},{},{},{},{},{}⟩, stamp := {stamp}, cause := {cause}, cast := {}, bindings := {bindings}, initFlag := {}, allocations := {}, headroom := {} }}",string(&a.verb),string(&a.signer),list(predecessors.iter().map(ToString::to_string)),fields,list(refs(a).iter().map(|id|ranks[id].to_string())),fact.as_ref().is_some_and(|f|f.bindings.is_some()),a.verb=="open",allocations("alloc"),allocations("room"))
}
fn ranks(ops: &[Act]) -> BTreeMap<String, usize> {
    let mut ids: BTreeSet<_> = ops.iter().map(|a| a.address.clone()).collect();
    ids.extend(ops.iter().flat_map(refs));
    ids.extend(
        ops.iter()
            .flat_map(|a| a.predecessors.iter().map(|p| wire_id(p))),
    );
    ids.into_iter()
        .enumerate()
        .map(|(i, id)| (id, i + 1))
        .collect()
}
fn projection(s: &Summary, ranks: &BTreeMap<String, usize>) -> Value {
    let mut value: Value = serde_json::from_str(&s.render_json()).unwrap();
    let old = value["r11"].as_object().unwrap().clone();
    value["r11"] = Value::Object(
        old.into_iter()
            .map(|(id, value)| (ranks[&id].to_string(), value))
            .collect(),
    );
    value
}
fn run_lean(
    root: &Path,
    ops: &[Act],
    ranks: &BTreeMap<String, usize>,
    control: Control,
    path: &Path,
) -> Vec<Value> {
    let events = list(ops.iter().map(|a| event(a, ops, ranks, control)));
    let signers: BTreeSet<_> = ops.iter().map(|a| a.signer.clone()).collect();
    let signers = list(
        signers
            .iter()
            .enumerate()
            .map(|(n, s)| format!("({}, {n})", string(s))),
    );
    let source=format!("import CheckpointAllRustOracle\nopen CheckpointAllRustOracle\ndef events : List Event := {events}\ndef signers : List (String × Nat) := {signers}\ndef main : IO Unit := do\n  for cut in List.range (events.length+1) do\n    for upto in List.range (events.length-cut+1) do\n      IO.println ((observations events signers cut (cut+upto)).compress)\n");
    std::fs::write(path, source).unwrap();
    let out = Command::new("lake")
        .current_dir(root.join("lean-cbcl"))
        .args(["env", "lean", "--run"])
        .arg(path)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "Lean compilation/execution failed (not an observational mismatch):\n{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout)
        .unwrap()
        .lines()
        .filter(|s| !s.trim().is_empty())
        .map(|s| serde_json::from_str(s).expect("Lean emitted JSON observations"))
        .collect()
}
#[test]
#[ignore = "requires pinned Lean4.27 and compiled CheckpointAllRustOracle"]
fn rust_all_sixteen_matches_compiled_lean_snapshots_and_native_fold() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let c = clause();
    let p = protocol();
    let path = std::env::temp_dir().join(format!("CheckpointAllCorpus{}.lean", std::process::id()));
    let mut comparisons = 0;
    let mut records = Vec::new();
    for (case_index, (name, ops)) in corpus().into_iter().enumerate() {
        let ranks = ranks(&ops);
        let mut summary = Summary::new(&c, Some(&p)).unwrap();
        let mut covered = BTreeSet::new();
        let mut history = Vec::new();
        let mut expected = vec![projection(&summary, &ranks)];
        for a in &ops {
            summary.apply(a, |id| covered.contains(id)).unwrap();
            covered.insert(a.address.clone());
            history.push(a.clone());
            assert_eq!(summary.render(), state::fold(&c, Some(&p), &history));
            expected.push(projection(&summary, &ranks));
        }
        // Actual binary resume, not a freshly recomputed Rust prefix substituted for it.
        for cut in 0..=ops.len() {
            let mut saved = Summary::new(&c, Some(&p)).unwrap();
            let mut seen = BTreeSet::new();
            for a in &ops[..cut] {
                saved.apply(a, |id| seen.contains(id)).unwrap();
                seen.insert(a.address.clone());
            }
            let mut saved = Summary::decode_for(&saved.encode(), &c, Some(&p)).unwrap();
            assert_eq!(projection(&saved, &ranks), expected[cut]);
            for (i, a) in ops.iter().enumerate().skip(cut) {
                saved.apply(a, |id| seen.contains(id)).unwrap();
                seen.insert(a.address.clone());
                assert_eq!(projection(&saved, &ranks), expected[i + 1]);
            }
        }
        let nonempty_union_prefixes = expected
            .iter()
            .filter(|v| !v["r10"].as_array().unwrap().is_empty())
            .count();
        if ops.iter().any(|a| a.verb == "put") {
            assert!(nonempty_union_prefixes > 0, "SetUnion must not be vacuous");
        }
        let got = run_lean(&root, &ops, &ranks, Control::None, &path);
        let target_records = (ops.len() + 1) * (ops.len() + 2) / 2;
        assert_eq!(got.len(), target_records);
        for row in &got {
            let upto = row["prefix"].as_u64().unwrap() as usize;
            assert_eq!(
                row["snapshot"], expected[upto],
                "{name}: snapshot cut={} prefix={upto}",
                row["cut"]
            );
            assert_eq!(
                row["fullFold"], expected[upto],
                "{name}: native Lean fold prefix={upto}"
            );
            comparisons += 32;
        }
        let mut controls = Vec::new();
        if case_index == 0 {
            for (control, field) in [
                (Control::SelectedValue, "r11"),
                (Control::CausalParent, "r14"),
                (Control::ResourceAllocation, "r15"),
            ] {
                let altered = run_lean(&root, &ops, &ranks, control, &path);
                assert_eq!(altered.len(), got.len());
                let changed = altered.iter().any(|row| {
                    row["snapshot"][field]
                        != expected[row["prefix"].as_u64().unwrap() as usize][field]
                });
                assert!(
                    changed,
                    "compiled oracle missed typed projection control {field}"
                );
                controls.push(
                    json!({"field":field,"compiled_and_executed":true,"observation_diverged":true}),
                );
            }
        }
        records.push(json!({"case":name,"acts":ops.len(),"prefix_cut_records":got.len(),"all_sixteen_outputs_matched_snapshot_and_fullfold":true,"controls":controls,"nonempty_union_prefixes":nonempty_union_prefixes,"signer_ranks":ops.iter().map(|a|a.signer.clone()).collect::<BTreeSet<_>>().into_iter().enumerate().map(|(n,s)|json!([s,n])).collect::<Vec<_>>(),"address_ranks":ranks,"lean_input_events":list(ops.iter().map(|a|event(a,&ops,&ranks,Control::None)))}));
    }
    let _ = std::fs::remove_file(&path);
    let report = json!({"summary_version":2,"claim":"bounded observational correspondence, not extraction/native-admission or general resource-classifier proof","protocol_port":"known opener edge maps to begin; subsequent single-verb tick predecessors retained, native bound3; no positions fed","resource_port":"independent bootstrap-only account cast+allocations classifier; Pending then Ready; no operations/conflicts/malformed/collective/quorum","rule_observations":comparisons,"cases":records});
    if let Some(path) = std::env::var_os("CHECKPOINT_ALL16_PARITY_OUT") {
        std::fs::write(path, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    }
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}
