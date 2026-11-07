//! Bounded correspondence evidence, NOT an extraction proof. Run explicitly:
//! CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 cargo test -p cbcl-checkpoint \
//!   --test lean_checkpoint_parity -- --ignored --nocapture
//! Requires built CheckpointSummary/CheckpointCompact Lean modules. The runner
//! executes in lean-cbcl. CHECKPOINT_PARITY_OUT retains the emitted JSON corpus.
#![cfg(feature = "std")]
extern crate alloc;
pub use cbcl_checkpoint::*;
#[allow(dead_code)]
#[path = "../src/test_support.rs"]
mod test_support;
use cbcl_checkpoint::{certificate::SignedMessage, summary::Summary};
use cbcl_core::{
    hlc::Hlc,
    sexpr::{Atom, SExpr},
    state::{Act, Entry, Rule, StateClause},
};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
    process::Command,
};

fn act(
    verb: &str,
    k: &str,
    v: &str,
    signer: &str,
    time: (u64, u32),
    refs: &[String],
    nonce: usize,
) -> Act {
    let text = format!("(lang parity ({verb} (@m0 @m1) :k \"{k}\" :v \"{v}\" :clock \"{}\" :replaces ({}) :nonce {nonce} :sender {signer} :thread \"parity\" :caused-by begin))", Hlc::new(time.0,time.1).render(), refs.iter().map(|r| format!("\"{r}\"")).collect::<Vec<_>>().join(" "));
    SignedMessage::sign(test_support::parse(&text), signer, &test_support::Keys)
        .unwrap()
        .authenticate(&test_support::Keys)
        .unwrap()
}
fn rules() -> StateClause {
    let rules = vec![
        Rule::Initial {
            verb: "init".into(),
            key: "v".into(),
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
fn refs(a: &Act) -> Vec<String> {
    match a.fields.get("replaces") {
        Some(SExpr::List(xs)) => xs
            .iter()
            .map(|x| match x {
                SExpr::Atom(Atom::Str(s) | Atom::Symbol(s)) => s.clone(),
                _ => panic!("reference"),
            })
            .collect(),
        _ => vec![],
    }
}
fn text(v: &SExpr) -> &str {
    match v {
        SExpr::Atom(Atom::Str(s)) => s,
        _ => panic!("string corpus"),
    }
}
fn projection(summary: &Summary, ranks: &BTreeMap<String, usize>) -> Value {
    let wire = serde_json::to_value(summary).unwrap();
    let rendered: Value = serde_json::from_str(&summary.render_json()).unwrap();
    Value::Array(wire["rows"].as_array().unwrap().iter().enumerate().map(|(i,row)| {
        let initial = row.get("Initial");
        let scoped = row.get("Scoped");
        let winner = row.get("LwwRegister");
        let contributions: Vec<&Value> = if let Some(xs) = initial {
            xs.as_array().unwrap().iter().collect()
        } else if let Some(s) = scoped {
            s["live"].as_array().unwrap().iter().collect()
        } else {
            winner.filter(|v| !v.is_null()).into_iter().collect()
        };
        let mut live: Vec<_> = contributions.iter().map(|a| ranks[a["id"].as_str().unwrap()]).collect(); live.sort();
        let pending_rows = scoped.map(|s|s["pending"].as_array().unwrap().as_slice()).unwrap_or(&[]);
        let mut pending: Vec<Value>=pending_rows.iter().map(|p| {
            let bytes: Vec<u8>=serde_json::from_value(p["scope"].clone()).unwrap();
            let scope=if bytes.is_empty() { Value::Null } else { json!(text(&codec::decode_sexpr(&bytes,1024).unwrap())) };
            json!([scope,ranks[p["target"].as_str().unwrap()]])
        }).collect(); pending.sort_by_key(Value::to_string);
        // Initial's proof model permits any two distinct witnesses; Rust keeps
        // the least two. Compare ambiguity cardinality and value, not witnesses.
        json!({"live":if i==0 { Value::Null } else { json!(live) },"witnesses":if i==0 { live.len() } else { 0 },"pending":pending,"value":rendered[format!("r{i}")]})
    }).collect())
}
fn case(name: &str, ops: Vec<Act>) -> Value {
    let mut ids: BTreeSet<String> = ops.iter().map(|a| a.address.clone()).collect();
    ids.extend(ops.iter().flat_map(refs));
    let ranks: BTreeMap<String, usize> = ids
        .into_iter()
        .enumerate()
        .map(|(i, id)| (id, i + 1))
        .collect();
    let signers: BTreeSet<String> = ops.iter().map(|a| a.signer.clone()).collect();
    let clause = rules();
    let mut s = Summary::new(&clause, None).unwrap();
    let mut covered = BTreeSet::new();
    let mut expected = vec![projection(&s, &ranks)];
    for a in &ops {
        s.apply(a, |id| covered.contains(id)).unwrap();
        covered.insert(a.address.clone());
        expected.push(projection(&s, &ranks));
    }
    let cuts: BTreeSet<usize> = [0, 1.min(ops.len()), ops.len() / 2, ops.len()]
        .into_iter()
        .collect();
    for cut in &cuts {
        let mut s = Summary::new(&clause, None).unwrap();
        let mut covered = BTreeSet::new();
        for a in &ops[..*cut] {
            s.apply(a, |id| covered.contains(id)).unwrap();
            covered.insert(a.address.clone());
        }
        let mut s = Summary::decode(&s.encode(), &clause).unwrap();
        assert_eq!(projection(&s, &ranks), expected[*cut]);
        for (i, a) in ops.iter().enumerate().skip(*cut) {
            s.apply(a, |id| covered.contains(id)).unwrap();
            covered.insert(a.address.clone());
            assert_eq!(projection(&s, &ranks), expected[i + 1]);
        }
    }
    let acts: Vec<Value>=ops.iter().map(|a| {
        let clock=Hlc::parse(text(&a.fields["clock"])).unwrap();
        json!({"addr":ranks[&a.address],"verb":a.verb,"signer":a.signer,"fields":[["k",text(&a.fields["k"])],["v",text(&a.fields["v"])]],"replaces":refs(a).iter().map(|id|ranks[id]).collect::<Vec<_>>(),"clock":[clock.physical_ms,clock.logical]})
    }).collect();
    json!({"name":name,"addresses":ranks.iter().map(|(id,n)|json!([id,n])).collect::<Vec<_>>(),"signers":signers.into_iter().enumerate().map(|(n,s)|json!([s,n])).collect::<Vec<_>>(),"acts":acts,"cuts":cuts,"expected":expected})
}
fn corpus() -> Value {
    let a = act("put", "x", "red", "@m0", (10, 0), &[], 1);
    let b = act("put", "x", "blue", "@m1", (10, 0), &[], 2);
    let c = act("put", "x", "green", "@m1", (10, 0), &[], 3);
    let winner = [&b, &c].into_iter().max_by_key(|a| &a.address).unwrap();
    let erase = act(
        "del",
        "x",
        "gone",
        "@m0",
        (11, 0),
        std::slice::from_ref(&winner.address),
        4,
    );
    let cross = act(
        "put",
        "y",
        "yellow",
        "@m1",
        (9, 0),
        std::slice::from_ref(&a.address),
        5,
    );
    let unknown = act("noise", "x", "ignored", "@m0", (1, 0), &[], 6);
    let pending = act(
        "put",
        "x",
        "purple",
        "@m1",
        (12, 0),
        std::slice::from_ref(&unknown.address),
        7,
    );
    let init = act("init", "x", "first", "@m0", (1, 0), &[], 8);
    let init2 = act("init", "x", "second", "@m1", (1, 0), &[], 9);
    let init3 = act("init", "x", "third", "@m0", (1, 0), &[], 10);
    let delayed = act(
        "del",
        "x",
        "gone",
        "@m0",
        (20, 0),
        std::slice::from_ref(&a.address),
        11,
    );
    let transitive = act(
        "put",
        "x",
        "final",
        "@m0",
        (21, 0),
        std::slice::from_ref(&delayed.address),
        12,
    );
    let later = act("put", "x", "logical", "@m0", (10, 1), &[], 13);
    let fixed = vec![
        init.clone(),
        a.clone(),
        b.clone(),
        c.clone(),
        erase,
        cross.clone(),
        pending.clone(),
        unknown.clone(),
        a.clone(),
        init2.clone(),
        later.clone(),
        init3,
    ];
    let mut cases = vec![
        case("ties-winner-removed-cross-key-signers", fixed.clone()),
        case(
            "late-retired-replacer",
            vec![transitive, delayed, a.clone(), a.clone()],
        ),
        case("nonstate-resolves-pending", vec![pending, unknown]),
        case("crosskey-reverse", vec![cross, a]),
    ];
    let mut reverse = fixed.clone();
    reverse.reverse();
    cases.push(case("reverse", reverse));
    for seed in [7_u64, 42, 3506] {
        let mut shuffled = fixed.clone();
        let mut state = seed;
        for i in (1..shuffled.len()).rev() {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            shuffled.swap(i, (state % (i + 1) as u64) as usize);
        }
        cases.push(case(&format!("seed-{seed}"), shuffled));
    }
    json!({"version":1,"claim":"bounded correspondence, not extraction; self replacement is Lean-model-only because native IDs commit replaces","cases":cases})
}
#[test]
#[ignore = "requires Lean 4 and built checkpoint proof modules"]
fn rust_summary_matches_lean_transitions_and_observations() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let retained = std::env::var_os("CHECKPOINT_PARITY_OUT");
    let path = retained.clone().map(PathBuf::from).unwrap_or_else(|| {
        std::env::temp_dir().join(format!(
            "cbcl-checkpoint-parity-{}.json",
            std::process::id()
        ))
    });
    let path = if path.is_absolute() {
        path
    } else {
        std::env::current_dir().unwrap().join(path)
    };
    let corpus = corpus();
    std::fs::write(&path, serde_json::to_vec_pretty(&corpus).unwrap()).unwrap();
    let invoke = |path: &std::path::Path| {
        Command::new("lake")
            .current_dir(root.join("lean-cbcl"))
            .args(["env", "lean", "--run", "CheckpointRustOracle.lean"])
            .arg(path)
            .output()
            .expect("run Lean in lean-cbcl")
    };
    let output = invoke(&path);
    if retained.is_none() {
        let _ = std::fs::remove_file(&path);
    }
    assert!(
        output.status.success(),
        "Lean parity failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    println!("{}", String::from_utf8_lossy(&output.stdout));
    // Prove the sidecar notices discrepancies in each compared component;
    // only emitted test data is mutated, never production code or proof files.
    let mutated_path = std::env::temp_dir().join(format!(
        "cbcl-checkpoint-parity-mutated-{}.json",
        std::process::id()
    ));
    for component in ["live", "pending", "value"] {
        let mut bad = corpus.clone();
        let row = &mut bad["cases"][2]["expected"][1][1];
        row[component] = match component {
            "live" => json!([]),
            "pending" => json!([[null, 999999]]),
            _ => json!(["not-a-rust-value"]),
        };
        std::fs::write(&mutated_path, serde_json::to_vec(&bad).unwrap()).unwrap();
        let rejected = invoke(&mutated_path);
        let _ = std::fs::remove_file(&mutated_path);
        assert!(
            !rejected.status.success(),
            "oracle missed {component} mutation"
        );
        assert!(
            String::from_utf8_lossy(&rejected.stderr).contains("cut 0, prefix 1"),
            "{component} was rejected before observational comparison: {}",
            String::from_utf8_lossy(&rejected.stderr)
        );
    }
    println!("Oracle rejected all 3 deliberate live/pending/value mutations");
}
