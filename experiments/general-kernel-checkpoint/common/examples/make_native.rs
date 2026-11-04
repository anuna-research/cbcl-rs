use cbcl_core::{
    intend::{canonical_text, intend, Instance},
    role::AgentKey,
    serializer::serialize,
    sexpr::{Atom, SExpr},
    state::Act,
    store::ThreadId,
};
use cbcl_parser::{parse, parse_and_install_dialect, parse_message};
use checkpoint_common::{Input, Record};
use std::collections::BTreeMap;
fn main() {
    let old: Input =
        serde_json::from_slice(&std::fs::read("fixtures/status-0.json").unwrap()).unwrap();
    let mut source = parse(&old.dialect).unwrap();
    if let SExpr::List(xs) = &mut source {
        xs[1] = SExpr::Atom(Atom::Symbol("checkpoint-status-native".into()));
    }
    let source = serialize(&source);
    let registry = parse_and_install_dialect(&parse(&source).unwrap()).unwrap();
    let dialect = registry.iter().last().unwrap();
    for count in [0, 1, 8] {
        let root=parse_message(&parse("(lang checkpoint-status-native (open @benchmark :title \"Checkpoint benchmark\" :from @owner :thread \"checkpoint-status\" :caused-by begin))").unwrap()).unwrap();
        let mut records = vec![Record {
            signer: "@owner".into(),
            canonical: canonical_text(&root),
        }];
        let mut acts = vec![Act::from_message(root, "@owner").unwrap()];
        for i in 0..count {
            let signer = format!("@writer{}", i % 2);
            let instance =
                Instance::new(dialect, ThreadId("checkpoint-status".into()), &acts).unwrap();
            let mut fields = BTreeMap::new();
            fields.insert(
                "value".into(),
                SExpr::Atom(Atom::Str(format!("state{}", i % 3))),
            );
            let message = intend(&instance, &AgentKey(signer.clone()), "put", fields).unwrap();
            records.push(Record {
                signer: signer.clone(),
                canonical: canonical_text(&message),
            });
            acts.push(Act::from_message(message, &signer).unwrap());
        }
        let input = Input {
            dialect: source.clone(),
            thread: "checkpoint-status".into(),
            messages: records,
        };
        let bytes = serde_json::to_vec_pretty(&input).unwrap();
        let computed = checkpoint_common::compute(&bytes).unwrap();
        // Different SDK/kernel revisions generate different histories. Assert the
        // independently known result of this native eight-write replacement trace.
        let heads = match count {
            0 => "{}",
            1 => "{\"@writer0\":\"state0\"}",
            8 => "{\"@writer0\":\"state0\",\"@writer1\":\"state1\"}",
            _ => unreachable!(),
        };
        let expected =
            format!("{{\"title\":\"Checkpoint benchmark\",\"heads\":{heads},\"count\":{count}}}");
        assert_eq!(computed.state, expected, "native status trace mismatch");
        std::fs::write(format!("fixtures/status-{count}-state.json"), expected).unwrap();
        std::fs::write(format!("fixtures/status-{count}.json"), bytes).unwrap();
    }
}
