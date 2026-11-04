use cbcl_core::{
    intend::{canonical_text, intend, Instance},
    role::AgentKey,
    sexpr::{Atom, SExpr},
    state::Act,
    store::ThreadId,
};
use cbcl_parser::{parse, parse_and_install_dialect, parse_message};
use checkpoint_common::{Input, Record};
use std::{collections::BTreeMap, fs, path::PathBuf, time::Instant};
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: Input = serde_json::from_slice(&fs::read(&args[1]).unwrap()).unwrap();
    let out = PathBuf::from(&args[2]);
    fs::create_dir_all(&out).unwrap();
    let t = Instant::now();
    let registry = parse_and_install_dialect(&parse(&seed.dialect).unwrap()).unwrap();
    let dialect = registry.iter().last().unwrap();
    let opener = parse_message(&parse(&seed.messages[0].canonical).unwrap()).unwrap();
    let opener = Act::from_message(opener, &seed.messages[0].signer).unwrap();
    let parents = [opener];
    // The drawing protocol declares each chunk caused by open. Independent
    // chunks therefore all reference this opener, as in the existing fixture.
    let instance = Instance::new(dialect, ThreadId(seed.thread.clone()), &parents).unwrap();
    let mut records = vec![seed.messages[0].clone()];
    let mut chunks = serde_json::Map::new();
    for i in 0..999 {
        let key = format!("stroke:{i:06}");
        let x = i % 1199;
        let y = i % 719;
        let data = serde_json::json!([key, "#203e36", 6, x, y, x + 1, y + 1]);
        let mut fields = BTreeMap::new();
        fields.insert("chunk-id".into(), SExpr::Atom(Atom::Str(key.clone())));
        fields.insert(
            "data".into(),
            parse(&format!(
                "(\"{key}\" \"#203e36\" 6 {x} {y} {} {})",
                x + 1,
                y + 1
            ))
            .unwrap(),
        );
        let signer = format!("@writer{}", i % 2);
        let message = intend(&instance, &AgentKey(signer.clone()), "chunk", fields).unwrap();
        records.push(Record {
            signer,
            canonical: canonical_text(&message),
        });
        chunks.insert(key, data);
    }
    let input = Input {
        dialect: seed.dialect,
        thread: seed.thread,
        messages: records,
    };
    assert_eq!(input.messages.len(), 1000);
    let bytes = serde_json::to_vec(&input).unwrap();
    fs::write(out.join("input.json"), &bytes).unwrap();
    let fixture_ms = t.elapsed().as_millis();
    let t = Instant::now();
    let native = checkpoint_common::compute(&bytes).unwrap();
    let expected = serde_json::json!({"title":"Checkpoint benchmark","chunks":chunks,"erased":{}});
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&native.state).unwrap(),
        expected
    );
    assert_eq!(native.journal.count, 1000);
    fs::write(
        out.join("expected.json"),
        serde_json::to_vec_pretty(&native.journal).unwrap(),
    )
    .unwrap();
    fs::write(out.join("state.json"), &native.state).unwrap();
    fs::write(out.join("fixture-metrics.json"),serde_json::to_vec_pretty(&serde_json::json!({"messages":1000,"chunks":999,"input_bytes":bytes.len(),"state_bytes":native.state.len(),"fixture_ms":fixture_ms,"native_ms":t.elapsed().as_millis(),"expected_state":"independent keyed map of 999 distinct drawing payloads","synthetic":true})).unwrap()).unwrap();
}
