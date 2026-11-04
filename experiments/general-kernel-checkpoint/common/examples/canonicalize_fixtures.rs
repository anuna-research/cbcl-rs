use checkpoint_common::Input;
fn main() {
    let mut changes = Vec::new();
    for name in [
        "drawing-0",
        "drawing-1",
        "drawing-8",
        "status-0",
        "status-1",
        "status-8",
    ] {
        let path = format!("fixtures/{name}.json");
        let mut input: Input = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        for (i, r) in input.messages.iter_mut().enumerate() {
            let message =
                cbcl_parser::parse_message(&cbcl_parser::parse(&r.canonical).unwrap()).unwrap();
            let canonical = cbcl_core::intend::canonical_text(&message);
            if canonical != r.canonical {
                changes.push(serde_json::json!({"fixture":name,"record":i,"received":r.canonical,"canonical":canonical}));
                r.canonical = canonical;
            }
        }
        std::fs::write(path, serde_json::to_vec_pretty(&input).unwrap()).unwrap();
    }
    std::fs::write(
        "evidence/fixture-canonicalization.json",
        serde_json::to_vec_pretty(&changes).unwrap(),
    )
    .unwrap();
}
