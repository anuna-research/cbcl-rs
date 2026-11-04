fn main() {
    let bytes = std::fs::read("fixtures/drawing-1.json").unwrap();
    let input: checkpoint_common::Input = serde_json::from_slice(&bytes).unwrap();
    for r in input.messages {
        let m = cbcl_parser::parse_message(&cbcl_parser::parse(&r.canonical).unwrap()).unwrap();
        let c = cbcl_core::intend::canonical_text(&m);
        if c != r.canonical {
            println!("wire={}\ncanonical={}", r.canonical, c);
        }
    }
}
