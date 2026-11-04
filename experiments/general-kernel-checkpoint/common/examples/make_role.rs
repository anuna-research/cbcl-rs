use cbcl_core::{intend::canonical_text, state::Act};
use cbcl_parser::{parse, parse_message};
use checkpoint_common::{Input, Record};
fn main() {
    let dialect = std::fs::read_to_string("../../dialects/checklist.cbcl")
        .unwrap()
        .lines()
        .filter(|l| !l.trim_start().starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n");
    let mut records = Vec::new();
    let mut push = |text: String, signer: &str| {
        let message = parse_message(&parse(&text).unwrap()).unwrap();
        let canonical = canonical_text(&message);
        let act = Act::from_message(message, signer).unwrap();
        records.push(Record {
            signer: signer.into(),
            canonical,
        });
        act.address
    };
    let root=push("(with-roles ((owner @aria) (member @bo @cy)) (signed @aria (hello :thread \"list-1\" :caused-by begin)))".into(),"@aria");
    let open=push(format!("(signed @aria (lang checklist (open (@aria @bo @cy) :title \"Launch tasks\" :caused-by {root} :thread \"list-1\" :from @aria)))"),"@aria");
    let check=push(format!("(signed @bo (lang checklist (check (@aria @bo @cy) :item \"venue\" :done #f :replaces () :caused-by {open} :thread \"list-1\" :from @bo)))"),"@bo");
    push(format!("(signed @bo (lang checklist (check (@aria @bo @cy) :item \"venue\" :done #t :replaces ({check}) :caused-by {open} :thread \"list-1\" :from @bo)))"),"@bo");
    let input = Input {
        dialect,
        thread: "list-1".into(),
        messages: records,
    };
    let bytes = serde_json::to_vec_pretty(&input).unwrap();
    let result = checkpoint_common::compute(&bytes).unwrap();
    std::fs::write("fixtures/checklist-role.json", bytes).unwrap();
    std::fs::write("fixtures/checklist-role-state.json", result.state).unwrap();
}
