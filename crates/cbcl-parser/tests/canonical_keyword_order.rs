//! SPEC-019 REQ-1949 / TEST-1970: one spelling per act. The receipt rejects a
//! state-bearing act whose keyword parameters are not in canonical order, and
//! the binder emits that order.
use cbcl_core::intend::{intend, Instance};
use cbcl_core::r7::verify_state_shape;
use cbcl_core::role::AgentKey;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::state::Act;
use cbcl_core::store::ThreadId;
use cbcl_parser::{parse, parse_dialect, parse_message};
use std::collections::BTreeMap;

const COIN: &str = include_str!("../../../dialects/example-coin.cbcl");

fn dialect() -> cbcl_core::dialect::Dialect {
    parse_dialect(&parse(COIN).unwrap()).unwrap()
}
fn act(s: &str, signer: &str) -> Act {
    Act::from_message(parse_message(&parse(s).unwrap()).unwrap(), signer).unwrap()
}
fn receipt(d: &cbcl_core::dialect::Dialect, s: &str) -> Result<(), String> {
    verify_state_shape(d, &parse_message(&parse(s).unwrap()).unwrap())
        .map_err(|v| format!("{}: {}", v.rule, v.detail))
}
fn base(d: &cbcl_core::dialect::Dialect) -> Vec<Act> {
    let root = act("(with-roles ((issuer @treasury) (holder @treasury @alice @bob)) (signed @treasury (hello :thread \"coin-1\" :caused-by begin)))", "@treasury");
    let open = act(&format!("(signed @treasury (lang {} (open (@alice @bob @treasury) :name \"Coin\" :allocations ((@treasury 1000) (@alice 0) (@bob 0)) :from @treasury :thread \"coin-1\" :caused-by {})))", d.name, root.address), "@treasury");
    vec![root, open]
}

#[test]
fn declared_order_is_accepted_and_reversed_order_is_rejected() {
    let d = dialect();
    let acts = base(&d);
    let open = &acts[1].address;
    let canonical = format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :recipient @alice :amount 100 :escrow-prev {open} :escrow-deps () :from @treasury :thread \"coin-1\" :caused-by {open})))");
    assert_eq!(receipt(&d, &canonical), Ok(()));
    let reversed = format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :amount 100 :recipient @alice :escrow-prev {open} :escrow-deps () :from @treasury :thread \"coin-1\" :caused-by {open})))");
    let err = receipt(&d, &reversed).unwrap_err();
    assert!(err.starts_with("order:"), "{err}");
    assert!(err.contains(":recipient after :amount"), "{err}");
}

#[test]
fn binder_emits_the_canonical_spelling() {
    let d = dialect();
    let acts = base(&d);
    let open = acts[1].address.clone();
    let inst = Instance::new(&d, ThreadId("coin-1".into()), &acts).unwrap();
    let fields = BTreeMap::from([
        (
            "recipient".to_string(),
            SExpr::Atom(Atom::Symbol("@alice".into())),
        ),
        ("amount".to_string(), SExpr::Atom(Atom::Num(100))),
    ]);
    let built = Act::from_message(
        intend(&inst, &AgentKey("@treasury".into()), "pay", fields).unwrap(),
        "@treasury",
    )
    .unwrap();
    let written = act(&format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :recipient @alice :amount 100 :escrow-prev {open} :escrow-deps () :from @treasury :thread \"coin-1\" :caused-by {open})))"), "@treasury");
    assert_eq!(
        built.address, written.address,
        "binder output is the declared-order spelling"
    );
}

#[test]
fn compiler_and_routing_fields_have_fixed_positions() {
    let d = dialect();
    let acts = base(&d);
    let open = &acts[1].address;
    let deps_first = format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :recipient @alice :amount 100 :escrow-deps () :escrow-prev {open} :from @treasury :thread \"coin-1\" :caused-by {open})))");
    assert!(receipt(&d, &deps_first)
        .unwrap_err()
        .contains(":escrow-prev after :escrow-deps"));
    let from_first = format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :recipient @alice :amount 100 :from @treasury :escrow-prev {open} :escrow-deps () :thread \"coin-1\" :caused-by {open})))");
    assert!(receipt(&d, &from_first)
        .unwrap_err()
        .contains(":escrow-prev after :from"));
    let business_last = format!("(signed @treasury (lang example-coin (pay (@alice @bob @treasury) () :escrow-prev {open} :escrow-deps () :recipient @alice :amount 100 :from @treasury :thread \"coin-1\" :caused-by {open})))");
    assert!(receipt(&d, &business_last)
        .unwrap_err()
        .contains(":recipient after :escrow-deps"));
}

#[test]
fn single_and_absent_business_fields_pass() {
    let d = dialect();
    let acts = base(&d);
    let open = &acts[1].address;
    let burn = format!("(signed @alice (lang example-coin (burn (@alice @bob @treasury) () :amount 1 :escrow-prev {open} :escrow-deps () :from @alice :thread \"coin-1\" :caused-by {open})))");
    assert_eq!(receipt(&d, &burn), Ok(()));
    // `open` has two business fields in declared order and no compiler fields.
    let open_text = format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) :name \"Coin\" :allocations ((@treasury 1)) :from @treasury :thread \"coin-1\" :caused-by {})))", acts[0].address);
    assert_eq!(receipt(&d, &open_text), Ok(()));
    let open_swapped = format!("(signed @treasury (lang example-coin (open (@alice @bob @treasury) :allocations ((@treasury 1)) :name \"Coin\" :from @treasury :thread \"coin-1\" :caused-by {})))", acts[0].address);
    assert!(receipt(&d, &open_swapped)
        .unwrap_err()
        .contains(":name after :allocations"));
}
