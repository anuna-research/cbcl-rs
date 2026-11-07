//! SPEC-038 TEST-3808: declarations are data, laws are installation gates.
use cbcl_core::lattice::{factor, Ctx};
use cbcl_core::state::{fold, render_json, Act};
use cbcl_parser::{parse, parse_dialect, parse_message, state_exports};
use serde_json::{json, Value};

fn source(n: usize, projection: &str, threshold: &str) -> String {
    let elements = (0..n)
        .map(|i| format!("e{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    let mut rows = String::new();
    for a in 0..n {
        for b in 0..n {
            rows.push_str(&format!(" (e{a} e{b} e{})", a.max(b)));
        }
    }
    let contributions = (0..n)
        .map(|i| format!(" (:phase \"e{i}\" e{i})"))
        .collect::<String>();
    format!(
        "(define finite-demo (cbcl) @anuna
      (extend open (to) (tell to)) (extend mark (to phase) (tell to :phase phase))
      (shape mark (require :phase string)) (protocol (then begin open) (then open mark))
      (state (lattice rank (elements {elements}) (bottom e0) (top e{}) (join {rows}))
        (phase (lift mark (into rank) (contribute {contributions}) {projection})) {threshold}))",
        n - 1
    )
}

fn install(src: &str) -> Result<(), String> {
    state_exports::parse_and_install_dialect(&parse(src).unwrap()).map(|_| ())
}

fn act(text: &str, who: &str) -> Act {
    Act::from_message(parse_message(&parse(text).unwrap()).unwrap(), who).unwrap()
}

fn history() -> Vec<Act> {
    let open = act(
        "(lang finite-demo (open @room :caused-by begin :thread \"t\" :from @a))",
        "@a",
    );
    let mark = act(
        &format!(
            "(lang finite-demo (mark @room :phase \"e1\" :caused-by {} :thread \"t\" :from @a))",
            open.address
        ),
        "@a",
    );
    vec![open, mark]
}

fn read(src: &str, acts: &[Act]) -> Value {
    let d = parse_dialect(&parse(src).unwrap()).unwrap();
    serde_json::from_str(&render_json(&fold(
        d.state.as_ref().unwrap(),
        d.causal_protocol.as_ref(),
        acts,
    )))
    .unwrap()
}

#[test]
fn verified_finite_lift_matches_display_and_union_law() {
    let src = source(3, "", "");
    install(&src).unwrap();
    let acts = history();
    assert_eq!(read(&src, &[])["phase"], "e0");
    assert_eq!(read(&src, &acts)["phase"], "e1");
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let clause = d.state.as_ref().unwrap();
    let f = factor(clause.rule_of("phase").unwrap()).unwrap();
    assert_eq!(Ctx::new(clause, &acts).display(&f, &[]).render(), "\"e1\"");
    let left = vec![acts[0].clone()];
    let right = acts.clone();
    assert_eq!(
        Ctx::new(clause, &acts).eval(&f.term),
        Ctx::new(clause, &left)
            .eval(&f.term)
            .join(Ctx::new(clause, &right).eval(&f.term))
    );
    let mut duplicates = acts.clone();
    duplicates.reverse();
    duplicates.extend(acts);
    assert_eq!(read(&src, &duplicates)["phase"], "e1");
}

#[test]
fn top_is_an_attributable_terminal_fault() {
    let src = source(3, "", "(threshold ready phase \"e1\")");
    install(&src).unwrap();
    let mut acts = history();
    assert_eq!(read(&src, &acts)["ready"]["status"], "reached");
    let top = act(
        &format!(
            "(lang finite-demo (mark @room :phase \"e2\" :caused-by {} :thread \"t\" :from @b))",
            acts[0].address
        ),
        "@b",
    );
    acts.push(top.clone());
    let value = read(&src, &acts);
    assert_eq!(value["phase"]["status"], "fault");
    assert_eq!(value["ready"], value["phase"]);
    assert!(value["phase"]["evidence"]
        .as_array()
        .unwrap()
        .contains(&json!(top.address)));
}

#[test]
fn invalid_join_tables_are_rejected_with_law_and_witness() {
    let src = source(3, "", "");
    let e = install(&src.replace("(e0 e2 e2)", "(e0 e2 e1)")).unwrap_err();
    assert!(e.contains("not commutative") && e.contains("e0 e2"), "{e}");
    let e = install(&src.replace("(e1 e2 e2)", "")).unwrap_err();
    assert!(e.contains("not total") && e.contains("e1 e2"), "{e}");
    let e = install(&src.replace("(e0 e1 e1)", "(e0 e1 unknown)")).unwrap_err();
    assert!(e.contains("undeclared element 'unknown'"), "{e}");
    assert!(
        install(&src.replace("(:phase \"e1\" e1)", "(:phase \"e1\" unknown)"))
            .unwrap_err()
            .contains("undeclared element")
    );
}

#[test]
fn associativity_idempotence_and_boundary_laws_are_checked_independently() {
    let bad = source(5, "", "")
        .replace("(e1 e2 e2)", "(e1 e2 e3)")
        .replace("(e2 e1 e2)", "(e2 e1 e3)")
        .replace("(e2 e3 e3)", "(e2 e3 e4)")
        .replace("(e3 e2 e3)", "(e3 e2 e4)");
    let error = install(&bad).unwrap_err();
    assert!(
        error.contains("not associative") && error.contains("e1 e2 e2"),
        "{error}"
    );
    let mut constant = source(3, "", "");
    for a in 0..3 {
        for b in 0..3 {
            constant = constant.replace(
                &format!("(e{a} e{b} e{})", a.max(b)),
                &format!("(e{a} e{b} e2)"),
            );
        }
    }
    assert!(install(&constant).unwrap_err().contains("not idempotent"));
    let error = install(&source(3, "", "").replace("(bottom e0)", "(bottom e1)")).unwrap_err();
    assert!(error.contains("bottom not identity"), "{error}");
    let error = install(&source(3, "", "").replace("(top e2)", "(top e1)")).unwrap_err();
    assert!(error.contains("top not absorbing"), "{error}");
}

#[test]
fn incompatible_finite_outcomes_are_stable_until_an_explicit_conflict() {
    let src = source(4, "", "(threshold result phase \"e1\" \"e2\")")
        .replace("(e1 e2 e2)", "(e1 e2 e3)")
        .replace("(e2 e1 e2)", "(e2 e1 e3)");
    install(&src).unwrap();
    let left = history();
    let second = act(
        &format!(
            "(lang finite-demo (mark @room :phase \"e2\" :caused-by {} :thread \"t\" :from @b))",
            left[0].address
        ),
        "@b",
    );
    assert_eq!(read(&src, &left)["result"]["element"], "e1");
    let right = vec![left[0].clone(), second.clone()];
    let union: Vec<Act> = left.iter().chain(&right).cloned().collect();
    let d = parse_dialect(&parse(&src).unwrap()).unwrap();
    let clause = d.state.as_ref().unwrap();
    let f = factor(clause.rule_of("phase").unwrap()).unwrap();
    assert_eq!(
        Ctx::new(clause, &union).eval(&f.term),
        Ctx::new(clause, &left)
            .eval(&f.term)
            .join(Ctx::new(clause, &right).eval(&f.term))
    );
    let merged = read(&src, &union);
    assert_eq!(merged["result"]["status"], "fault");
    let mut evidence = vec![left[1].address.clone(), second.address];
    evidence.sort();
    assert_eq!(merged["result"]["evidence"], json!(evidence));
    let mut reverse = union;
    reverse.reverse();
    assert_eq!(read(&src, &reverse), merged);
}

#[test]
fn projection_stability_is_verified_and_snapshot_projection_stays_available() {
    let stable = "(project stable ((e0 0) (e1 1) (e2 2)))";
    let src = source(3, stable, "(threshold ready phase 1)");
    install(&src).unwrap();
    assert_eq!(read(&src, &history())["ready"]["status"], "reached");
    let inverted = "(project stable ((e0 0) (e1 2) (e2 1)))";
    let e = install(&source(3, inverted, "")).unwrap_err();
    assert!(e.contains("not monotone") && e.contains("e1 e2"), "{e}");
    let snapshot = inverted.replace(" stable", "");
    let src = source(3, &snapshot, "");
    install(&src).unwrap();
    assert_eq!(read(&src, &history())["phase"], 2);
    assert!(install(&source(3, &snapshot, "(threshold bad phase 1)")).is_err());
    assert!(
        install(&source(3, stable, "(threshold bad phase \"e1\" 1)"))
            .unwrap_err()
            .contains("compatible")
    );
}

#[test]
fn element_count_is_bounded_and_a_64_element_lattice_installs() {
    let bounded = source(4, "", "").replace("(state", "(:state-bounds (max-list 3)) (state");
    assert!(install(&bounded).unwrap_err().contains("max-list"));
    install(&source(64, "", "")).unwrap();
}
