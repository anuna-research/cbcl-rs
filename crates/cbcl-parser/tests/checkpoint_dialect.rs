//! Native installation/admission coverage for SPEC-035 CON-3504.
extern crate alloc;

// Also permits this disjoint task to run before the parent exposes the module.
pub use cbcl_parser::{parse, parse_and_install_dialect, parse_dialect};
#[path = "../src/checkpoint_dialect.rs"]
mod checkpoint_dialect;

use cbcl_core::canonical::{dialect_hash, dialect_name};
use cbcl_core::dialect::Dialect;
use cbcl_core::state::Act;
use cbcl_core::store::ThreadId;
use cbcl_parser::parse_message;
use cbcl_parser::state_exports::{admit, Admission};

fn act(text: &str, signer: &str) -> Act {
    Act::from_message(parse_message(&parse(text).unwrap()).unwrap(), signer).unwrap()
}
fn scope() -> &'static str {
    ":target \"target\" :context \"context\" :policy \"policy\" :profile \"profile\""
}
fn message(d: &Dialect, verb: &str, signer: &str, parent: &str, extra: &str) -> Act {
    act(&format!("(signed {signer} (lang {} ({verb} (@init @a @b) {} {extra} :caused-by {parent} :thread \"checkpoints\" :from {signer})))", d.name, scope()), signer)
}
fn bootstrap(d: &Dialect) -> Vec<Act> {
    let root = act("(with-roles ((initializer @init) (member @a @b)) (signed @init (hello :thread \"checkpoints\" :caused-by begin)))", "@init");
    let open = message(d, "open", "@init", &root.address, ":version 1");
    vec![root, open]
}
fn verdict(d: &Dialect, history: &[Act], a: &Act) -> Admission {
    admit(d, &ThreadId("checkpoints".into()), history, a)
}

#[test]
fn bundled_definition_installs_under_native_rules_and_has_no_truth_gate() {
    let d = checkpoint_dialect::builtin().unwrap();
    assert!(cbcl_core::r1::verify_r1_dialect(&d));
    assert!(cbcl_core::r2::verify_r2(&d));
    assert!(cbcl_core::r3::verify_r3(&d));
    assert!(cbcl_core::r5::verify_r5(&d));
    assert!(cbcl_core::r6::r6_violations(&d).is_empty());
    assert!(cbcl_core::r7::r7_violations(&d).is_empty());
    assert!(d.state.is_none());
    assert_eq!(d.name, dialect_name(&d));
    assert_eq!(d.hash.as_deref(), Some(dialect_hash(&d).as_str()));
}

#[test]
fn code_pin_matches_known_vector_and_ignores_source_formatting() {
    let d = checkpoint_dialect::builtin().unwrap();
    assert_eq!(
        dialect_hash(&d),
        "sha256:59d337319e0df5acf2f99488e6c4509cd8902c90d38c8fe1bdd87d81a45acd2a"
    );
    let reformatted = format!("; another comment\n{}\n", checkpoint_dialect::SOURCE);
    let mut form = parse(&reformatted).unwrap();
    if let cbcl_core::sexpr::SExpr::List(items) = &mut form {
        items[1] = cbcl_core::sexpr::SExpr::Atom(cbcl_core::sexpr::Atom::Symbol(d.name.clone()));
    }
    let registry = parse_and_install_dialect(&form).unwrap();
    assert_eq!(
        dialect_hash(registry.iter().last().unwrap()),
        dialect_hash(&d)
    );
}

#[test]
fn source_alias_is_not_the_builtin_authority() {
    let d = checkpoint_dialect::builtin().unwrap();
    let alias = parse_and_install_dialect(&parse(checkpoint_dialect::SOURCE).unwrap()).unwrap();
    let alias = alias.iter().last().unwrap();
    assert_eq!(alias.name, "checkpoint");
    assert_ne!(alias.name, d.name);
    assert_ne!(dialect_hash(alias), dialect_hash(&d));
    let changed = checkpoint_dialect::SOURCE
        .replace("(require :manifest string)", "(require :manifest integer)");
    assert_ne!(
        dialect_name(&parse_dialect(&parse(&changed).unwrap()).unwrap()),
        d.name
    );
}

#[test]
fn native_cast_and_opener_allow_independent_member_acts_without_history() {
    let d = checkpoint_dialect::builtin().unwrap();
    let history = bootstrap(&d);
    assert_eq!(verdict(&d, &[], &history[0]), Admission::Accepted);
    assert_eq!(verdict(&d, &history[..1], &history[1]), Admission::Accepted);
    for signer in ["@a", "@b"] {
        for (verb, extra) in [
            ("propose", ":manifest \"m\" :descriptor \"d\""),
            ("endorse", ":manifest \"m\""),
            (
                "publish",
                ":manifest \"m\" :certificate \"c\" :locations ()",
            ),
        ] {
            let a = message(&d, verb, signer, &history[1].address, extra);
            assert_eq!(
                verdict(&d, &history, &a),
                Admission::Accepted,
                "{verb} by {signer}"
            );
        }
    }
    let bad_open = message(&d, "open", "@a", &history[0].address, ":version 1");
    assert!(matches!(
        verdict(&d, &history[..1], &bad_open),
        Admission::Rejected(_)
    ));
    for signer in ["@init", "@outsider"] {
        let a = message(
            &d,
            "endorse",
            signer,
            &history[1].address,
            ":manifest \"m\"",
        );
        assert!(matches!(verdict(&d, &history, &a), Admission::Rejected(_)));
    }
    let first = message(&d, "endorse", "@a", &history[1].address, ":manifest \"m\"");
    let mut extended = history.clone();
    extended.push(first.clone());
    let chained = message(&d, "endorse", "@b", &first.address, ":manifest \"m\"");
    assert!(matches!(
        verdict(&d, &extended, &chained),
        Admission::Rejected(_)
    ));
    let root_parent = message(&d, "endorse", "@a", &history[0].address, ":manifest \"m\"");
    assert!(matches!(
        verdict(&d, &history, &root_parent),
        Admission::Rejected(_)
    ));
    let good = cbcl_core::intend::canonical_text(&first.message);
    let extra_parent = good.replace(
        &format!(":caused-by {}", history[1].address),
        &format!(":caused-by ({} {})", history[1].address, history[0].address),
    );
    assert!(matches!(
        verdict(&d, &history, &act(&extra_parent, "@a")),
        Admission::Rejected(_)
    ));
    let wrong_recipients = good.replace("(@a @b @init)", "(@a @b)");
    assert_ne!(wrong_recipients, good);
    assert!(matches!(
        verdict(&d, &history, &act(&wrong_recipients, "@a")),
        Admission::Rejected(_)
    ));
}

#[test]
fn native_shapes_reject_missing_and_wrong_typed_payloads() {
    let d = checkpoint_dialect::builtin().unwrap();
    let history = bootstrap(&d);
    for (verb, extra) in [
        ("open", ":version \"1\""),
        ("propose", ":manifest \"m\""),
        ("propose", ":manifest \"m\" :descriptor 1"),
        ("endorse", ":manifest 1"),
        (
            "publish",
            ":manifest \"m\" :certificate \"c\" :locations \"url\"",
        ),
        ("publish", ":manifest \"m\" :locations ()"),
    ] {
        let (signer, parent, accepted) = if verb == "open" {
            ("@init", &history[0].address, &history[..1])
        } else {
            ("@a", &history[1].address, &history[..])
        };
        let a = message(&d, verb, signer, parent, extra);
        assert!(
            matches!(verdict(&d, accepted, &a), Admission::Rejected(_)),
            "{verb} {extra}"
        );
    }
    for field in ["target", "context", "policy", "profile"] {
        let good = message(&d, "endorse", "@a", &history[1].address, ":manifest \"m\"");
        let text = cbcl_core::intend::canonical_text(&good.message);
        let changed = text.replace(&format!(":{field} \"{field}\""), &format!(":{field} 7"));
        let a = act(&changed, "@a");
        assert!(
            matches!(verdict(&d, &history, &a), Admission::Rejected(_)),
            "{field}"
        );
    }
}
