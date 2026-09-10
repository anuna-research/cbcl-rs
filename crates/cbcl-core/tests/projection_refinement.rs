//! Live Rust/Lean projection comparison for SPEC-014 REQ-609/610.
//!
//! Rust's real `project` computes the expected output. The test serializes the
//! input and output as Lean data and asks the kernel to reduce the proved Lean
//! function against that output (`decide`, never `native_decide`). This tests the
//! source transcription boundary; it is not a proof of the Rust compiler or of
//! envelope-route derivation. Run after `cd lean-cbcl && lake build` with:
//! `cargo test -p cbcl-core --test projection_refinement -- --ignored`.

use cbcl_core::dialect::{Dialect, PerformativeDef, ResourceBounds};
use cbcl_core::projection::{project, LocalStep};
use cbcl_core::protocol::{CausalProtocol, NodeRef, StepDecl};
use cbcl_core::r6::derive_occupant_envelope_routes;
use cbcl_core::role::{
    AgentKey, Cast, CausalLocality, Endpoint, EnvelopeRoutes, RoleAnnotation, RoleCardinality,
    RoleDecl,
};
use cbcl_core::sexpr::SExpr;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::path::PathBuf;
use std::process::Command;

// Character codepoints avoid assuming Rust and Lean share literal escaping.
fn string(s: &str) -> String {
    format!(
        "(String.ofList [{}])",
        s.chars()
            .map(|c| format!("Char.ofNat {}", c as u32))
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn list<T>(xs: impl IntoIterator<Item = T>, f: impl Fn(T) -> String) -> String {
    format!("[{}]", xs.into_iter().map(f).collect::<Vec<_>>().join(","))
}
fn node(n: &NodeRef) -> String {
    match n {
        NodeRef::Single(s) => format!(".single {}", string(s)),
        NodeRef::Any(ns) => format!(".any {}", list(ns, |s| string(s))),
        NodeRef::All(ns) => format!(".all {}", list(ns, |s| string(s))),
    }
}
fn protocol(cp: &Option<CausalProtocol>) -> String {
    match cp {
        None => "none".into(),
        Some(cp) => format!(
            "some {}",
            list(&cp.steps, |(key, st)| format!(
                "({}, ⟨{}, {}, {}⟩)",
                string(key),
                string(&st.performative),
                list(&st.predecessors, node),
                list(&st.successors, node)
            ))
        ),
    }
}
fn performative(p: &PerformativeDef) -> String {
    let ann = p.role.as_ref().map_or("none".into(), |a| {
        format!("some ⟨{}, {}⟩", string(&a.from), list(&a.to, |r| string(r)))
    });
    format!("⟨{}, {}⟩", string(&p.name), ann)
}
fn local_step(s: Option<&LocalStep>) -> String {
    match s {
        None => "none",
        Some(LocalStep::Send) => "some .send",
        Some(LocalStep::Recv) => "some .recv",
    }
    .into()
}
fn perf(name: &str, sender: Option<&str>, recipients: &[&str]) -> PerformativeDef {
    PerformativeDef {
        name: name.into(),
        params: vec![],
        template: SExpr::List(vec![]),
        role: sender.map(|from| RoleAnnotation {
            from: from.into(),
            to: recipients.iter().map(|r| (*r).into()).collect(),
        }),
    }
}
fn fixture(seed: usize) -> (Dialect, Endpoint, Option<Cast>) {
    let mut perfs = vec![
        perf("p", Some("r0"), &["r1"]),
        perf("self", Some("r0"), &["r0"]),
        perf("bystander", Some("r2"), &[]),
        perf("unannotated", None, &[]),
        perf("unicode-λ#1", Some("r1"), &["r0", "r2"]),
    ];
    // Duplicate declarations pin last relevant insertion and no deletion by
    // later unannotated/bystander entries, even on uninstalled dialect inputs.
    match seed % 5 {
        1 => perfs.push(perf("p", Some("r1"), &["r0"])),
        2 => perfs.push(perf("p", Some("r2"), &[])),
        3 => perfs.push(perf("p", None, &[])),
        4 => perfs.reverse(),
        _ => {}
    }
    let mut steps = BTreeMap::new();
    for (index, p) in perfs.iter().enumerate() {
        let predecessors = match (seed + index) % 5 {
            0 => vec![],
            1 => vec![NodeRef::Single("begin".into())],
            2 => vec![NodeRef::Any(BTreeSet::from(["p".into(), "self".into()]))],
            3 => vec![NodeRef::All(BTreeSet::from([
                "p".into(),
                "unicode-λ#1".into(),
            ]))],
            _ => vec![
                NodeRef::Any(BTreeSet::new()),
                NodeRef::All(BTreeSet::new()),
                NodeRef::Single("bystander".into()),
                NodeRef::All(BTreeSet::from(["p".into()])),
            ],
        };
        steps.insert(
            p.name.clone(),
            StepDecl {
                // Occasionally distinct from the key: neither may be normalized away.
                performative: if seed % 11 == 0 {
                    format!("{}-stored", p.name)
                } else {
                    p.name.clone()
                },
                predecessors,
                successors: vec![
                    NodeRef::Single("end".into()),
                    NodeRef::All(BTreeSet::from(["self".into()])),
                ],
            },
        );
    }
    let cp = match seed % 7 {
        0 => None,
        1 => Some(CausalProtocol {
            steps: BTreeMap::new(),
        }),
        _ => Some(CausalProtocol { steps }),
    };
    let d = Dialect {
        name: "projection-refinement".into(),
        extends: vec![],
        author: None,
        performatives: perfs,
        resources: ResourceBounds {
            max_depth: 8,
            max_expansion_size: 1024,
            verification_time_ms: 10,
        },
        examples: vec![],
        signature: None,
        hash: None,
        protocol: None,
        causal_protocol: cp,
        shapes: vec![],
        roles: vec![RoleDecl {
            name: "r0".into(),
            cardinality: RoleCardinality::Indexed,
        }],
        causal_locality: if seed % 2 == 0 {
            CausalLocality::Reject
        } else {
            CausalLocality::Derive(EnvelopeRoutes(BTreeMap::from([
                (
                    "bystander".into(),
                    BTreeSet::from(["r0".into(), "r1".into()]),
                ),
                ("envelope-only".into(), BTreeSet::from(["r0".into()])),
            ])))
        },
    };
    let endpoint = Endpoint {
        role: ["r0", "r1", "r2", "missing"][(seed / 5) % 4].into(),
        occupant: ((seed / 7) % 3 != 0).then(|| AgentKey("@a".into())),
    };
    let cast = ((seed / 3) % 4 < 2).then(|| Cast {
        singleton: BTreeMap::new(),
        indexed: BTreeMap::from([(
            "r0".into(),
            BTreeSet::from([AgentKey("@a".into()), AgentKey("@b".into())]),
        )]),
        dialect_pin: None,
    });
    (d, endpoint, cast)
}

// A rooted, causally local chain exercises the theorem's intended domain.
fn clean_fixture(role: &str) -> (Dialect, Endpoint, Option<Cast>) {
    let (mut d, mut endpoint, _) = fixture(0);
    d.performatives = vec![
        perf("p", Some("r0"), &["r1"]),
        perf("q", Some("r1"), &["r0"]),
    ];
    d.roles = ["r0", "r1"]
        .into_iter()
        .map(|name| RoleDecl {
            name: name.into(),
            cardinality: RoleCardinality::Singleton,
        })
        .collect();
    d.causal_locality = CausalLocality::Reject;
    d.causal_protocol = Some(CausalProtocol {
        steps: [
            ("begin", vec![], vec![NodeRef::Single("p".into())]),
            (
                "p",
                vec![NodeRef::Single("begin".into())],
                vec![NodeRef::Single("q".into())],
            ),
            ("q", vec![NodeRef::Single("p".into())], vec![]),
        ]
        .into_iter()
        .map(|(name, predecessors, successors)| {
            (
                name.into(),
                StepDecl {
                    performative: name.into(),
                    predecessors,
                    successors,
                },
            )
        })
        .collect(),
    });
    endpoint.role = role.into();
    endpoint.occupant = None;
    assert!(cbcl_core::r6::r6_violations(&d).is_empty());
    (d, endpoint, None)
}

#[test]
#[ignore = "requires the pinned Lean toolchain and a built ConcreteProjection module"]
fn rust_projection_matches_kernel_reduction() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let temp = std::env::temp_dir().join(format!(
        "cbcl-projection-refinement-{}.lean",
        std::process::id()
    ));
    let mut source = String::from("import LeanCbcl.ConcreteProjection\nopen LeanCbcl.ConcreteProjection\nset_option maxRecDepth 8192\nset_option maxHeartbeats 2000000\n");
    let mut nonempty_occupant_routes = 0;
    for i in 0..144 {
        let (d, endpoint, cast) = if i < 140 {
            fixture(i)
        } else {
            clean_fixture(["r0", "r1", "bystander", ""][i - 140])
        };
        let actual = project(&d, &endpoint, cast.as_ref());
        let role_routes = match &d.causal_locality {
            CausalLocality::Reject => BTreeMap::new(),
            CausalLocality::Derive(routes) => routes.0.clone(),
        };
        let occ = cast
            .as_ref()
            .map(|c| derive_occupant_envelope_routes(&d, c))
            .unwrap_or_default();
        nonempty_occupant_routes += usize::from(!occ.0.is_empty());
        // Probe the complete union of possible inserted keys, plus absent keys.
        let names: BTreeSet<String> = d
            .performatives
            .iter()
            .map(|p| p.name.clone())
            .chain(role_routes.keys().cloned())
            .chain(occ.0.keys().cloned())
            .chain(actual.steps.keys().cloned())
            .chain(actual.expect_envelopes.iter().cloned())
            .chain(["absent".into(), "begin".into(), "".into()])
            .collect();
        writeln!(
            source,
            "def ps{i} : List Performative := {}",
            list(&d.performatives, performative)
        )
        .unwrap();
        writeln!(
            source,
            "def cp{i} : Option Protocol := {}",
            protocol(&d.causal_protocol)
        )
        .unwrap();
        writeln!(
            source,
            "def routes{i} : Routes := ⟨{}, {}, {}, {}, {}⟩",
            matches!(d.causal_locality, CausalLocality::Derive(_)),
            list(&role_routes, |(p, rs)| format!(
                "({}, {})",
                string(p),
                list(rs, |r| string(r))
            )),
            list(&occ.0, |(p, ks)| format!(
                "({}, {})",
                string(p),
                list(ks, |k| string(&k.0))
            )),
            cast.is_some(),
            endpoint
                .occupant
                .as_ref()
                .map_or("none".into(), |k| format!("some {}", string(&k.0)))
        )
        .unwrap();
        writeln!(
            source,
            "def result{i} := project ps{i} cp{i} {} routes{i}",
            string(&endpoint.role)
        )
        .unwrap();
        writeln!(
            source,
            "example : result{i}.protocol = {} := by decide",
            protocol(&actual.protocol)
        )
        .unwrap();
        if i >= 140 {
            writeln!(
                source,
                "example : checkAnnotationsConsistent ps{i} = true := by decide"
            )
            .unwrap();
        }
        for name in &names {
            let annotation = d.find_performative(name).and_then(|p| p.role.as_ref());
            let expected = annotation.map_or("none".into(), |a| {
                format!("some ⟨{}, {}⟩", string(&a.from), list(&a.to, |r| string(r)))
            });
            writeln!(
                source,
                "example : annotationAt ps{i} {} = {} := by decide",
                string(name),
                expected
            )
            .unwrap();

            writeln!(
                source,
                "example : result{i}.steps {} = {} := by decide",
                string(name),
                local_step(actual.steps.get(name))
            )
            .unwrap();
            writeln!(
                source,
                "example : result{i}.expectEnvelopes {} = {} := by decide",
                string(name),
                actual.expect_envelopes.contains(name)
            )
            .unwrap();
        }
    }
    assert!(
        nonempty_occupant_routes > 0,
        "fixture must exercise occupant route handling"
    );
    std::fs::write(&temp, source).unwrap();
    let output = Command::new("lake")
        .args(["env", "lean"])
        .arg(&temp)
        .current_dir(root.join("lean-cbcl"))
        .output()
        .expect("run pinned Lean via lake");
    // Keep failing input available for diagnosis; successful runs leave no file.
    assert!(
        output.status.success(),
        "Lean/Rust mismatch; input {}\n{}\n{}",
        temp.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("sorry"),
        "kernel comparison must not admit a proof"
    );
    std::fs::remove_file(temp).unwrap();
}
