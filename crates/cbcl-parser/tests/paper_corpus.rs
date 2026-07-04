//! The corpus study of the EPP paper (§ Evaluation): protocols from the
//! session-types literature, each encoded in concrete CBCL syntax, driven
//! through the real R6 checker.
//!
//! Each test pins the exact `NotCausallyLocal` violation set for the
//! protocol as written, and that the recipient-widened repair passes.
//! These verdicts are the paper's corpus table; if a checker change moves
//! a verdict, this file fails and the table is stale.
//!
//! OAuth is pinned by `paper_oauth.rs`; the indexed-role auction (terminal,
//! announcing, and full-widening variants) by the TEST-608 block of
//! `cbcl-core/src/r6.rs`. This file covers the rest of the corpus with
//! singleton-role encodings (two-phase commit is encoded with three
//! explicit participants so that its fan-in is surface-parseable).

use cbcl_core::r6::r6_violations;
use cbcl_core::role::R6Violation as V;
use cbcl_core::sexpr::SExpr;
use cbcl_parser::parse_dialect;

fn parse(src: &str) -> cbcl_core::dialect::Dialect {
    let sexpr: SExpr = src.parse().expect("corpus dialect must parse as an S-expression");
    parse_dialect(&sexpr).expect("corpus dialect must parse as a dialect")
}

fn ncl(performative: &str, predecessor: &str, role: &str) -> V {
    V::NotCausallyLocal {
        performative: performative.into(),
        predecessor: predecessor.into(),
        role: role.into(),
    }
}

/// Assert the violation set is exactly `expected` (order-insensitive).
fn assert_violations(d: &cbcl_core::dialect::Dialect, mut expected: Vec<V>) {
    let mut got = r6_violations(d);
    let key = |v: &V| format!("{v:?}");
    got.sort_by_key(key);
    expected.sort_by_key(key);
    assert_eq!(got, expected);
}

// --- request-response (folklore two-party RPC) ------------------------------

#[test]
fn request_response_passes_as_written() {
    let d = parse(
        "(define reqresp (cbcl) @corpus
           (:roles (client server))
           (extend rpc-req (payload) :from client :to server
             (tell @server :payload payload :domain reqresp))
           (extend rpc-resp (result) :from server :to client
             (tell @client :result result :domain reqresp))
           (protocol (then begin rpc-req rpc-resp)))",
    );
    assert_violations(&d, vec![]);
}

// --- logistics (EPP paper §3) ------------------------------------------------

fn logistics(with_warehouse: bool) -> String {
    let (roles, warehouse, tail) = if with_warehouse {
        (
            "(shipper tracking-svc warehouse)",
            "(extend dispatch (item) :from warehouse :to shipper
               (tell @shipper :item item :domain logistics))",
            "(then accept dispatch)",
        )
    } else {
        ("(shipper tracking-svc)", "", "")
    };
    format!(
        "(define logistics (cbcl) @corpus
           (:roles {roles})
           (extend track-shipment (item) :from shipper :to tracking-svc
             (tell @tracking-svc :item item :domain logistics))
           (extend accept (item) :from tracking-svc :to shipper
             (tell @shipper :item item :domain logistics))
           (extend reject (item) :from tracking-svc :to shipper
             (tell @shipper :item item :domain logistics))
           {warehouse}
           (protocol (then begin track-shipment (any accept reject)) {tail}))"
    )
}

#[test]
fn logistics_two_party_passes_as_written() {
    assert_violations(&parse(&logistics(false)), vec![]);
}

#[test]
fn warehouse_extension_fails_exactly_at_dispatch() {
    assert_violations(
        &parse(&logistics(true)),
        vec![ncl("dispatch", "accept", "warehouse")],
    );
}

#[test]
fn warehouse_widened_passes() {
    // Repair (a) of §4: route the decision and its causal prefix to warehouse.
    let widened = logistics(true)
        .replace(":from shipper :to tracking-svc", ":from shipper :to (tracking-svc warehouse)")
        .replace(":from tracking-svc :to shipper", ":from tracking-svc :to (shipper warehouse)");
    assert_violations(&parse(&widened), vec![]);
}

// --- two-buyer (Honda–Yoshida–Carbone) ---------------------------------------

fn two_buyer(widened: bool) -> String {
    let (title_to, share_to) = if widened {
        ("(seller buyer2)", "(buyer2 seller)")
    } else {
        ("seller", "buyer2")
    };
    format!(
        "(define twobuyer (cbcl) @corpus
           (:roles (buyer1 buyer2 seller))
           (extend title (name) :from buyer1 :to {title_to}
             (tell @seller :name name :domain twobuyer))
           (extend quote (price) :from seller :to (buyer1 buyer2)
             (tell @buyer1 :price price :domain twobuyer))
           (extend share (amount) :from buyer1 :to {share_to}
             (tell @buyer2 :amount amount :domain twobuyer))
           (extend buy (address) :from buyer2 :to seller
             (tell @seller :address address :domain twobuyer))
           (extend quit (reason) :from buyer2 :to seller
             (tell @seller :reason reason :domain twobuyer))
           (extend date (delivery) :from seller :to buyer2
             (tell @buyer2 :delivery delivery :domain twobuyer))
           (protocol (then begin title quote share (any buy quit))
                     (then buy date)))"
    )
}

#[test]
fn two_buyer_fails_at_quote_and_choice() {
    // buyer2 receives the quote but never saw the title; the seller receives
    // buyer2's decision but never saw buyer1's share.
    assert_violations(
        &parse(&two_buyer(false)),
        vec![
            ncl("quote", "title", "buyer2"),
            ncl("buy", "share", "seller"),
            ncl("quit", "share", "seller"),
        ],
    );
}

#[test]
fn two_buyer_widened_passes() {
    assert_violations(&parse(&two_buyer(true)), vec![]);
}

// --- three-stage pipeline (folklore) ------------------------------------------

fn pipeline(widened: bool) -> String {
    let produce_to = if widened { "(kernel sink)" } else { "kernel" };
    format!(
        "(define pipeline (cbcl) @corpus
           (:roles (source kernel sink))
           (extend produce (chunk) :from source :to {produce_to}
             (tell @kernel :chunk chunk :domain pipeline))
           (extend forward (chunk) :from kernel :to sink
             (tell @sink :chunk chunk :domain pipeline))
           (protocol (then begin produce forward)))"
    )
}

#[test]
fn pipeline_fails_straight_line() {
    // No choice anywhere: the canonical straight-line failure of the paper's
    // \"choice points do not suffice\" remark.
    assert_violations(&parse(&pipeline(false)), vec![ncl("forward", "produce", "sink")]);
}

#[test]
fn pipeline_widened_passes() {
    assert_violations(&parse(&pipeline(true)), vec![]);
}

// --- three-party ring (folklore) ----------------------------------------------

fn ring(widened: bool) -> String {
    let (f1_to, f2_to) = if widened { ("(b c)", "(c a)") } else { ("b", "c") };
    format!(
        "(define ring (cbcl) @corpus
           (:roles (a b c))
           (extend fwd1 (token) :from a :to {f1_to}
             (tell @b :token token :domain ring))
           (extend fwd2 (token) :from b :to {f2_to}
             (tell @c :token token :domain ring))
           (extend fwd3 (token) :from c :to a
             (tell @a :token token :domain ring))
           (protocol (then begin fwd1 fwd2 fwd3)))"
    )
}

#[test]
fn ring_fails_at_each_hop() {
    assert_violations(
        &parse(&ring(false)),
        vec![ncl("fwd2", "fwd1", "c"), ncl("fwd3", "fwd2", "a")],
    );
}

#[test]
fn ring_widened_passes() {
    assert_violations(&parse(&ring(true)), vec![]);
}

// --- two-phase commit (Gray), 3 explicit participants -------------------------

fn two_pc(widened: bool) -> String {
    let vote_to = if widened { "(coordinator p1 p2 p3)" } else { "coordinator" };
    format!(
        "(define twopc (cbcl) @corpus
           (:roles (coordinator p1 p2 p3))
           (extend prepare (txn) :from coordinator :to (p1 p2 p3)
             (tell @p1 :txn txn :domain twopc))
           (extend vote1 (v) :from p1 :to {vote_to}
             (tell @coordinator :v v :domain twopc))
           (extend vote2 (v) :from p2 :to {vote_to}
             (tell @coordinator :v v :domain twopc))
           (extend vote3 (v) :from p3 :to {vote_to}
             (tell @coordinator :v v :domain twopc))
           (extend decision (outcome) :from coordinator :to (p1 p2 p3)
             (tell @p1 :outcome outcome :domain twopc))
           (protocol (then begin prepare)
                     (then prepare vote1)
                     (then prepare vote2)
                     (then prepare vote3)
                     (then (all vote1 vote2 vote3) decision)))"
    )
}

#[test]
fn two_pc_fails_per_participant_at_decision() {
    // Each participant is an endpoint of the decision, which names every
    // vote; no participant is an endpoint of another's vote. The
    // singleton-role image of the auction's per-occupant failure.
    assert_violations(
        &parse(&two_pc(false)),
        vec![
            ncl("decision", "vote1", "p2"),
            ncl("decision", "vote1", "p3"),
            ncl("decision", "vote2", "p1"),
            ncl("decision", "vote2", "p3"),
            ncl("decision", "vote3", "p1"),
            ncl("decision", "vote3", "p2"),
        ],
    );
}

#[test]
fn two_pc_widened_votes_pass() {
    assert_violations(&parse(&two_pc(true)), vec![]);
}

// --- TEST-709: derived envelope routing (SPEC-015 REQ-709, ADR-704) ----------
//
// Under `(:causal-locality derive)` every R6(vi)-failing corpus dialect
// installs, and its derived routes equal the hand-widened repair pinned
// above, read as *envelope* recipients — transitive closure included
// (warehouse ⇒ track-shipment too). Payload `:to` sets are byte-identical
// before and after; under the default `reject` the TEST-640 verdicts above
// are unchanged (those tests parse the same sources and stay pinned).
// The indexed-role (auction) half of TEST-709 — routes appearing only in
// the thread-open derivation, never the install table — lives with the
// TEST-608 auction fixtures in `cbcl-core/src/r6.rs`
// (`announcing_auction_routes_appear_only_at_thread_open`), because the
// auction's single-member `(all reveal)` fan-in is a struct-level encoding
// the surface grammar's two-member group rule cannot spell.

use cbcl_core::canonical::canonical_encode;
use cbcl_core::dialect::{Dialect, DialectRegistry};
use cbcl_core::projection::project;
use cbcl_core::r6::derive_envelope_routes;
use cbcl_core::role::{CausalLocality, Endpoint, EnvelopeRoutes};
use std::collections::BTreeMap;

/// The corpus source with `(:causal-locality derive)` declared.
fn deriving(src: &str) -> String {
    src.replacen("(:roles", "(:causal-locality derive)\n           (:roles", 1)
}

/// Parse and install under `derive`, returning the installed dialect.
fn install_deriving(src: &str) -> Dialect {
    let d = parse(&deriving(src));
    let name = d.name.clone();
    let mut reg = DialectRegistry::new();
    reg.install(d)
        .expect("R6(vi)-failing corpus dialect must install under derive");
    reg.find_by_name(&name).unwrap().clone()
}

fn table(pairs: &[(&str, &[&str])]) -> EnvelopeRoutes {
    EnvelopeRoutes(
        pairs
            .iter()
            .map(|(p, rs)| {
                (
                    (*p).to_string(),
                    rs.iter().map(|r| (*r).to_string()).collect(),
                )
            })
            .collect(),
    )
}

fn recorded_routes(d: &Dialect) -> &EnvelopeRoutes {
    match &d.causal_locality {
        CausalLocality::Derive(t) => t,
        CausalLocality::Reject => panic!("expected a deriving dialect"),
    }
}

/// Every R6(vi)-failing corpus dialect of this file with its expected
/// derived table — the hand-widened repairs above, as envelope recipients.
fn failing_corpus() -> Vec<(String, EnvelopeRoutes)> {
    vec![
        (
            logistics(true),
            // Transitive: warehouse ⇒ track-shipment too, not just the
            // deciding branch (accept); the untaken `reject` branch is on
            // no violation and gets no route.
            table(&[("accept", &["warehouse"]), ("track-shipment", &["warehouse"])]),
        ),
        (
            two_buyer(false),
            table(&[("title", &["buyer2"]), ("share", &["seller"])]),
        ),
        (pipeline(false), table(&[("produce", &["sink"])])),
        (
            ring(false),
            table(&[("fwd1", &["c"]), ("fwd2", &["a"])]),
        ),
        (
            two_pc(false),
            table(&[
                ("vote1", &["p2", "p3"]),
                ("vote2", &["p1", "p3"]),
                ("vote3", &["p1", "p2"]),
            ]),
        ),
    ]
}

#[test]
fn test_709_failing_corpus_installs_under_derive_with_the_widened_routes() {
    for (src, expected) in failing_corpus() {
        let d = install_deriving(&src);
        assert_eq!(
            recorded_routes(&d),
            &expected,
            "derived routes for '{}' must equal the hand-widened repair",
            d.name
        );
    }
}

#[test]
fn test_709_derivation_is_idempotent_and_identical_across_installs() {
    for (src, _) in failing_corpus() {
        let d1 = install_deriving(&src);
        let d2 = install_deriving(&src);
        assert_eq!(
            recorded_routes(&d1),
            recorded_routes(&d2),
            "independent installs of '{}' must derive identical routes",
            d1.name
        );
        // Idempotent: re-deriving from the installed dialect (table
        // recorded) reproduces the recorded table exactly.
        assert_eq!(&derive_envelope_routes(&d1), recorded_routes(&d1));
    }
}

#[test]
fn test_709_payload_to_sets_are_byte_identical() {
    for (src, _) in failing_corpus() {
        let parsed = parse(&deriving(&src));
        let annotation_bytes = |d: &Dialect| -> BTreeMap<String, Vec<u8>> {
            d.performatives
                .iter()
                .map(|p| {
                    let ann = p.role.as_ref().expect("corpus performatives are annotated");
                    let mut to: Vec<_> = ann.to.iter().cloned().collect();
                    to.sort();
                    let sexpr: cbcl_core::sexpr::SExpr =
                        format!("({} ({}))", ann.from, to.join(" ")).parse().unwrap();
                    (p.name.clone(), canonical_encode(&sexpr))
                })
                .collect()
        };
        let before = annotation_bytes(&parsed);
        let installed = install_deriving(&src);
        assert_eq!(
            annotation_bytes(&installed),
            before,
            "payload :from/:to bytes of '{}' must be untouched by derivation",
            installed.name
        );
    }
}

#[test]
fn test_709_default_reject_keeps_v1_verdicts_and_rejects_install() {
    use cbcl_core::dialect::DialectInstallError;
    // The pinned TEST-640 verdict tests above already re-check the exact
    // violation sets under the default; here: the sources parse to
    // `Reject` and still fail install with the R6 rejection, v1 semantics.
    for (src, _) in failing_corpus() {
        let d = parse(&src);
        assert_eq!(d.causal_locality, CausalLocality::Reject);
        let mut reg = DialectRegistry::new();
        let err = reg.install(d).unwrap_err();
        assert!(
            matches!(err, DialectInstallError::R6Violation { .. }),
            "expected the v1 R6 rejection, got: {err}"
        );
    }
}

#[test]
fn test_709_projection_emits_expect_envelope_for_every_route() {
    for (src, expected) in failing_corpus() {
        let d = install_deriving(&src);
        for (perf, roles) in &expected.0 {
            for role in roles {
                let local = project(
                    &d,
                    &Endpoint {
                        role: role.clone(),
                        occupant: None,
                    },
                    None,
                );
                assert!(
                    local.expect_envelopes.contains(perf),
                    "'{}': projection for '{role}' must expect the envelope of '{perf}'",
                    d.name
                );
                // ExpectEnvelope is a Recv-analogue, not a Recv: the route
                // role stays a payload bystander of the performative.
                assert!(
                    !local.steps.contains_key(perf),
                    "'{}': '{role}' must hold no Send/Recv step for '{perf}'",
                    d.name
                );
            }
        }
    }
}
