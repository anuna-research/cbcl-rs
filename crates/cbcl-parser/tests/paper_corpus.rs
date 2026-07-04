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
