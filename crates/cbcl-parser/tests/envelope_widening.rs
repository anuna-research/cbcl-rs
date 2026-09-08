//! SPEC-015 TEST-702: corpus re-run under envelope widening.
//!
//! Re-encodes corpus repairs of SPEC-014 TEST-640 (`paper_corpus.rs`) with
//! *envelope* deliveries in place of payload widenings: the widened
//! recipient receives the predecessor as a redacted envelope over the
//! CON-700 wire form, not as a full message. Pinned here:
//!
//! - the R6 verdict of every widened dialect is unchanged (still clean);
//! - the widened recipient reaches the *same R5 safety verdict* it would
//!   with the full predecessor (REQ-702) — Unknown before the envelope
//!   arrives, then resolved identically to the full-message holder;
//! - no widened recipient sees a single payload field: the wire form of
//!   each envelope is checked for the payload strings (NFR-701), while the
//!   metadata that IS disclosed (performative name) stays visible, as
//!   NFR-702 states — metadata-only, never "none".
//!
//! Repairs re-encoded: pipeline (straight-line), two-buyer (choice
//! disclosure — the share amount), and two-phase commit (fan-in over
//! envelope votes, exercising the `(all …)` type check of REQ-702; the
//! completion-level boundary of REQ-703 is pinned in
//! `cbcl-core/src/projection.rs`).

use cbcl_core::attest::sign_attestation_v2;
use cbcl_core::envelope::{parse_envelope, redact, RedactedEnvelope};
use cbcl_core::equivocation::{attestation_header_for, message_content_hash};
use cbcl_core::message::Message;
use cbcl_core::protocol::{verify_causal, VerificationResult};
use cbcl_core::r4::Signer;
use cbcl_core::r6::r6_violations;
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use cbcl_parser::parse_dialect;

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

fn parse(src: &str) -> cbcl_core::dialect::Dialect {
    let sexpr: SExpr = src
        .parse()
        .expect("corpus dialect must parse as an S-expression");
    parse_dialect(&sexpr).expect("corpus dialect must parse as a dialect")
}

fn msg(src: &str) -> Message {
    // The cryptographic APIs below operate on the recognized simple body.
    Message::try_from(&src.parse::<SExpr>().unwrap())
        .unwrap()
        .innermost_simple()
        .unwrap()
        .clone()
}

fn tid(s: &str) -> ThreadId {
    ThreadId(s.into())
}

/// Data-dependent test signer: sig = secret ‖ data, so any change to the
/// attestation preimage changes the signature. Distinct secrets model
/// distinct keys.
struct TestSigner {
    secret: &'static [u8],
}

impl Signer for TestSigner {
    fn sign(&self, data: &[u8]) -> Vec<u8> {
        let mut out = self.secret.to_vec();
        out.extend_from_slice(data);
        out
    }
    fn verify(&self, data: &[u8], sig: &[u8]) -> bool {
        self.sign(data) == sig
    }
}

/// Append a full message to a store under its real content hash.
fn deliver_full(store: &mut ThreadedMessageStore, thread: &str, m: &Message) -> String {
    let h = message_content_hash(m);
    assert!(store.append(ContentHash(h.clone()), tid(thread), m.clone()));
    h
}

/// Redact a signed message and deliver the envelope through its CON-700
/// wire form (serialise → transport → full recognition → store acceptance).
/// Returns (content hash, wire text) so callers can assert disclosure.
fn deliver_envelope(
    store: &mut ThreadedMessageStore,
    m: &Message,
    signer: &TestSigner,
) -> (String, String) {
    let header = attestation_header_for(m).expect("corpus trace messages carry the full header");
    let signature = sign_attestation_v2(signer, &header).unwrap();
    let envelope = redact(m, signature).expect("redaction is total on well-headed messages");

    // Over the wire: CON-700 serialise ∘ parse is identity (full
    // recognition before any semantic action).
    let wire = envelope.to_sexpr().to_string();
    let received: RedactedEnvelope =
        parse_envelope(&wire.parse::<SExpr>().unwrap(), 8).expect("wire envelope re-parses");
    assert_eq!(received, envelope);

    // Store acceptance verifies the attestation and places the envelope in
    // its authenticated thread (REQ-702).
    assert_eq!(store.append_envelope(received, signer), Ok(true));
    (envelope.header.content_hash.clone(), wire)
}

// ---------------------------------------------------------------------------
// Pipeline (folklore): the straight-line repair, paid in evidence
// ---------------------------------------------------------------------------

#[test]
fn pipeline_widened_with_envelopes_same_verdicts_zero_disclosure() {
    // The widened dialect of the corpus table — R6 verdict unchanged.
    let d = parse(
        "(define pipeline (cbcl) @corpus
           (:roles (source kernel sink))
           (extend produce (chunk) :from source :to (kernel sink)
             (tell @kernel :chunk chunk :domain pipeline))
           (extend forward (chunk) :from kernel :to sink
             (tell @sink :chunk chunk :domain pipeline))
           (protocol (then begin produce forward)))",
    );
    assert_eq!(r6_violations(&d), vec![]);
    let cp = d.causal_protocol.as_ref().unwrap();

    let src_signer = TestSigner { secret: b"source" };
    let produce = msg(
        "(lang pipeline (produce (@ker @snk) \"chunk-payload-7\" :thread \"run-1\" :sender @src :caused-by begin))",
    );

    // kernel — the payload recipient — holds the full message.
    let mut kernel = ThreadedMessageStore::new();
    let h_prod = deliver_full(&mut kernel, "run-1", &produce);

    // sink — the widened recipient — holds only the redacted envelope.
    let mut sink = ThreadedMessageStore::new();
    let forward = msg(&format!(
        "(lang pipeline (forward @snk \"chunk-payload-7\" :thread \"run-1\" :sender @ker :caused-by {h_prod}))"
    ));
    let verdict = |store: &ThreadedMessageStore| {
        verify_causal(
            "forward",
            forward.innermost_simple().unwrap().caused_by(),
            store,
            cp,
            &tid("run-1"),
        )
    };

    // Before the evidence arrives: not-yet, never a violation.
    assert_eq!(verdict(&sink), VerificationResult::Unknown);

    let (h_env, wire) = deliver_envelope(&mut sink, &produce, &src_signer);
    assert_eq!(
        h_env, h_prod,
        "the envelope names the redacted message (TEST-700)"
    );

    // Same R5 safety verdict as the full-message holder (REQ-702).
    assert_eq!(verdict(&sink), VerificationResult::Valid);
    assert_eq!(verdict(&sink), verdict(&kernel));

    // Zero payload fields visible to the widened party (NFR-701) — and
    // the disclosure that remains is metadata, stated as such (NFR-702).
    assert!(
        !wire.contains("chunk-payload-7"),
        "payload leaked to sink: {wire}"
    );
    assert!(
        wire.contains("produce"),
        "the performative type is (deliberate) metadata"
    );
}

// ---------------------------------------------------------------------------
// Two-buyer (Honda–Yoshida–Carbone): the disclosure repair, without the
// disclosure — buyer2 never sees the title, the seller never sees the share
// ---------------------------------------------------------------------------

#[test]
fn two_buyer_widened_with_envelopes_same_verdicts_zero_disclosure() {
    let d = parse(
        "(define twobuyer (cbcl) @corpus
           (:roles (buyer1 buyer2 seller))
           (extend title (name) :from buyer1 :to (seller buyer2)
             (tell @seller :name name :domain twobuyer))
           (extend quote (price) :from seller :to (buyer1 buyer2)
             (tell @buyer1 :price price :domain twobuyer))
           (extend share (amount) :from buyer1 :to (buyer2 seller)
             (tell @buyer2 :amount amount :domain twobuyer))
           (extend buy (address) :from buyer2 :to seller
             (tell @seller :address address :domain twobuyer))
           (extend quit (reason) :from buyer2 :to seller
             (tell @seller :reason reason :domain twobuyer))
           (extend date (delivery) :from seller :to buyer2
             (tell @buyer2 :delivery delivery :domain twobuyer))
           (protocol (then begin title quote share (any buy quit))
                     (then buy date)))",
    );
    assert_eq!(r6_violations(&d), vec![]);
    let cp = d.causal_protocol.as_ref().unwrap();
    let t = "order-66";

    let b1_signer = TestSigner { secret: b"buyer1" };

    // The trace, with the two payloads the corpus table flags as the
    // disclosure objection: the book title and buyer1's share amount.
    let title = msg(&format!(
        "(lang twobuyer (title (@b2 @slr) \"war-and-peace\" :thread \"{t}\" :sender @b1 :caused-by begin))"
    ));
    let h_title = message_content_hash(&title);
    let quote = msg(&format!(
        "(lang twobuyer (quote (@b1 @b2) 3999 :thread \"{t}\" :sender @slr :caused-by {h_title}))"
    ));
    let h_quote = message_content_hash(&quote);
    let share = msg(&format!(
        "(lang twobuyer (share (@b2 @slr) \"amount-1250\" :thread \"{t}\" :sender @b1 :caused-by {h_quote}))"
    ));
    let h_share = message_content_hash(&share);
    let buy = msg(&format!(
        "(lang twobuyer (buy @slr \"ship-to-coruscant\" :thread \"{t}\" :sender @b2 :caused-by {h_share}))"
    ));

    // buyer2's local store: the quote arrives in full (buyer2 is a payload
    // recipient), the *title* only as an envelope.
    let mut buyer2 = ThreadedMessageStore::new();
    let quote_verdict = |store: &ThreadedMessageStore| {
        verify_causal(
            "quote",
            quote.innermost_simple().unwrap().caused_by(),
            store,
            cp,
            &tid(t),
        )
    };
    assert_eq!(quote_verdict(&buyer2), VerificationResult::Unknown);
    let (_, title_wire) = deliver_envelope(&mut buyer2, &title, &b1_signer);
    assert_eq!(quote_verdict(&buyer2), VerificationResult::Valid);
    assert!(
        !title_wire.contains("war-and-peace"),
        "buyer2 must not see the title payload: {title_wire}"
    );

    // The seller's local store: buyer2's decision cites the share, which
    // the seller receives only as an envelope — the amount stays private.
    let mut seller = ThreadedMessageStore::new();
    let buy_verdict = |store: &ThreadedMessageStore| {
        verify_causal(
            "buy",
            buy.innermost_simple().unwrap().caused_by(),
            store,
            cp,
            &tid(t),
        )
    };
    assert_eq!(buy_verdict(&seller), VerificationResult::Unknown);
    let (_, share_wire) = deliver_envelope(&mut seller, &share, &b1_signer);
    assert_eq!(buy_verdict(&seller), VerificationResult::Valid);
    assert!(
        !share_wire.contains("amount-1250"),
        "the seller must not see the share amount: {share_wire}"
    );

    // Same verdicts as a fully-widened (payload) delivery would give.
    let mut full = ThreadedMessageStore::new();
    deliver_full(&mut full, t, &title);
    deliver_full(&mut full, t, &quote);
    deliver_full(&mut full, t, &share);
    assert_eq!(quote_verdict(&buyer2), quote_verdict(&full));
    assert_eq!(buy_verdict(&seller), buy_verdict(&full));
}

// ---------------------------------------------------------------------------
// Two-phase commit (Gray): the O(n²) vote widening as O(n²) headers —
// a participant resolves the decision's fan-in from envelope votes
// ---------------------------------------------------------------------------

#[test]
fn two_pc_widened_with_envelope_votes_same_verdicts_zero_disclosure() {
    let d = parse(
        "(define twopc (cbcl) @corpus
           (:roles (coordinator p1 p2 p3))
           (extend prepare (txn) :from coordinator :to (p1 p2 p3)
             (tell @p1 :txn txn :domain twopc))
           (extend vote1 (v) :from p1 :to (coordinator p1 p2 p3)
             (tell @coordinator :v v :domain twopc))
           (extend vote2 (v) :from p2 :to (coordinator p1 p2 p3)
             (tell @coordinator :v v :domain twopc))
           (extend vote3 (v) :from p3 :to (coordinator p1 p2 p3)
             (tell @coordinator :v v :domain twopc))
           (extend decision (outcome) :from coordinator :to (p1 p2 p3)
             (tell @p1 :outcome outcome :domain twopc))
           (protocol (then begin prepare)
                     (then prepare vote1)
                     (then prepare vote2)
                     (then prepare vote3)
                     (then (all vote1 vote2 vote3) decision)))",
    );
    assert_eq!(r6_violations(&d), vec![]);
    let cp = d.causal_protocol.as_ref().unwrap();
    let t = "txn-9";

    let p2_signer = TestSigner { secret: b"p2" };
    let p3_signer = TestSigner { secret: b"p3" };

    let prepare = msg(&format!(
        "(lang twopc (prepare (@p1 @p2 @p3) \"txn-payload\" :thread \"{t}\" :sender @coord :caused-by begin))"
    ));
    let h_prep = message_content_hash(&prepare);
    let vote = |n: u32, sender: &str, secret_ballot: &str| {
        msg(&format!(
            "(lang twopc (vote{n} (@coord @p1 @p2 @p3) \"{secret_ballot}\" :thread \"{t}\" :sender {sender} :caused-by {h_prep}))"
        ))
    };
    let vote1 = vote(1, "@p1", "ballot-p1-yes");
    let vote2 = vote(2, "@p2", "ballot-p2-yes");
    let vote3 = vote(3, "@p3", "ballot-p3-no");
    let (h1, h2, h3) = (
        message_content_hash(&vote1),
        message_content_hash(&vote2),
        message_content_hash(&vote3),
    );
    let decision = msg(&format!(
        "(lang twopc (decision (@p1 @p2 @p3) \"abort\" :thread \"{t}\" :sender @coord :caused-by ({h1} {h2} {h3})))"
    ));

    // p1's local store: prepare (full, p1 is a recipient), its own vote1
    // (full), and the *other* votes as envelopes only.
    let mut p1 = ThreadedMessageStore::new();
    deliver_full(&mut p1, t, &prepare);
    deliver_full(&mut p1, t, &vote1);
    let verdict = |store: &ThreadedMessageStore| {
        verify_causal(
            "decision",
            decision.innermost_simple().unwrap().caused_by(),
            store,
            cp,
            &tid(t),
        )
    };
    // Two members missing entirely: the fan-in is unresolved.
    assert_eq!(verdict(&p1), VerificationResult::Unknown);

    let (_, w2) = deliver_envelope(&mut p1, &vote2, &p2_signer);
    assert_eq!(
        verdict(&p1),
        VerificationResult::Unknown,
        "one member still missing"
    );
    let (_, w3) = deliver_envelope(&mut p1, &vote3, &p3_signer);

    // All members evidenced: the `(all …)` type check resolves (REQ-702)…
    assert_eq!(verdict(&p1), VerificationResult::Valid);

    // …with zero ballot disclosure to p1 (NFR-701): the votes' payloads
    // never crossed the wire, only their headers did.
    for (wire, ballot) in [(&w2, "ballot-p2-yes"), (&w3, "ballot-p3-no")] {
        assert!(!wire.contains(ballot), "ballot leaked to p1: {wire}");
    }

    // The coordinator (the fan-in's payload recipient) holds full votes
    // and reaches the identical verdict: evidence widening changed the
    // disclosure column, not the verdict column.
    let mut coord = ThreadedMessageStore::new();
    deliver_full(&mut coord, t, &prepare);
    deliver_full(&mut coord, t, &vote1);
    deliver_full(&mut coord, t, &vote2);
    deliver_full(&mut coord, t, &vote3);
    assert_eq!(verdict(&coord), verdict(&p1));
}
