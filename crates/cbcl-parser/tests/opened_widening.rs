//! SPEC-017 TEST-816 (Stage 3): corpus re-run under *opened-envelope*
//! widening — the native-field-openings successor to
//! `envelope_widening.rs`'s SPEC-015 redacted-envelope re-run.
//!
//! Re-encodes the same corpus repairs (pipeline, two-buyer, two-phase
//! commit) with widened deliveries as **opened envelopes**: instead of a
//! reconstructed header re-bound by a v2 attestation, the widened recipient
//! receives the predecessor as a set of field-openings (leaves 0–4)
//! self-authenticating against the signed typed root (REQ-813). Pinned here:
//!
//! - the R6 verdict of every widened dialect is unchanged (still clean);
//! - the widened recipient reaches the *same R5 safety verdict* it would
//!   with the full predecessor — Unknown before the opened envelope arrives,
//!   then resolved identically to the full-message holder (REQ-813/REQ-702);
//! - no widened recipient sees a single payload field: the payload leaf is
//!   never opened and no disclosed opening carries the payload bytes
//!   (NFR-701), while the metadata that IS disclosed (performative type)
//!   stays visible (NFR-702);
//! - the completion boundary (REQ-703) is untouched: opened envelopes seal
//!   leaf 5, so they satisfy the R5 safety fan-in type check but never the
//!   role layer's occupant fan-in — pinned in `cbcl-core/src/projection.rs`.

use cbcl_core::envelope::{build_opened, OpenedEnvelope, HEADER_FIELDS};
use cbcl_core::equivocation::message_content_hash;
use cbcl_core::keyid::SignatureSuite;
use cbcl_core::message::Message;
use cbcl_core::protocol::{verify_causal, VerificationResult};
use cbcl_core::r4::Signer;
use cbcl_core::r6::r6_violations;
use cbcl_core::sexpr::SExpr;
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use cbcl_core::typed_addr::FieldId;
use cbcl_parser::parse_dialect;

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

fn parse(src: &str) -> cbcl_core::dialect::Dialect {
    let sexpr: SExpr = src.parse().expect("corpus dialect must parse as an S-expression");
    parse_dialect(&sexpr).expect("corpus dialect must parse as a dialect")
}

fn msg(src: &str) -> Message {
    Message::try_from(&src.parse::<SExpr>().unwrap()).unwrap()
}

fn tid(s: &str) -> ThreadId {
    ThreadId(s.into())
}

/// Data-dependent test signer: sig = secret ‖ data, so any change to the
/// signed bytes changes the signature. Distinct secrets model distinct keys.
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

/// Append a full message to a store under its typed content root.
fn deliver_full(store: &mut ThreadedMessageStore, thread: &str, m: &Message) -> String {
    let h = message_content_hash(m);
    assert!(store.append(ContentHash(h.clone()), tid(thread), m.clone()));
    h
}

/// Open a signed message over its header fields (payload sealed) and deliver
/// the opened envelope: store acceptance verifies the v3 root-signature and
/// every opening, and places it in its authenticated thread (REQ-813).
/// Returns (typed root, the opened envelope) so callers can assert sealing.
fn deliver_opened(
    store: &mut ThreadedMessageStore,
    m: &Message,
    signer: &TestSigner,
) -> (String, OpenedEnvelope) {
    let env = build_opened(m, &HEADER_FIELDS, &SignatureSuite::Ed25519, signer)
        .expect("opening is total on well-headed corpus messages");
    let root = env.root.clone();
    assert_eq!(store.append_opened(env.clone(), signer), Ok(true));
    (root, env)
}

/// NFR-701: no payload field crosses to a widened recipient — the payload
/// leaf is never opened, and no disclosed opening carries the payload bytes.
fn assert_payload_sealed(env: &OpenedEnvelope, payload: &str) {
    assert!(
        env.opening(FieldId::Payload).is_none(),
        "redacted delivery must not open the payload leaf"
    );
    for op in &env.openings {
        let disclosed = format!("{}", op.value);
        assert!(
            !disclosed.contains(payload),
            "payload '{payload}' leaked via opening {:?}: {disclosed}",
            op.field
        );
    }
}

// ---------------------------------------------------------------------------
// Pipeline (folklore): the straight-line repair, paid in openings
// ---------------------------------------------------------------------------

#[test]
fn pipeline_widened_with_openings_same_verdicts_zero_disclosure() {
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
        "(produce (@ker @snk) \"chunk-payload-7\" :thread \"run-1\" :sender @src :caused-by begin)",
    );

    // kernel — the payload recipient — holds the full message.
    let mut kernel = ThreadedMessageStore::new();
    let h_prod = deliver_full(&mut kernel, "run-1", &produce);

    // sink — the widened recipient — holds only the opened envelope.
    let mut sink = ThreadedMessageStore::new();
    let forward = msg(&format!(
        "(forward @snk \"chunk-payload-7\" :thread \"run-1\" :sender @ker :caused-by {h_prod})"
    ));
    let verdict = |store: &ThreadedMessageStore| {
        verify_causal("forward", forward.caused_by(), store, cp, &tid("run-1"))
    };

    assert_eq!(verdict(&sink), VerificationResult::Unknown);

    let (root, env) = deliver_opened(&mut sink, &produce, &src_signer);
    assert_eq!(root, h_prod, "the opened envelope names the redacted message's root");

    // Same R5 safety verdict as the full-message holder (REQ-813).
    assert_eq!(verdict(&sink), VerificationResult::Valid);
    assert_eq!(verdict(&sink), verdict(&kernel));

    // Zero payload fields visible to the widened party (NFR-701) — and the
    // performative type stays visible as deliberate metadata (NFR-702).
    assert_payload_sealed(&env, "chunk-payload-7");
    assert_eq!(env.performative(), Some("produce"));
}

// ---------------------------------------------------------------------------
// Two-buyer (Honda–Yoshida–Carbone): the disclosure repair, without the
// disclosure — buyer2 never sees the title, the seller never sees the share
// ---------------------------------------------------------------------------

#[test]
fn two_buyer_widened_with_openings_same_verdicts_zero_disclosure() {
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

    let title = msg(&format!(
        "(title (@b2 @slr) \"war-and-peace\" :thread \"{t}\" :sender @b1 :caused-by begin)"
    ));
    let h_title = message_content_hash(&title);
    let quote = msg(&format!(
        "(quote (@b1 @b2) 3999 :thread \"{t}\" :sender @slr :caused-by {h_title})"
    ));
    let h_quote = message_content_hash(&quote);
    let share = msg(&format!(
        "(share (@b2 @slr) \"amount-1250\" :thread \"{t}\" :sender @b1 :caused-by {h_quote})"
    ));
    let h_share = message_content_hash(&share);
    let buy = msg(&format!(
        "(buy @slr \"ship-to-coruscant\" :thread \"{t}\" :sender @b2 :caused-by {h_share})"
    ));

    // buyer2's local store: quote in full (buyer2 is a payload recipient),
    // the *title* only as an opened envelope.
    let mut buyer2 = ThreadedMessageStore::new();
    let quote_verdict =
        |store: &ThreadedMessageStore| verify_causal("quote", quote.caused_by(), store, cp, &tid(t));
    assert_eq!(quote_verdict(&buyer2), VerificationResult::Unknown);
    let (_, title_env) = deliver_opened(&mut buyer2, &title, &b1_signer);
    assert_eq!(quote_verdict(&buyer2), VerificationResult::Valid);
    assert_payload_sealed(&title_env, "war-and-peace");

    // The seller's store: buyer2's decision cites the share, which the
    // seller receives only as an opened envelope — the amount stays private.
    let mut seller = ThreadedMessageStore::new();
    let buy_verdict =
        |store: &ThreadedMessageStore| verify_causal("buy", buy.caused_by(), store, cp, &tid(t));
    assert_eq!(buy_verdict(&seller), VerificationResult::Unknown);
    let (_, share_env) = deliver_opened(&mut seller, &share, &b1_signer);
    assert_eq!(buy_verdict(&seller), VerificationResult::Valid);
    assert_payload_sealed(&share_env, "amount-1250");

    // Same verdicts as a fully-widened (payload) delivery would give.
    let mut full = ThreadedMessageStore::new();
    deliver_full(&mut full, t, &title);
    deliver_full(&mut full, t, &quote);
    deliver_full(&mut full, t, &share);
    assert_eq!(quote_verdict(&buyer2), quote_verdict(&full));
    assert_eq!(buy_verdict(&seller), buy_verdict(&full));
}

// ---------------------------------------------------------------------------
// Two-phase commit (Gray): the O(n²) vote widening as O(n²) openings —
// a participant resolves the decision's fan-in from opened votes
// ---------------------------------------------------------------------------

#[test]
fn two_pc_widened_with_opened_votes_same_verdicts_zero_disclosure() {
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
        "(prepare (@p1 @p2 @p3) \"txn-payload\" :thread \"{t}\" :sender @coord :caused-by begin)"
    ));
    let h_prep = message_content_hash(&prepare);
    let vote = |n: u32, sender: &str, secret_ballot: &str| {
        msg(&format!(
            "(vote{n} (@coord @p1 @p2 @p3) \"{secret_ballot}\" :thread \"{t}\" :sender {sender} :caused-by {h_prep})"
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
        "(decision (@p1 @p2 @p3) \"abort\" :thread \"{t}\" :sender @coord :caused-by ({h1} {h2} {h3}))"
    ));

    // p1's store: prepare (full), its own vote1 (full), the *other* votes
    // as opened envelopes only.
    let mut p1 = ThreadedMessageStore::new();
    deliver_full(&mut p1, t, &prepare);
    deliver_full(&mut p1, t, &vote1);
    let verdict = |store: &ThreadedMessageStore| {
        verify_causal("decision", decision.caused_by(), store, cp, &tid(t))
    };
    assert_eq!(verdict(&p1), VerificationResult::Unknown);

    let (_, e2) = deliver_opened(&mut p1, &vote2, &p2_signer);
    assert_eq!(verdict(&p1), VerificationResult::Unknown, "one member still missing");
    let (_, e3) = deliver_opened(&mut p1, &vote3, &p3_signer);

    // All members evidenced: the `(all …)` type check resolves (REQ-813)…
    assert_eq!(verdict(&p1), VerificationResult::Valid);

    // …with zero ballot disclosure to p1 (NFR-701).
    assert_payload_sealed(&e2, "ballot-p2-yes");
    assert_payload_sealed(&e3, "ballot-p3-no");

    // The coordinator (the fan-in's payload recipient) holds full votes and
    // reaches the identical verdict: widening changed the disclosure column,
    // not the verdict column.
    let mut coord = ThreadedMessageStore::new();
    deliver_full(&mut coord, t, &prepare);
    deliver_full(&mut coord, t, &vote1);
    deliver_full(&mut coord, t, &vote2);
    deliver_full(&mut coord, t, &vote3);
    assert_eq!(verdict(&coord), verdict(&p1));
}
