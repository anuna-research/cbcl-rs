//! SPEC-024 `mls-ds/v1` crypto-boundary proof vectors (native, real Ed25519).
//!
//! Case labels map to SPEC-024 TEST-012 / TEST-013 / TEST-018.

use super::*;
use crate::serializer::serialize;
use crate::sexpr::{Atom, SExpr};
use alloc::string::ToString;
use alloc::vec;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

const THREAD: &str = "0123456789abcdef0123456789abcdef";

fn kp(n: u8) -> Ed25519Keypair {
    Ed25519Keypair::from_seed(&[n; 32])
}
fn kw(k: &str) -> SExpr {
    SExpr::Atom(Atom::Keyword(k.to_string()))
}
fn qb64(sig: &[u8; 64]) -> SExpr {
    SExpr::Atom(Atom::Str(b64url_encode(sig)))
}
fn h64(byte: u8) -> String {
    let mut s = String::from("sha256:");
    push_hex(&mut s, &[byte; 32]);
    s
}

/// Holds the two principals and the representative dialect.
struct Env {
    client: Ed25519Keypair,
    ds: Ed25519Keypair,
    d: Dialect,
    dh: String,
}

impl Env {
    fn new() -> Self {
        let d = mls_ds_dialect();
        let dh = d.hash.clone().unwrap();
        Env {
            client: kp(1),
            ds: kp(2),
            d,
            dh,
        }
    }
    fn cid(&self) -> String {
        self.client.key_id()
    }
    fn did(&self) -> String {
        self.ds.key_id()
    }
    fn bindings(&self) -> SExpr {
        bindings_sexpr(&self.cid(), &self.did())
    }
    fn opener_msg(&self) -> SExpr {
        opener_message(&self.cid(), &self.did(), THREAD)
    }
    fn h0(&self) -> String {
        typed_root(&Message::try_from(&self.opener_msg()).unwrap())
    }
    /// A valid signed opener with the given dialect pin.
    fn opener(&self, pin: &str) -> SExpr {
        let om = self.opener_msg();
        let t = DomainTuple::Open {
            bindings: self.bindings(),
            dialect_hash: self.dh.clone(),
            opener_message: om.clone(),
        };
        let sig = t.sign(&self.client);
        let signed_opener = SExpr::List(vec![sym("signed"), sym(&self.cid()), qb64(&sig), om]);
        SExpr::List(vec![
            sym("with-roles"),
            self.bindings(),
            kw("dialect"),
            qstr(pin),
            signed_opener,
        ])
    }
    /// A signed request over `request`, using `read_context`, signed by
    /// `signer` and labelled with `signer_id` in the wrapper.
    fn signed_request(
        &self,
        request: &SExpr,
        rc: &ReadContext,
        signer: &Ed25519Keypair,
        signer_id: &str,
    ) -> SExpr {
        let t = DomainTuple::Request {
            bindings: self.bindings(),
            dialect_hash: self.dh.clone(),
            h0: self.h0(),
            request: request.clone(),
            read_context: rc.clone(),
        };
        let sig = t.sign(signer);
        SExpr::List(vec![sym("signed"), sym(signer_id), qb64(&sig), request.clone()])
    }
    fn env_ctx(&self, room: &str, frame: i64) -> EnvelopeContext {
        EnvelopeContext {
            session_id: String::from("sess-abc"),
            frame_id: frame,
            outer_room: String::from(room),
        }
    }
}

fn opener_message(client_id: &str, ds_id: &str, thread: &str) -> SExpr {
    SExpr::List(vec![
        sym("mls-ds-open-v1"),
        sym(ds_id),
        SExpr::List(vec![sym("open-v1"), sym(client_id), sym(ds_id)]),
        kw("thread"),
        qstr(thread),
        kw("caused-by"),
        sym("begin"),
    ])
}

#[allow(clippy::too_many_arguments)]
fn request_desc(
    kind: &str,
    ds_id: &str,
    body: SExpr,
    issued: i64,
    expires: i64,
    thread: &str,
    h0: &str,
) -> SExpr {
    SExpr::List(vec![
        sym(kind),
        sym(ds_id),
        body,
        kw("issued-at"),
        num(issued),
        kw("expires-at"),
        num(expires),
        kw("thread"),
        qstr(thread),
        kw("caused-by"),
        qhash(h0),
    ])
}

fn request_bundle_sexpr(opener: SExpr, signed_request: SExpr, sidecars: SExpr) -> SExpr {
    SExpr::List(vec![
        sym(REQUEST_BUNDLE_TAG),
        opener,
        signed_request,
        sidecars,
    ])
}

/// Recognize a payload string and require a request bundle.
fn recognize_request(payload: &str) -> RequestBundleAst {
    match recognize_dispatch_verified_outer(payload.as_bytes()) {
        OuterClass::Request(a) => a,
        other => panic!("expected request bundle, got {other:?}"),
    }
}

/// Build a full, valid `commit-submit` request bundle (mutation path with a
/// nested SOURCE-SIG and one ciphertext sidecar). Returns (payload, room, issued).
fn valid_commit_submit(env: &Env) -> (String, String, i64) {
    let room = String::from("room-1");
    let issued = 1_000_000;
    let expires = issued + 86_400_000; // mutation duration
    let ct = b"ciphertext-opaque-bytes";
    let ct_digest = sha256_hex(ct);
    let ct_ref = SExpr::List(vec![
        sym("blob-ref-v1"),
        sym("ciphertext"),
        qhash(&ct_digest),
        num(ct.len() as i64),
    ]);
    let source = SExpr::List(vec![
        sym("commit-v1"),
        qstr(&room),
        num(0),
        qhash(&h64(0xAA)),
        ct_ref,
    ]);
    let src_sig = DomainTuple::Source {
        source: source.clone(),
    }
    .sign(&env.client);
    let signed_source = SExpr::List(vec![
        sym("source-signed"),
        sym(&env.cid()),
        qb64(&src_sig),
        source,
    ]);
    let body = SExpr::List(vec![sym("submit-v1"), signed_source]);
    let request = request_desc(
        "commit-submit",
        &env.did(),
        body,
        issued,
        expires,
        THREAD,
        &env.h0(),
    );
    let signed_request = env.signed_request(&request, &ReadContext::None, &env.client, &env.cid());
    let sidecar = SExpr::List(vec![
        sym("blob-sidecar-v1"),
        sym("ciphertext"),
        qhash(&ct_digest),
        num(ct.len() as i64),
        qstr(&b64url_encode(ct)),
    ]);
    let bundle = request_bundle_sexpr(
        env.opener(&env.dh),
        signed_request,
        SExpr::List(vec![sidecar]),
    );
    (serialize(&bundle), room, issued)
}

/// Build a valid DS `record-admitted` response for a persisted VTC.
fn admitted_response(env: &Env, vtc: &VerifiedThreadContext, room: &str) -> String {
    let body = SExpr::List(vec![
        sym("admitted-v1"),
        qstr(room),
        num(1),
        qhash(&h64(0xBB)),
        qhash(&h64(0xCC)),
    ]);
    let msg = SExpr::List(vec![
        sym("record-admitted"),
        sym(&vtc.client_key_id),
        body,
        kw("thread"),
        qstr(&vtc.thread_id),
        kw("caused-by"),
        qhash(&vtc.request_message_hash),
    ]);
    let sig = DomainTuple::Response {
        bindings: vtc.bindings.clone(),
        dialect_hash: env.dh.clone(),
        request_content_hash: vtc.request_message_hash.clone(),
        response_message: msg.clone(),
        read_context: vtc.request_frame_context.clone(),
    }
    .sign(&env.ds);
    let signed = SExpr::List(vec![sym("signed"), sym(&env.did()), qb64(&sig), msg]);
    serialize(&SExpr::List(vec![
        sym(RESPONSE_BUNDLE_TAG),
        signed,
        SExpr::List(vec![]),
    ]))
}

fn recognize_response(payload: &str) -> ResponseBundleAst {
    match recognize_dispatch_verified_outer(payload.as_bytes()) {
        OuterClass::Response(a) => a,
        other => panic!("expected response bundle, got {other:?}"),
    }
}

// ===========================================================================
// TEST-018 T18-13 — REQ-141 pinned strict Ed25519 profile
// ===========================================================================

/// The little-endian order L (re-derived locally so the vector does not lean on
/// a module-private constant).
const L_LE: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

fn add_l(s: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let sum = s[i] as u16 + L_LE[i] as u16 + carry;
        out[i] = (sum & 0xff) as u8;
        carry = sum >> 8;
    }
    assert_eq!(carry, 0, "s + L must fit in 256 bits");
    out
}

#[test]
fn t18_13_canonical_signature_accepted() {
    let a = kp(9);
    let msg = b"mls-ds/v1 canonical vector";
    let sig = a.sign(msg);
    assert!(verify_strict_ed25519(&a.public_bytes(), msg, &sig));
}

#[test]
fn t18_13_s_plus_l_malleation_rejected() {
    // The headline REQ-141 defence: S += L verifies under a lax verifier but is
    // rejected by the canonical-S check, so no verifier-differential fork.
    let a = kp(9);
    let msg = b"mls-ds/v1 canonical vector";
    let sig = a.sign(msg);
    let mut s = [0u8; 32];
    s.copy_from_slice(&sig[32..64]);
    assert!(scalar_is_canonical(&s), "the honest S is canonical");
    let s_prime = add_l(&s);
    assert!(!scalar_is_canonical(&s_prime), "S + L is non-canonical");
    // The concrete verifier-differential: S + L still passes the *lax*
    // top-3-bits check (`s[31] & 0xE0 == 0`) that a non-strict verifier uses,
    // so a lax verifier would ACCEPT this malleation while the strict profile
    // rejects it — exactly the fork the threat model names.
    assert_eq!(
        s_prime[31] & 0xE0,
        0,
        "S + L passes the lax top-3-bits check (would fork a non-strict verifier)"
    );
    let mut malleated = sig;
    malleated[32..64].copy_from_slice(&s_prime);
    assert!(
        !verify_strict_ed25519(&a.public_bytes(), msg, &malleated),
        "S += L must be rejected"
    );
}

#[test]
fn t18_13_low_order_r_rejected() {
    // R replaced by the identity-point encoding (order 1, small order).
    let a = kp(9);
    let msg = b"mls-ds/v1 canonical vector";
    let sig = a.sign(msg);
    let mut bad = sig;
    let mut identity = [0u8; 32];
    identity[0] = 1; // canonical encoding of the identity point
    bad[0..32].copy_from_slice(&identity);
    assert!(!verify_strict_ed25519(&a.public_bytes(), msg, &bad));
}

#[test]
fn t18_13_noncanonical_point_encoding_rejected() {
    // R presented as a non-canonical / mismatched field encoding (top bits set,
    // y ≥ p): verify_strict recomputes the canonical R and the byte comparison
    // (or decode failure) rejects it.
    let a = kp(9);
    let msg = b"mls-ds/v1 canonical vector";
    let sig = a.sign(msg);
    let mut bad = sig;
    bad[0..32].copy_from_slice(&[0xff; 32]);
    assert!(!verify_strict_ed25519(&a.public_bytes(), msg, &bad));
}

#[test]
fn t18_13_small_order_public_key_rejected() {
    // A weak (small-order) public key A is rejected by verify_strict.
    let a = kp(9);
    let msg = b"mls-ds/v1 canonical vector";
    let sig = a.sign(msg);
    let mut identity = [0u8; 32];
    identity[0] = 1;
    assert!(!verify_strict_ed25519(&identity, msg, &sig));
}

#[test]
fn scalar_canonical_boundaries() {
    // 0 and L-1 are canonical; L and L+1 are not.
    let zero = [0u8; 32];
    assert!(scalar_is_canonical(&zero));
    let mut l_minus_1 = L_LE;
    l_minus_1[0] -= 1;
    assert!(scalar_is_canonical(&l_minus_1));
    assert!(!scalar_is_canonical(&L_LE)); // exactly L is non-canonical
    let mut l_plus_1 = L_LE;
    l_plus_1[0] += 1;
    assert!(!scalar_is_canonical(&l_plus_1));
}

// ===========================================================================
// CON-002 — canonical tuple sign/verify + domain separation
// ===========================================================================

#[test]
fn tuple_sign_verify_roundtrip_and_tamper() {
    let a = kp(3);
    let b = kp(4);
    let t = DomainTuple::Source {
        source: SExpr::List(vec![sym("commit-v1"), qstr("room"), num(7), qhash(&h64(1))]),
    };
    let sig = t.sign(&a);
    assert!(t.verify(&a.public_bytes(), &sig), "canonical verify");
    assert!(!t.verify(&b.public_bytes(), &sig), "wrong key rejected");
    // Tamper one field → different canonical bytes → rejected.
    let t2 = DomainTuple::Source {
        source: SExpr::List(vec![sym("commit-v1"), qstr("room"), num(8), qhash(&h64(1))]),
    };
    assert!(!t2.verify(&a.public_bytes(), &sig), "tampered field rejected");
}

#[test]
fn all_sixteen_domain_tuples_are_distinctly_domain_separated() {
    // One representative of each of the ~16 CON-002 tuples; their canonical
    // signable bytes must be pairwise distinct (leading domain tag separates).
    let core = SExpr::List(vec![sym("x")]);
    let tuples: alloc::vec::Vec<DomainTuple> = vec![
        DomainTuple::Open {
            bindings: core.clone(),
            dialect_hash: h64(1),
            opener_message: core.clone(),
        },
        DomainTuple::Request {
            bindings: core.clone(),
            dialect_hash: h64(1),
            h0: h64(2),
            request: core.clone(),
            read_context: ReadContext::None,
        },
        DomainTuple::Response {
            bindings: core.clone(),
            dialect_hash: h64(1),
            request_content_hash: h64(2),
            response_message: core.clone(),
            read_context: ReadContext::None,
        },
        DomainTuple::Source {
            source: core.clone(),
        },
        DomainTuple::AddAuth {
            room: "r".into(),
            source_author_key: "@k".into(),
            base_seq: 1,
            base_hash: h64(3),
            ciphertext_digest: h64(4),
            targets: vec!["@t".into()],
            welcome_digest: h64(5),
            genesis_anchor_hash: h64(6),
        },
        DomainTuple::Record {
            log_record: core.clone(),
        },
        DomainTuple::Claim {
            room_claim_core: core.clone(),
        },
        DomainTuple::ClaimDs {
            room_claim_core: core.clone(),
            creator_signature: "sig".into(),
        },
        DomainTuple::Genesis {
            room: "r".into(),
            genesis_blob_ref: core.clone(),
            creator_key: "@k".into(),
        },
        DomainTuple::PredecessorOffer {
            successor_offer_core: core.clone(),
        },
        DomainTuple::SuccessorConsent {
            successor_offer: core.clone(),
        },
        DomainTuple::SuccessorDs {
            successor_proposal: core.clone(),
        },
        DomainTuple::OfferHash {
            successor_offer: core.clone(),
        },
        DomainTuple::BridgeHash {
            successor_value: core.clone(),
        },
        DomainTuple::ClosurePackageHash {
            closure_package: core.clone(),
        },
    ];
    assert_eq!(tuples.len(), 15, "OPEN..closure-package hash tuples");
    let mut seen: BTreeSet<alloc::vec::Vec<u8>> = BTreeSet::new();
    for t in &tuples {
        assert!(
            seen.insert(t.signable_bytes()),
            "domain tag {} collides",
            t.domain_tag()
        );
    }
}

// ===========================================================================
// CON-002 — key-id / signature recognition predicates
// ===========================================================================

#[test]
fn key_id_and_signature_recognition_are_canonical() {
    let a = kp(5);
    let id = a.key_id();
    assert_eq!(recognize_key_id(&id), Some(a.public_bytes()));
    // Wrong length / missing sigil / non-canonical base64url are rejected.
    assert_eq!(recognize_key_id("alice"), None);
    assert_eq!(recognize_key_id("@short"), None);
    let sig = a.sign(b"x");
    let sig_str = b64url_encode(&sig);
    assert_eq!(recognize_signature(&sig_str), Some(sig));
    assert_eq!(recognize_signature("AAAA"), None);
}

// ===========================================================================
// TEST-012 — recognition and role boundary
// ===========================================================================

#[test]
fn t12_01_valid_request_and_reply_are_valid() {
    let env = Env::new();
    let (payload, room, issued) = valid_commit_submit(&env);
    let ast = recognize_request(&payload);
    let ctx = env.env_ctx(&room, 7);
    let verdict = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &ctx,
        issued, // trusted wall clock at issue time
        &ast,
    );
    let vtc = match verdict {
        RequestVerdict::Valid(TypedRequest::CommitSubmit { room: r, .. }, _, vtc) => {
            assert_eq!(r, room);
            vtc
        }
        other => panic!("expected Valid commit-submit, got {other:?}"),
    };
    assert_eq!(vtc.opener_message_hash, env.h0());
    assert_eq!(vtc.authority_room, room);

    // DS reply: record-admitted, projects only to the client.
    let resp_payload = admitted_response(&env, &vtc, &room);
    let rast = recognize_response(&resp_payload);
    let rverdict = verify_mls_ds_response(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.ds.public_bytes(), // outer signer on the response path is the DS
        &env.env_ctx(&room, 8),
        &vtc,
        &rast,
    );
    match rverdict {
        ResponseVerdict::Valid(TypedResponse::RecordAdmitted { seq, .. }, _) => assert_eq!(seq, 1),
        other => panic!("expected Valid record-admitted, got {other:?}"),
    }
}

#[test]
fn t12_02_malformed_is_violation_before_transition() {
    let env = Env::new();
    // (a) A duplicate :thread keyword in the request.
    let (payload, room, issued) = valid_commit_submit(&env);
    // Rebuild with a duplicated keyword by string surgery on a fresh build.
    let dup = payload.replacen(
        ":thread \"0123456789abcdef0123456789abcdef\"",
        ":thread \"0123456789abcdef0123456789abcdef\" :thread \"0123456789abcdef0123456789abcdef\"",
        1,
    );
    // The recognizer still parses; the role boundary rejects the duplicate.
    if let OuterClass::Request(ast) = recognize_dispatch_verified_outer(dup.as_bytes()) {
        let v = verify_mls_ds_request(
            &env.d,
            &env.dh,
            &env.ds.public_bytes(),
            &env.client.public_bytes(),
            &env.client.public_bytes(),
            &env.env_ctx(&room, 7),
            issued,
            &ast,
        );
        assert!(matches!(v, RequestVerdict::Violation(_)), "dup keyword");
    }

    // (b) A sidecar whose declared digest does not match its bytes.
    let bad = payload.replacen(&h64(0), &h64(1), 0); // no-op guard
    let _ = bad;
    let tampered = tamper_sidecar_digest(&payload);
    let ast = recognize_request(&tampered);
    let v = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(&room, 7),
        issued,
        &ast,
    );
    assert!(matches!(v, RequestVerdict::Violation(Code::Sidecar)));
}

/// Corrupt the sidecar's declared digest so it no longer matches its bytes.
fn tamper_sidecar_digest(payload: &str) -> String {
    // The sidecar digest and the source ciphertext-ref digest are equal; flip a
    // single hex nibble inside the *sidecar* occurrence only (the last one).
    let needle = "blob-sidecar-v1";
    let pos = payload.find(needle).unwrap();
    let (head, tail) = payload.split_at(pos);
    // In the tail, replace the first `sha256:` hash's leading hex char.
    let hpos = tail.find("sha256:").unwrap() + "sha256:".len();
    let mut tail = tail.to_string();
    let ch = tail.as_bytes()[hpos];
    let repl = if ch == b'0' { '1' } else { '0' };
    tail.replace_range(hpos..hpos + 1, &repl.to_string());
    format!("{head}{tail}")
}

#[test]
fn t12_03_wrong_dialect_and_member_signed_response_rejected() {
    let env = Env::new();
    // Wrong dialect pin in the opener.
    let wrong_pin = h64(0x77);
    let (payload, room, issued) = {
        // Rebuild a next-record request under a wrong opener pin.
        let issued = 2_000_000;
        let expires = issued + 60_000;
        let body = SExpr::List(vec![
            sym("next-v1"),
            qstr("room-1"),
            num(0),
            qhash(&h64(0)),
            num(0),
        ]);
        let req = request_desc("next-record", &env.did(), body, issued, expires, THREAD, &env.h0());
        let rc = ReadContext::Read {
            session_id: "sess-abc".into(),
            frame_id: 7,
        };
        let sreq = env.signed_request(&req, &rc, &env.client, &env.cid());
        let bundle =
            request_bundle_sexpr(env.opener(&wrong_pin), sreq, SExpr::List(vec![]));
        (serialize(&bundle), "room-1".to_string(), issued)
    };
    let ast = recognize_request(&payload);
    let v = verify_mls_ds_request(
        &env.d,
        &env.dh, // the *expected* (installed) hash, ≠ the opener's wrong pin
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(&room, 7),
        issued,
        &ast,
    );
    assert!(matches!(v, RequestVerdict::Violation(Code::WrongDialectPin)));

    // Member-signed response (signed by the client, not the DS).
    let (cpayload, croom, cissued) = valid_commit_submit(&env);
    let cast = recognize_request(&cpayload);
    let vtc = match verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(&croom, 7),
        cissued,
        &cast,
    ) {
        RequestVerdict::Valid(_, _, vtc) => vtc,
        other => panic!("setup: {other:?}"),
    };
    // Build a record-admitted response but sign it with the CLIENT key.
    let body = SExpr::List(vec![
        sym("admitted-v1"),
        qstr(&croom),
        num(1),
        qhash(&h64(0xBB)),
        qhash(&h64(0xCC)),
    ]);
    let msg = SExpr::List(vec![
        sym("record-admitted"),
        sym(&vtc.client_key_id),
        body,
        kw("thread"),
        qstr(&vtc.thread_id),
        kw("caused-by"),
        qhash(&vtc.request_message_hash),
    ]);
    let sig = DomainTuple::Response {
        bindings: vtc.bindings.clone(),
        dialect_hash: env.dh.clone(),
        request_content_hash: vtc.request_message_hash.clone(),
        response_message: msg.clone(),
        read_context: vtc.request_frame_context.clone(),
    }
    .sign(&env.client); // WRONG signer: a member
    let signed = SExpr::List(vec![sym("signed"), sym(&env.cid()), qb64(&sig), msg]);
    let payload = serialize(&SExpr::List(vec![
        sym(RESPONSE_BUNDLE_TAG),
        signed,
        SExpr::List(vec![]),
    ]));
    let rast = recognize_response(&payload);
    let rv = verify_mls_ds_response(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.ds.public_bytes(),
        &env.env_ctx(&croom, 8),
        &vtc,
        &rast,
    );
    assert!(matches!(rv, ResponseVerdict::Violation(Code::WrongSigner)));
}

#[test]
fn t12_04_wrong_root_signer_and_foreign_nested_source_rejected() {
    let env = Env::new();
    let mallory = kp(66);

    // (a) The request is signed by Mallory, not the admitted client.
    let issued = 3_000_000;
    let expires = issued + 60_000;
    let body = SExpr::List(vec![
        sym("next-v1"),
        qstr("room-1"),
        num(0),
        qhash(&h64(0)),
        num(0),
    ]);
    let req = request_desc("next-record", &env.did(), body, issued, expires, THREAD, &env.h0());
    let rc = ReadContext::Read {
        session_id: "sess-abc".into(),
        frame_id: 7,
    };
    // Signed by Mallory, labelled with Mallory's key-id.
    let sreq = env.signed_request(&req, &rc, &mallory, &mallory.key_id());
    let bundle = request_bundle_sexpr(env.opener(&env.dh), sreq, SExpr::List(vec![]));
    let ast = recognize_request(&serialize(&bundle));
    let v = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx("room-1", 7),
        issued,
        &ast,
    );
    assert!(matches!(v, RequestVerdict::Violation(Code::WrongSigner)));

    // (b) Alice's commit-submit whose nested source is signed by Bob.
    let room = "room-1";
    let ct = b"ct";
    let ct_ref = SExpr::List(vec![
        sym("blob-ref-v1"),
        sym("ciphertext"),
        qhash(&sha256_hex(ct)),
        num(ct.len() as i64),
    ]);
    let source = SExpr::List(vec![sym("commit-v1"), qstr(room), num(0), qhash(&h64(0xAA)), ct_ref]);
    let bob_sig = DomainTuple::Source {
        source: source.clone(),
    }
    .sign(&mallory); // Bob/Mallory signs the source
    let signed_source = SExpr::List(vec![
        sym("source-signed"),
        sym(&mallory.key_id()), // …and is named as the source signer
        qb64(&bob_sig),
        source,
    ]);
    let cbody = SExpr::List(vec![sym("submit-v1"), signed_source]);
    let cissued = 4_000_000;
    let creq = request_desc(
        "commit-submit",
        &env.did(),
        cbody,
        cissued,
        cissued + 86_400_000,
        THREAD,
        &env.h0(),
    );
    let csreq = env.signed_request(&creq, &ReadContext::None, &env.client, &env.cid());
    let sidecar = SExpr::List(vec![
        sym("blob-sidecar-v1"),
        sym("ciphertext"),
        qhash(&sha256_hex(ct)),
        num(ct.len() as i64),
        qstr(&b64url_encode(ct)),
    ]);
    let cbundle =
        request_bundle_sexpr(env.opener(&env.dh), csreq, SExpr::List(vec![sidecar]));
    let cast = recognize_request(&serialize(&cbundle));
    let cv = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(room, 7),
        cissued,
        &cast,
    );
    assert!(matches!(cv, RequestVerdict::Violation(Code::BadSourceSignature)));
}

/// Build a valid `commit-add-submit` request: nested SOURCE-SIG (client) + a
/// real 9-field ADD-AUTH signed by the immutable creator (here the client), two
/// sorted target keys, and the ciphertext+welcome sidecar set.
fn valid_commit_add_submit(env: &Env) -> (String, String, i64) {
    let room = String::from("room-1");
    let issued = 6_500_000;
    let expires = issued + 86_400_000;
    let base_hash = h64(0xAA);
    let genesis_anchor = h64(0x6E);

    let ct = b"add-ciphertext";
    let wel = b"welcome-blob";
    let ct_digest = sha256_hex(ct);
    let w_digest = sha256_hex(wel);
    let ct_ref = SExpr::List(vec![
        sym("blob-ref-v1"),
        sym("ciphertext"),
        qhash(&ct_digest),
        num(ct.len() as i64),
    ]);
    let w_ref = SExpr::List(vec![
        sym("blob-ref-v1"),
        sym("welcome"),
        qhash(&w_digest),
        num(wel.len() as i64),
    ]);

    // Two target keys, strictly increasing by decoded bytes.
    let (t0, t1) = {
        let a = kp(10);
        let b = kp(11);
        if a.public_bytes() < b.public_bytes() {
            (a.key_id(), b.key_id())
        } else {
            (b.key_id(), a.key_id())
        }
    };
    let targets = vec![t0.clone(), t1.clone()];
    let targets_sexpr = SExpr::List(vec![sym(&t0), sym(&t1)]);

    // ADD-AUTH (creator == client here) over the reconstructed 9-field tuple.
    let add_auth = DomainTuple::AddAuth {
        room: room.clone(),
        source_author_key: env.cid(),
        base_seq: 0,
        base_hash: base_hash.clone(),
        ciphertext_digest: ct_digest.clone(),
        targets: targets.clone(),
        welcome_digest: w_digest.clone(),
        genesis_anchor_hash: genesis_anchor.clone(),
    };
    let add_auth_sig = add_auth.sign(&env.client);
    let admission_proof = SExpr::List(vec![
        sym("add-authorized-v1"),
        sym(&env.cid()),
        qhash(&genesis_anchor),
        qb64(&add_auth_sig),
    ]);

    let source = SExpr::List(vec![
        sym("commit-add-v1"),
        qstr(&room),
        num(0),
        qhash(&base_hash),
        ct_ref,
        targets_sexpr,
        w_ref,
        admission_proof,
    ]);
    let src_sig = DomainTuple::Source {
        source: source.clone(),
    }
    .sign(&env.client);
    let signed_source = SExpr::List(vec![
        sym("source-signed"),
        sym(&env.cid()),
        qb64(&src_sig),
        source,
    ]);
    let body = SExpr::List(vec![sym("submit-add-v1"), signed_source]);
    let request = request_desc(
        "commit-add-submit",
        &env.did(),
        body,
        issued,
        expires,
        THREAD,
        &env.h0(),
    );
    let signed_request = env.signed_request(&request, &ReadContext::None, &env.client, &env.cid());
    // Sidecars sorted by (purpose, digest): ciphertext then welcome.
    let sc_ct = SExpr::List(vec![
        sym("blob-sidecar-v1"),
        sym("ciphertext"),
        qhash(&ct_digest),
        num(ct.len() as i64),
        qstr(&b64url_encode(ct)),
    ]);
    let sc_w = SExpr::List(vec![
        sym("blob-sidecar-v1"),
        sym("welcome"),
        qhash(&w_digest),
        num(wel.len() as i64),
        qstr(&b64url_encode(wel)),
    ]);
    let bundle = request_bundle_sexpr(
        env.opener(&env.dh),
        signed_request,
        SExpr::List(vec![sc_ct, sc_w]),
    );
    (serialize(&bundle), room, issued)
}

#[test]
fn commit_add_submit_with_real_add_auth_is_valid() {
    let env = Env::new();
    let (payload, room, issued) = valid_commit_add_submit(&env);
    let ast = recognize_request(&payload);
    let v = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(&room, 7),
        issued,
        &ast,
    );
    match v {
        RequestVerdict::Valid(TypedRequest::CommitAddSubmit { targets, .. }, _, _) => {
            assert_eq!(targets.len(), 2);
        }
        other => panic!("expected Valid commit-add-submit, got {other:?}"),
    }
}

#[test]
fn commit_add_submit_with_none_proof_is_add_unauthorized() {
    // A well-formed Add source whose admission proof is the bare `none`, with a
    // VALID SOURCE-SIG over that source, so verification reaches the proof and
    // maps `none` → add-unauthorized (CON-002 reducer mapping).
    let env = Env::new();
    let room = String::from("room-1");
    let issued = 6_600_000;
    let ct = b"add-ct";
    let wel = b"add-wel";
    let ct_ref = SExpr::List(vec![
        sym("blob-ref-v1"),
        sym("ciphertext"),
        qhash(&sha256_hex(ct)),
        num(ct.len() as i64),
    ]);
    let w_ref = SExpr::List(vec![
        sym("blob-ref-v1"),
        sym("welcome"),
        qhash(&sha256_hex(wel)),
        num(wel.len() as i64),
    ]);
    let (t0, t1) = {
        let a = kp(10);
        let b = kp(11);
        if a.public_bytes() < b.public_bytes() {
            (a.key_id(), b.key_id())
        } else {
            (b.key_id(), a.key_id())
        }
    };
    let source = SExpr::List(vec![
        sym("commit-add-v1"),
        qstr(&room),
        num(0),
        qhash(&h64(0xAA)),
        ct_ref,
        SExpr::List(vec![sym(&t0), sym(&t1)]),
        w_ref,
        sym("none"), // admission proof is `none`
    ]);
    let src_sig = DomainTuple::Source {
        source: source.clone(),
    }
    .sign(&env.client);
    let signed_source = SExpr::List(vec![
        sym("source-signed"),
        sym(&env.cid()),
        qb64(&src_sig),
        source,
    ]);
    let body = SExpr::List(vec![sym("submit-add-v1"), signed_source]);
    let request = request_desc(
        "commit-add-submit",
        &env.did(),
        body,
        issued,
        issued + 86_400_000,
        THREAD,
        &env.h0(),
    );
    let sreq = env.signed_request(&request, &ReadContext::None, &env.client, &env.cid());
    let sc_ct = SExpr::List(vec![
        sym("blob-sidecar-v1"),
        sym("ciphertext"),
        qhash(&sha256_hex(ct)),
        num(ct.len() as i64),
        qstr(&b64url_encode(ct)),
    ]);
    let sc_w = SExpr::List(vec![
        sym("blob-sidecar-v1"),
        sym("welcome"),
        qhash(&sha256_hex(wel)),
        num(wel.len() as i64),
        qstr(&b64url_encode(wel)),
    ]);
    let bundle =
        request_bundle_sexpr(env.opener(&env.dh), sreq, SExpr::List(vec![sc_ct, sc_w]));
    let ast = recognize_request(&serialize(&bundle));
    let v = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(&room, 7),
        issued,
        &ast,
    );
    assert!(
        matches!(v, RequestVerdict::Violation(Code::AddUnauthorized)),
        "none admission proof must map to add-unauthorized, got {v:?}"
    );
}

#[test]
fn t12_06_reserved_name_via_generic_route_rejected() {
    // A member publishes a reserved performative through the generic path.
    for name in ["record-admitted", "ds-rejected", "commit-submit", "room-closed"] {
        let payload = format!("({name} @x (foo))");
        assert!(matches!(
            recognize_dispatch_verified_outer(payload.as_bytes()),
            OuterClass::Violation(Code::ReservedMlsControl)
        ));
    }
    // A genuinely non-reserved publication is NonMls, not a violation.
    assert!(matches!(
        recognize_dispatch_verified_outer(b"(tell @x \"hi\")"),
        OuterClass::NonMls(_)
    ));
}

#[test]
fn t12_10_wrong_recipient_rejected() {
    let env = Env::new();
    let mallory = kp(66);
    // Request addressed to Mallory instead of the DS.
    let issued = 5_000_000;
    let body = SExpr::List(vec![
        sym("next-v1"),
        qstr("room-1"),
        num(0),
        qhash(&h64(0)),
        num(0),
    ]);
    let req = request_desc(
        "next-record",
        &mallory.key_id(), // WRONG recipient
        body,
        issued,
        issued + 60_000,
        THREAD,
        &env.h0(),
    );
    let rc = ReadContext::Read {
        session_id: "sess-abc".into(),
        frame_id: 7,
    };
    let sreq = env.signed_request(&req, &rc, &env.client, &env.cid());
    let bundle = request_bundle_sexpr(env.opener(&env.dh), sreq, SExpr::List(vec![]));
    let ast = recognize_request(&serialize(&bundle));
    let v = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx("room-1", 7),
        issued,
        &ast,
    );
    assert!(matches!(v, RequestVerdict::Violation(Code::NotAddressee)));
}

// ===========================================================================
// TEST-013 — transaction causality and idempotency
// ===========================================================================

#[test]
fn t13_01_causality_binds_opener_request_response() {
    let env = Env::new();
    let (payload, room, issued) = valid_commit_submit(&env);
    let ast = recognize_request(&payload);
    let vtc = match verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(&room, 7),
        issued,
        &ast,
    ) {
        RequestVerdict::Valid(_, ContentHash(h1), vtc) => {
            assert_eq!(h1, vtc.request_message_hash);
            vtc
        }
        other => panic!("{other:?}"),
    };
    // The opener is the causal root; the request is caused by h0.
    assert_eq!(vtc.opener_message_hash, env.h0());

    // A response citing the WRONG predecessor (not h1) fails causality.
    let body = SExpr::List(vec![
        sym("admitted-v1"),
        qstr(&room),
        num(1),
        qhash(&h64(0xBB)),
        qhash(&h64(0xCC)),
    ]);
    let wrong_pred = h64(0xEE);
    let msg = SExpr::List(vec![
        sym("record-admitted"),
        sym(&vtc.client_key_id),
        body,
        kw("thread"),
        qstr(&vtc.thread_id),
        kw("caused-by"),
        qhash(&wrong_pred),
    ]);
    let sig = DomainTuple::Response {
        bindings: vtc.bindings.clone(),
        dialect_hash: env.dh.clone(),
        request_content_hash: wrong_pred.clone(),
        response_message: msg.clone(),
        read_context: vtc.request_frame_context.clone(),
    }
    .sign(&env.ds);
    let signed = SExpr::List(vec![sym("signed"), sym(&env.did()), qb64(&sig), msg]);
    let payload = serialize(&SExpr::List(vec![
        sym(RESPONSE_BUNDLE_TAG),
        signed,
        SExpr::List(vec![]),
    ]));
    let rast = recognize_response(&payload);
    let rv = verify_mls_ds_response(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.ds.public_bytes(),
        &env.env_ctx(&room, 8),
        &vtc,
        &rast,
    );
    assert!(matches!(rv, ResponseVerdict::Violation(Code::Causality)));
}

#[test]
fn t13_02_thread_reuse_is_rejected() {
    let env = Env::new();
    let (payload, room, issued) = valid_commit_submit(&env);
    let ast = recognize_request(&payload);
    let vtc1 = match verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx(&room, 7),
        issued,
        &ast,
    ) {
        RequestVerdict::Valid(_, _, vtc) => vtc,
        other => panic!("{other:?}"),
    };
    let mut reg = ThreadRegistry::new();
    assert!(reg.bind(&vtc1).is_ok());
    assert!(reg.bind(&vtc1).is_ok(), "exact replay reuses the binding");

    // A DIFFERENT root (different body → different h1) on the same
    // (room, client, thread) is a terminal violation.
    let mut vtc2 = vtc1.clone();
    vtc2.request_message_hash = h64(0x99);
    assert!(matches!(reg.bind(&vtc2), Err(Code::ThreadReuse)));
}

#[test]
fn t13_15_root_window_boundaries() {
    // Read duration 60s; mutation 24h; skew 300s.
    let now = 1_000_000i64;
    // Exact valid interval, wall clock at issue.
    assert!(root_window_valid("next-record", now, now + 60_000, now));
    // Wrong interval.
    assert!(!root_window_valid("next-record", now, now + 60_001, now));
    // issued exactly at now + skew (valid boundary) vs one past.
    assert!(root_window_valid(
        "next-record",
        now + 300_000,
        now + 300_000 + 60_000,
        now
    ));
    assert!(!root_window_valid(
        "next-record",
        now + 300_001,
        now + 300_001 + 60_000,
        now
    ));
    // trusted_now exactly at expires + skew (valid) vs one past (expired).
    let issued = now;
    let expires = now + 60_000;
    assert!(root_window_valid("next-record", issued, expires, expires + 300_000));
    assert!(!root_window_valid(
        "next-record",
        issued,
        expires,
        expires + 300_001
    ));
    // Mutation uses the 24h duration.
    assert!(root_window_valid("commit-submit", now, now + 86_400_000, now));
    assert!(!root_window_valid("commit-submit", now, now + 60_000, now));
    // Overflow is a terminal violation, not a panic.
    assert!(!root_window_valid("commit-submit", i64::MAX, i64::MAX, i64::MAX));
}

#[test]
fn t13_15_end_to_end_wrong_interval_is_root_window_violation() {
    let env = Env::new();
    // Build a next-record whose expires ≠ issued + 60_000.
    let issued = 7_000_000;
    let expires = issued + 59_999; // off by one
    let body = SExpr::List(vec![
        sym("next-v1"),
        qstr("room-1"),
        num(0),
        qhash(&h64(0)),
        num(0),
    ]);
    let req = request_desc("next-record", &env.did(), body, issued, expires, THREAD, &env.h0());
    let rc = ReadContext::Read {
        session_id: "sess-abc".into(),
        frame_id: 7,
    };
    let sreq = env.signed_request(&req, &rc, &env.client, &env.cid());
    let bundle = request_bundle_sexpr(env.opener(&env.dh), sreq, SExpr::List(vec![]));
    let ast = recognize_request(&serialize(&bundle));
    let v = verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx("room-1", 7),
        issued,
        &ast,
    );
    assert!(matches!(v, RequestVerdict::Violation(Code::RootWindow)));
}

// ===========================================================================
// CON-011 — recognizer bounds
// ===========================================================================

#[test]
fn next_record_read_path_is_valid_and_at_head_reply_projects() {
    let env = Env::new();
    let issued = 8_000_000;
    let expires = issued + 60_000;
    let body = SExpr::List(vec![
        sym("next-v1"),
        qstr("room-1"),
        num(0),
        qhash(&h64(0)),
        num(0),
    ]);
    let req = request_desc("next-record", &env.did(), body, issued, expires, THREAD, &env.h0());
    let rc = ReadContext::Read {
        session_id: "sess-abc".into(),
        frame_id: 7,
    };
    let sreq = env.signed_request(&req, &rc, &env.client, &env.cid());
    let bundle = request_bundle_sexpr(env.opener(&env.dh), sreq, SExpr::List(vec![]));
    let ast = recognize_request(&serialize(&bundle));
    let vtc = match verify_mls_ds_request(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.client.public_bytes(),
        &env.client.public_bytes(),
        &env.env_ctx("room-1", 7),
        issued,
        &ast,
    ) {
        RequestVerdict::Valid(TypedRequest::NextRecord { .. }, _, vtc) => vtc,
        other => panic!("{other:?}"),
    };
    // at-head reply.
    let hbody = SExpr::List(vec![
        sym("head-v1"),
        qstr("room-1"),
        num(0),
        qhash(&h64(0)),
        num(1),
        qhash(&h64(0)),
    ]);
    let msg = SExpr::List(vec![
        sym("at-head"),
        sym(&vtc.client_key_id),
        hbody,
        kw("thread"),
        qstr(&vtc.thread_id),
        kw("caused-by"),
        qhash(&vtc.request_message_hash),
    ]);
    let sig = DomainTuple::Response {
        bindings: vtc.bindings.clone(),
        dialect_hash: env.dh.clone(),
        request_content_hash: vtc.request_message_hash.clone(),
        response_message: msg.clone(),
        read_context: vtc.request_frame_context.clone(),
    }
    .sign(&env.ds);
    let signed = SExpr::List(vec![sym("signed"), sym(&env.did()), qb64(&sig), msg]);
    let payload = serialize(&SExpr::List(vec![
        sym(RESPONSE_BUNDLE_TAG),
        signed,
        SExpr::List(vec![]),
    ]));
    let rast = recognize_response(&payload);
    let rv = verify_mls_ds_response(
        &env.d,
        &env.dh,
        &env.ds.public_bytes(),
        &env.ds.public_bytes(),
        &env.env_ctx("room-1", 8),
        &vtc,
        &rast,
    );
    assert!(matches!(
        rv,
        ResponseVerdict::Valid(TypedResponse::AtHead { .. }, _)
    ));
}

#[test]
fn recognizer_enforces_outer_byte_cap_and_depth_cap() {
    // Outer byte cap.
    let big = vec![b'a'; MAX_OUTER_BYTES + 1];
    assert!(matches!(
        recognize_dispatch_verified_outer(&big),
        OuterClass::Violation(Code::ResourceExcess)
    ));
    // A request bundle nested one level too deep (depth 9 > cap 8).
    let env = Env::new();
    let deep_body = {
        // next-v1 with an extra nested wrapper to push depth beyond 8.
        let inner = SExpr::List(vec![SExpr::List(vec![SExpr::List(vec![
            SExpr::List(vec![qhash(&h64(0))]),
        ])])]);
        SExpr::List(vec![sym("next-v1"), qstr("room-1"), num(0), inner, num(0)])
    };
    let req = request_desc(
        "next-record",
        &env.did(),
        deep_body,
        1,
        60_001,
        THREAD,
        &env.h0(),
    );
    let sreq = env.signed_request(
        &req,
        &ReadContext::Read {
            session_id: "s".into(),
            frame_id: 1,
        },
        &env.client,
        &env.cid(),
    );
    let bundle = request_bundle_sexpr(env.opener(&env.dh), sreq, SExpr::List(vec![]));
    let payload = serialize(&bundle);
    assert!(sexpr_depth(&bundle) > REQUEST_DEPTH_CAP);
    assert!(matches!(
        recognize_dispatch_verified_outer(payload.as_bytes()),
        OuterClass::Violation(Code::ResourceExcess)
    ));
}

#[test]
fn dialect_hash_is_stable_and_populated() {
    let d = mls_ds_dialect();
    assert_eq!(d.hash.as_deref(), Some(dialect_hash(&d).as_str()));
    // Deterministic across builds.
    assert_eq!(mls_ds_dialect().hash, mls_ds_dialect().hash);
}
