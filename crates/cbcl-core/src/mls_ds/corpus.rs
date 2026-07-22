//! SPEC-024 REQ-142 / TEST-018 cross-runtime parity CORPUS.
//!
//! A deterministic set of ~19 verify vectors built with **real Ed25519** keys
//! and signatures, reusing the exact fixture constructions from
//! [`super::tests`]. Every vector is a self-describing blob (see
//! [`super::run_verify_vector`] for the wire format); the same builder runs on
//! every compile target and therefore emits byte-identical INPUT blobs, so the
//! only thing the cross-target gate has to compare is the RUNNER's output.
//!
//! This module is compiled unconditionally under the `mls-ds-proof` feature
//! (NOT `cfg(test)`) so the cbcl-erl NIF and the cbcl-wasm wasm32 target can
//! both pull the identical corpus.

use super::*;
use crate::serializer::serialize;

const THREAD: &str = "0123456789abcdef0123456789abcdef";
const SESSION: &str = "sess-abc";
const FRAME: i64 = 7;

/// The pinned REQ-142 baseline digest — `corpus_digest_hex(corpus_input_vectors())`
/// computed on the NATIVE target. Every compile target (native, the cbcl-erl
/// NIF, the cbcl-wasm wasm32 build) MUST reproduce this exact hex, and all three
/// parity tests assert against this single constant. A legitimate corpus change
/// updates it here, once.
pub const NATIVE_CORPUS_DIGEST_HEX: &str =
    "b3e8a9b8d0f53bdd8d769648131d1a49819a438ad5d8daa4f27d60816bef5011";

fn kp(n: u8) -> Ed25519Keypair {
    Ed25519Keypair::from_seed(&[n; 32])
}
fn kw(k: &str) -> SExpr {
    SExpr::Atom(Atom::Keyword(String::from(k)))
}
fn qb64(sig: &[u8; 64]) -> SExpr {
    SExpr::Atom(Atom::Str(b64url_encode(sig)))
}
fn h64(byte: u8) -> String {
    let mut s = String::from("sha256:");
    push_hex(&mut s, &[byte; 32]);
    s
}

/// The Ed25519 group order L (little-endian), for the S += L malleation vector.
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
    debug_assert_eq!(carry, 0, "s + L must fit in 256 bits");
    out
}

struct Env {
    client: Ed25519Keypair,
    ds: Ed25519Keypair,
    dh: String,
}

impl Env {
    fn new() -> Self {
        let d = mls_ds_dialect();
        let dh = d.hash.clone().unwrap();
        Env {
            client: kp(1),
            ds: kp(2),
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
    fn request_sig(&self, request: &SExpr, rc: &ReadContext, signer: &Ed25519Keypair) -> [u8; 64] {
        DomainTuple::Request {
            bindings: self.bindings(),
            dialect_hash: self.dh.clone(),
            h0: self.h0(),
            request: request.clone(),
            read_context: rc.clone(),
        }
        .sign(signer)
    }
    fn signed_request(
        &self,
        request: &SExpr,
        rc: &ReadContext,
        signer: &Ed25519Keypair,
        signer_id: &str,
    ) -> SExpr {
        let sig = self.request_sig(request, rc, signer);
        SExpr::List(vec![sym("signed"), sym(signer_id), qb64(&sig), request.clone()])
    }
    /// Like [`signed_request`], but the REQUEST-SIG scalar S is malleated to
    /// S += L — a non-canonical scalar that a LAX verifier would accept but the
    /// REQ-141 strict profile rejects (T18-13). Surfaces as `wrong-signer`.
    fn signed_request_malleated(
        &self,
        request: &SExpr,
        rc: &ReadContext,
        signer: &Ed25519Keypair,
        signer_id: &str,
    ) -> SExpr {
        let sig = self.request_sig(request, rc, signer);
        let mut s = [0u8; 32];
        s.copy_from_slice(&sig[32..64]);
        let mut bad = sig;
        bad[32..64].copy_from_slice(&add_l(&s));
        SExpr::List(vec![sym("signed"), sym(signer_id), qb64(&bad), request.clone()])
    }
    fn h1(&self, request: &SExpr) -> String {
        typed_root(&Message::try_from(request).unwrap())
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
    SExpr::List(vec![sym(REQUEST_BUNDLE_TAG), opener, signed_request, sidecars])
}

// ---------------------------------------------------------------------------
// Vector envelope wrappers
// ---------------------------------------------------------------------------

fn b64(bytes: &[u8]) -> SExpr {
    SExpr::Atom(Atom::Str(b64url_encode(bytes)))
}

#[allow(clippy::too_many_arguments)]
fn request_clause(
    exp_hash: &str,
    ds_id: &str,
    client_id: &str,
    outer_id: &str,
    room: &str,
    wall: i64,
    bundle_text: &str,
) -> SExpr {
    SExpr::List(vec![
        sym("request"),
        qstr(exp_hash),
        qstr(ds_id),
        qstr(client_id),
        qstr(outer_id),
        qstr(SESSION),
        num(FRAME),
        qstr(room),
        num(wall),
        b64(bundle_text.as_bytes()),
    ])
}

fn wrap(clause: SExpr) -> Vec<u8> {
    serialize(&SExpr::List(vec![sym("mls-ds-verify-vector-v1"), clause])).into_bytes()
}

/// A whole request vector: `env` context + the serialized request bundle text.
fn request_vector(env: &Env, room: &str, wall: i64, bundle_text: &str) -> Vec<u8> {
    wrap(request_clause(
        &env.dh,
        &env.did(),
        &env.cid(),
        &env.cid(),
        room,
        wall,
        bundle_text,
    ))
}

/// A response vector: the VTC-reproducing request clause + the response bundle.
fn response_vector(env: &Env, req_clause: SExpr, room: &str, resp_bundle_text: &str) -> Vec<u8> {
    let clause = SExpr::List(vec![
        sym("response"),
        req_clause,
        qstr(SESSION),
        num(FRAME + 1),
        qstr(room),
        qstr(&env.did()),
        b64(resp_bundle_text.as_bytes()),
    ]);
    wrap(clause)
}

// ---------------------------------------------------------------------------
// Request-bundle builders (return the serialized bundle text + room + wall)
// ---------------------------------------------------------------------------

/// A valid `commit-submit` (mutation) bundle — nested SOURCE-SIG + 1 sidecar.
fn build_commit_submit(env: &Env, opener_pin: &str, source_signer: &Ed25519Keypair,
    source_signer_id: &str, malleate_req_sig: bool) -> (SExpr, String, i64) {
    let room = String::from("room-1");
    let issued = 1_000_000;
    let expires = issued + 86_400_000;
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
    let src_sig = DomainTuple::Source { source: source.clone() }.sign(source_signer);
    let signed_source = SExpr::List(vec![
        sym("source-signed"),
        sym(source_signer_id),
        qb64(&src_sig),
        source,
    ]);
    let body = SExpr::List(vec![sym("submit-v1"), signed_source]);
    let request = request_desc("commit-submit", &env.did(), body, issued, expires, THREAD, &env.h0());
    let signed_request = if malleate_req_sig {
        env.signed_request_malleated(&request, &ReadContext::None, &env.client, &env.cid())
    } else {
        env.signed_request(&request, &ReadContext::None, &env.client, &env.cid())
    };
    let sidecar = SExpr::List(vec![
        sym("blob-sidecar-v1"),
        sym("ciphertext"),
        qhash(&ct_digest),
        num(ct.len() as i64),
        qstr(&b64url_encode(ct)),
    ]);
    let bundle = request_bundle_sexpr(env.opener(opener_pin), signed_request, SExpr::List(vec![sidecar]));
    (bundle, room, issued)
}

/// A valid `commit-add-submit` bundle with a real 9-field ADD-AUTH.
fn build_commit_add_submit(env: &Env, admission_none: bool) -> (SExpr, String, i64) {
    let room = String::from("room-1");
    let issued = 6_500_000;
    let expires = issued + 86_400_000;
    let base_hash = h64(0xAA);
    let genesis_anchor = h64(0x6E);
    let ct = b"add-ciphertext";
    let wel = b"welcome-blob";
    let ct_digest = sha256_hex(ct);
    let w_digest = sha256_hex(wel);
    let ct_ref = SExpr::List(vec![sym("blob-ref-v1"), sym("ciphertext"), qhash(&ct_digest), num(ct.len() as i64)]);
    let w_ref = SExpr::List(vec![sym("blob-ref-v1"), sym("welcome"), qhash(&w_digest), num(wel.len() as i64)]);
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
    let admission_proof = if admission_none {
        sym("none")
    } else {
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
        SExpr::List(vec![
            sym("add-authorized-v1"),
            sym(&env.cid()),
            qhash(&genesis_anchor),
            qb64(&add_auth_sig),
        ])
    };
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
    let src_sig = DomainTuple::Source { source: source.clone() }.sign(&env.client);
    let signed_source = SExpr::List(vec![sym("source-signed"), sym(&env.cid()), qb64(&src_sig), source]);
    let body = SExpr::List(vec![sym("submit-add-v1"), signed_source]);
    let request = request_desc("commit-add-submit", &env.did(), body, issued, expires, THREAD, &env.h0());
    let signed_request = env.signed_request(&request, &ReadContext::None, &env.client, &env.cid());
    let sc_ct = SExpr::List(vec![
        sym("blob-sidecar-v1"), sym("ciphertext"), qhash(&ct_digest), num(ct.len() as i64), qstr(&b64url_encode(ct)),
    ]);
    let sc_w = SExpr::List(vec![
        sym("blob-sidecar-v1"), sym("welcome"), qhash(&w_digest), num(wel.len() as i64), qstr(&b64url_encode(wel)),
    ]);
    let bundle = request_bundle_sexpr(env.opener(&env.dh), signed_request, SExpr::List(vec![sc_ct, sc_w]));
    (bundle, room, issued)
}

/// A `next-record` (read) bundle. `recipient_id` and `interval_ok` let the same
/// builder produce the valid, wrong-recipient, and wrong-interval vectors.
fn build_next_record(env: &Env, recipient_id: &str, interval_ok: bool, req_signer: &Ed25519Keypair, req_signer_id: &str) -> (SExpr, String, i64) {
    let room = String::from("room-1");
    let issued = 8_000_000;
    let expires = if interval_ok { issued + 60_000 } else { issued + 59_999 };
    let body = SExpr::List(vec![sym("next-v1"), qstr("room-1"), num(0), qhash(&h64(0)), num(0)]);
    let request = request_desc("next-record", recipient_id, body, issued, expires, THREAD, &env.h0());
    let rc = ReadContext::Read { session_id: String::from(SESSION), frame_id: FRAME };
    let signed_request = env.signed_request(&request, &rc, req_signer, req_signer_id);
    let bundle = request_bundle_sexpr(env.opener(&env.dh), signed_request, SExpr::List(vec![]));
    (bundle, room, issued)
}

/// The next-record REQUEST descriptor (for computing h1 of the read path).
fn next_record_request(env: &Env) -> SExpr {
    let body = SExpr::List(vec![sym("next-v1"), qstr("room-1"), num(0), qhash(&h64(0)), num(0)]);
    request_desc("next-record", &env.did(), body, 8_000_000, 8_060_000, THREAD, &env.h0())
}

/// The commit-submit REQUEST descriptor (for computing h1 of the mutation path).
fn commit_submit_request(env: &Env) -> SExpr {
    let ct = b"ciphertext-opaque-bytes";
    let ct_ref = SExpr::List(vec![
        sym("blob-ref-v1"), sym("ciphertext"), qhash(&sha256_hex(ct)), num(ct.len() as i64),
    ]);
    let source = SExpr::List(vec![sym("commit-v1"), qstr("room-1"), num(0), qhash(&h64(0xAA)), ct_ref]);
    let src_sig = DomainTuple::Source { source: source.clone() }.sign(&env.client);
    let signed_source = SExpr::List(vec![sym("source-signed"), sym(&env.cid()), qb64(&src_sig), source]);
    let body = SExpr::List(vec![sym("submit-v1"), signed_source]);
    request_desc("commit-submit", &env.did(), body, 1_000_000, 1_000_000 + 86_400_000, THREAD, &env.h0())
}

// ---------------------------------------------------------------------------
// Response-bundle builders
// ---------------------------------------------------------------------------

/// A DS `record-admitted` response, signed over `h1` and `rc` (the request's).
fn build_admitted_response(env: &Env, room: &str, h1: &str, rc: &ReadContext, wrong_pred: bool, ds_signs: bool) -> SExpr {
    let caused = if wrong_pred { h64(0xEE) } else { h1.to_string() };
    let body = SExpr::List(vec![
        sym("admitted-v1"), qstr(room), num(1), qhash(&h64(0xBB)), qhash(&h64(0xCC)),
    ]);
    let msg = SExpr::List(vec![
        sym("record-admitted"),
        sym(&env.cid()),
        body,
        kw("thread"),
        qstr(THREAD),
        kw("caused-by"),
        qhash(&caused),
    ]);
    let sig = DomainTuple::Response {
        bindings: env.bindings(),
        dialect_hash: env.dh.clone(),
        request_content_hash: caused.clone(),
        response_message: msg.clone(),
        read_context: rc.clone(),
    }
    .sign(if ds_signs { &env.ds } else { &env.client });
    let signer_id = if ds_signs { env.did() } else { env.cid() };
    let signed = SExpr::List(vec![sym("signed"), sym(&signer_id), qb64(&sig), msg]);
    SExpr::List(vec![sym(RESPONSE_BUNDLE_TAG), signed, SExpr::List(vec![])])
}

/// A DS `at-head` response (read path), signed over `h1` and the read `rc`.
fn build_at_head_response(env: &Env, room: &str, h1: &str, rc: &ReadContext) -> SExpr {
    let hbody = SExpr::List(vec![
        sym("head-v1"), qstr(room), num(0), qhash(&h64(0)), num(1), qhash(&h64(0)),
    ]);
    let msg = SExpr::List(vec![
        sym("at-head"),
        sym(&env.cid()),
        hbody,
        kw("thread"),
        qstr(THREAD),
        kw("caused-by"),
        qhash(h1),
    ]);
    let sig = DomainTuple::Response {
        bindings: env.bindings(),
        dialect_hash: env.dh.clone(),
        request_content_hash: h1.to_string(),
        response_message: msg.clone(),
        read_context: rc.clone(),
    }
    .sign(&env.ds);
    let signed = SExpr::List(vec![sym("signed"), sym(&env.did()), qb64(&sig), msg]);
    SExpr::List(vec![sym(RESPONSE_BUNDLE_TAG), signed, SExpr::List(vec![])])
}

// ---------------------------------------------------------------------------
// The corpus
// ---------------------------------------------------------------------------

/// The REQ-142 corpus as `(label, input-bytes)` pairs. Deterministic and
/// portable: identical bytes on native, the NIF, and wasm32.
pub fn labelled_vectors() -> Vec<(&'static str, Vec<u8>)> {
    let env = Env::new();
    let mallory = kp(66);
    let mut out: Vec<(&'static str, Vec<u8>)> = Vec::new();

    // --- 1. valid commit-submit (Valid) ---
    let (b, room, wall) = build_commit_submit(&env, &env.dh, &env.client, &env.cid(), false);
    out.push(("req-valid-commit-submit", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 2. valid commit-add-submit (Valid) ---
    let (b, room, wall) = build_commit_add_submit(&env, false);
    out.push(("req-valid-commit-add-submit", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 3. valid next-record read (Valid) ---
    let (b, room, wall) = build_next_record(&env, &env.did(), true, &env.client, &env.cid());
    out.push(("req-valid-next-record", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 4. wrong dialect pin in the opener (Violation wrong-dialect-pin) ---
    let (b, room, wall) = build_commit_submit(&env, &h64(0x77), &env.client, &env.cid(), false);
    out.push(("req-wrong-dialect-pin", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 5. wrong recipient (Violation not-addressee) ---
    let (b, room, wall) = build_next_record(&env, &mallory.key_id(), true, &env.client, &env.cid());
    out.push(("req-not-addressee", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 6. wrong root signer: request signed by Mallory (Violation wrong-signer) ---
    let (b, room, wall) = build_next_record(&env, &env.did(), true, &mallory, &mallory.key_id());
    out.push(("req-wrong-root-signer", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 7. foreign nested SOURCE-SIG (Violation bad-source-signature) ---
    let (b, room, wall) = build_commit_submit(&env, &env.dh, &mallory, &mallory.key_id(), false);
    out.push(("req-bad-source-signature", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 8. commit-add-submit with `none` admission proof (Violation add-unauthorized) ---
    let (b, room, wall) = build_commit_add_submit(&env, true);
    out.push(("req-add-unauthorized", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 9. root-window off-by-one interval (Violation root-window) ---
    let (b, room, wall) = build_next_record(&env, &env.did(), false, &env.client, &env.cid());
    out.push(("req-root-window", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 10. tampered sidecar digest (Violation sidecar) ---
    let (b, room, wall) = build_commit_submit(&env, &env.dh, &env.client, &env.cid(), false);
    let tampered = tamper_sidecar_digest(&serialize(&b));
    out.push(("req-sidecar-tamper", request_vector(&env, &room, wall, &tampered)));

    // --- 11. T18-13 strict-Ed25519: REQUEST-SIG scalar S += L (Violation wrong-signer) ---
    let (b, room, wall) = build_commit_submit(&env, &env.dh, &env.client, &env.cid(), true);
    out.push(("req-strict-ed25519-malleated-request-sig", request_vector(&env, &room, wall, &serialize(&b))));

    // --- 12. reserved performative via the generic route (recognize-violation) ---
    out.push(("recognize-reserved-mls-control",
        request_vector(&env, "room-1", 1_000_000, "(record-admitted @x (foo))")));

    // --- 13. resource-excess: request bundle nested one level past the depth cap ---
    let deep = build_depth_excess_bundle(&env);
    out.push(("recognize-resource-excess", request_vector(&env, "room-1", 1, &serialize(&deep))));

    // --- 14. valid record-admitted response (Valid) ---
    let (cb, croom, cwall) = build_commit_submit(&env, &env.dh, &env.client, &env.cid(), false);
    let creq_clause = request_clause(&env.dh, &env.did(), &env.cid(), &env.cid(), &croom, cwall, &serialize(&cb));
    let h1 = env.h1(&commit_submit_request(&env));
    let resp = build_admitted_response(&env, &croom, &h1, &ReadContext::None, false, true);
    out.push(("resp-valid-record-admitted", response_vector(&env, creq_clause.clone(), &croom, &serialize(&resp))));

    // --- 15. valid at-head response, read path (Valid) ---
    let (nb, nroom, nwall) = build_next_record(&env, &env.did(), true, &env.client, &env.cid());
    let nreq_clause = request_clause(&env.dh, &env.did(), &env.cid(), &env.cid(), &nroom, nwall, &serialize(&nb));
    let nh1 = env.h1(&next_record_request(&env));
    let nrc = ReadContext::Read { session_id: String::from(SESSION), frame_id: FRAME };
    let ahead = build_at_head_response(&env, &nroom, &nh1, &nrc);
    out.push(("resp-valid-at-head", response_vector(&env, nreq_clause, &nroom, &serialize(&ahead))));

    // --- 16. response citing the wrong predecessor (Violation causality) ---
    let wrong = build_admitted_response(&env, &croom, &h1, &ReadContext::None, true, true);
    out.push(("resp-causality", response_vector(&env, creq_clause.clone(), &croom, &serialize(&wrong))));

    // --- 17. member-signed response (Violation wrong-signer) ---
    let member = build_admitted_response(&env, &croom, &h1, &ReadContext::None, false, false);
    out.push(("resp-member-signed-wrong-signer", response_vector(&env, creq_clause, &croom, &serialize(&member))));

    // --- 18. direct Unknown (request side) — the outcome verify never returns ---
    out.push(("direct-unknown-request",
        wrap(SExpr::List(vec![sym("direct"), sym("request"), sym("unknown"),
            SExpr::List(vec![qstr(&h64(0x11)), qstr(&h64(0x22))])]))));

    // --- 19. direct Unknown (response side) ---
    out.push(("direct-unknown-response",
        wrap(SExpr::List(vec![sym("direct"), sym("response"), sym("unknown"),
            SExpr::List(vec![qstr(&h64(0x33))])]))));

    out
}

/// The corpus input blobs, in order (label stripped).
pub fn corpus_input_vectors() -> Vec<Vec<u8>> {
    labelled_vectors().into_iter().map(|(_, v)| v).collect()
}

/// Corrupt the sidecar's declared digest so it no longer matches its bytes
/// (identical surgery to the `t12_02` fixture).
fn tamper_sidecar_digest(payload: &str) -> String {
    let needle = "blob-sidecar-v1";
    let pos = payload.find(needle).unwrap();
    let (head, tail) = payload.split_at(pos);
    let hpos = tail.find("sha256:").unwrap() + "sha256:".len();
    let mut tail = tail.to_string();
    let ch = tail.as_bytes()[hpos];
    let repl = if ch == b'0' { '1' } else { '0' };
    tail.replace_range(hpos..hpos + 1, &repl.to_string());
    let mut s = String::from(head);
    s.push_str(&tail);
    s
}

/// A request bundle whose AST depth exceeds the CON-011 request cap (8).
fn build_depth_excess_bundle(env: &Env) -> SExpr {
    let inner = SExpr::List(vec![SExpr::List(vec![SExpr::List(vec![SExpr::List(vec![qhash(
        &h64(0),
    )])])])]);
    let deep_body = SExpr::List(vec![sym("next-v1"), qstr("room-1"), num(0), inner, num(0)]);
    let req = request_desc("next-record", &env.did(), deep_body, 1, 60_001, THREAD, &env.h0());
    let rc = ReadContext::Read { session_id: String::from("s"), frame_id: 1 };
    let sreq = env.signed_request(&req, &rc, &env.client, &env.cid());
    request_bundle_sexpr(env.opener(&env.dh), sreq, SExpr::List(vec![]))
}
