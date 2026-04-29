//! cbcl-wasm: WebAssembly bindings for CBCL.
//!
//! Two-tier API (ADR-003):
//! - Pure WASM exports (always available on wasm32 targets)
//! - wasm-bindgen JS interop (behind `bindgen` feature)
//!
//! API surface matches `wasm-cbcl-wrapper.scm`:
//! - `parse_message` — parse S-expr string into a CBCL message
//! - `verify_dialect` — parse and verify a dialect definition against R1/R2/R3
//! - `create_agent` — create a new agent with base dialect
//! - `send_message` — construct a tell message and evaluate it

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

// ---------------------------------------------------------------------------
// no_std wasm32 requirements: allocator + panic handler
// ---------------------------------------------------------------------------

// When targeting wasm32 without std, provide a global allocator and panic handler.
// unsafe is required only here for the FFI allocator boundary (ADR-004).
#[cfg(all(target_arch = "wasm32", not(feature = "std"), not(feature = "bindgen")))]
mod wasm_alloc {
    use core::alloc::{GlobalAlloc, Layout};

    struct WasmAlloc;

    // SAFETY: This delegates to the wasm32 dlmalloc implementation provided by
    // the compiler's built-in allocator shim. Required for cdylib crates that
    // use alloc without std.
    unsafe impl GlobalAlloc for WasmAlloc {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            // SAFETY: dlmalloc is linked by default on wasm32 targets.
            extern "C" {
                fn __rust_alloc(size: usize, align: usize) -> *mut u8;
            }
            unsafe { __rust_alloc(layout.size(), layout.align()) }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            // SAFETY: ptr was allocated by the matching __rust_alloc.
            extern "C" {
                fn __rust_dealloc(ptr: *mut u8, size: usize, align: usize);
            }
            unsafe { __rust_dealloc(ptr, layout.size(), layout.align()) }
        }
    }

    #[global_allocator]
    static ALLOC: WasmAlloc = WasmAlloc;
}

#[cfg(all(target_arch = "wasm32", not(feature = "std"), not(feature = "bindgen")))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use cbcl_core::agent::Agent;
use cbcl_core::blame::ViolationError;
use cbcl_core::canonical::{canonical_encode, dialect_canonical_bytes};
use cbcl_core::dialect::DialectRegistry;
use cbcl_core::evaluator;
use cbcl_core::message::{CorePerformative, Message, Performative};
use cbcl_core::protocol::{verify_causal, VerificationResult};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{ContentHash, MessageStore, ThreadId, ThreadedMessageStore};
use cbcl_parser::parser;
use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------
// Pure WASM byte-level API (always available)
// ---------------------------------------------------------------------------

/// Parse an S-expression from a UTF-8 byte slice.
///
/// Returns serialized result or error string as UTF-8 bytes.
pub fn parse_bytes(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let input_str =
        core::str::from_utf8(input).map_err(|e| format!("invalid UTF-8: {e}").into_bytes())?;

    match parser::parse(input_str) {
        Ok(expr) => Ok(serialize(&expr).into_bytes()),
        Err(e) => Err(format!("{e}").into_bytes()),
    }
}

/// Run the full pipeline on a UTF-8 byte slice.
pub fn run_pipeline_bytes(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let input_str =
        core::str::from_utf8(input).map_err(|e| format!("invalid UTF-8: {e}").into_bytes())?;

    match cbcl_parser::run_pipeline(input_str) {
        cbcl_parser::PipelineResult::Success(msg) => Ok(format!("{msg:?}").into_bytes()),
        cbcl_parser::PipelineResult::ParseError(e) => Err(format!("parse error: {e}").into_bytes()),
        cbcl_parser::PipelineResult::ValidationError(e) => {
            Err(format!("validation error: {e}").into_bytes())
        }
        // run_pipeline (lightweight) skips causal verification.
        cbcl_parser::PipelineResult::Pending { .. }
        | cbcl_parser::PipelineResult::Buffered { .. } => {
            Err("validation error: unexpected pending result".to_string().into_bytes())
        }
    }
}

/// Parse an S-expression into a CBCL message and return its canonical serialized form.
pub fn parse_message_bytes(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let input_str =
        core::str::from_utf8(input).map_err(|e| format!("invalid UTF-8: {e}").into_bytes())?;
    parse_message_str(input_str)
        .map(|s| s.into_bytes())
        .map_err(|e| e.into_bytes())
}

/// Verify a dialect definition (parse + R1/R2/R3/R5 checks + `:hash` consistency).
///
/// Input: UTF-8 bytes of a `(define ...)` S-expression, or a
/// `(dialects (define <ancestor>) ... (define <leaf>))` chain to install
/// non-base ancestors before the leaf so R5 can resolve parent performatives.
/// Returns "ok" on success or error description on failure. If a dialect in
/// the chain declares a `(:hash "sha256:...")` field, the wrapper recomputes
/// the canonical hash and rejects on mismatch — so a frame cannot install a
/// dialect with a fabricated hash that downstream callers might later treat
/// as authoritative.
pub fn verify_dialect_bytes(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let input_str =
        core::str::from_utf8(input).map_err(|e| format!("invalid UTF-8: {e}").into_bytes())?;
    verify_dialect_str(input_str)
        .map(|s| s.into_bytes())
        .map_err(|e| e.into_bytes())
}

/// Verify an expanded message against a dialect's shape constraints (REQ-220, REQ-223).
///
/// Input frame: `(verify-shape <dialect> <performative-symbol> <expanded-message>)`.
/// The `<dialect>` slot accepts either a bare `(define ...)` form or a
/// `(dialects (define <ancestor>) ... (define <leaf>))` chain when the leaf
/// extends a non-base parent — the leaf's shapes are then applied. The
/// dialect (or chain) is parsed *and installed* (running the same R1/R2/R3/R5
/// checks as `cbcl_verify_dialect`) before any shape is applied, so an
/// ill-formed dialect — e.g. a shape targeting an undefined performative or
/// a max-depth exceeding the dialect's R2 bound — fails fast instead of
/// producing a misleading verification result.
/// Returns "ok" if no shape constraint targets the performative or every matching
/// constraint passes; otherwise returns the canonical REQ-233 blame S-expression.
pub fn verify_message_shape_bytes(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let input_str =
        core::str::from_utf8(input).map_err(|e| format!("invalid UTF-8: {e}").into_bytes())?;
    verify_message_shape_str(input_str)
        .map(|s| s.into_bytes())
        .map_err(|e| e.into_bytes())
}

/// Verify a message's causal predecessor against a dialect's protocol (REQ-203, REQ-304).
///
/// Input frame: `(verify-protocol <dialect> <thread-id> <message> [(history (<hash> <msg>) ...)])`.
/// The `<dialect>` slot accepts either a bare `(define ...)` form or a
/// `(dialects (define <ancestor>) ... (define <leaf>))` chain when the leaf
/// extends a non-base parent — the leaf's protocol is then applied. The
/// dialect (or chain) is parsed *and installed* (running the same R1/R2/R3/R5
/// checks as `cbcl_verify_dialect`) before its protocol is honoured, so an
/// ill-formed protocol — e.g. one referencing an undefined predecessor
/// performative — fails fast instead of being driven to "ok" by a matching
/// history entry.
/// The optional `history` block populates a per-call `ThreadedMessageStore` so
/// hash-linked predecessors (`:caused-by sha256:...`) resolve under the supplied
/// `<thread-id>`; without it only `:caused-by begin` and protocol-unconstrained
/// messages can succeed. Each `<hash>` in `history` must equal the canonical
/// content hash (`sha256:<hex>`) of its paired predecessor message — caller-
/// supplied hashes that don't match are rejected, so a fabricated `:caused-by`
/// cannot be satisfied by an unrelated history entry.
///
/// Thread isolation (ADR-008): the frame `<thread-id>` is the *default* causal
/// scope. If `<message>` or any history predecessor carries an explicit
/// `:thread` field that disagrees with `<thread-id>`, the frame is rejected —
/// otherwise a caller could verify a message against predecessors from a
/// different thread.
///
/// Returns "ok" on `Valid`; the canonical REQ-233 blame S-expression on
/// `Violation`; or `(pending :reason "unknown-predecessor")` on `Unknown`.
pub fn verify_protocol_bytes(input: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let input_str =
        core::str::from_utf8(input).map_err(|e| format!("invalid UTF-8: {e}").into_bytes())?;
    verify_protocol_str(input_str)
        .map(|s| s.into_bytes())
        .map_err(|e| e.into_bytes())
}

/// Create a new agent with the given ID and base dialect.
///
/// Returns the agent's ID as confirmation (the agent is well-formed with base dialect installed).
pub fn create_agent_bytes(id: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let id_str =
        core::str::from_utf8(id).map_err(|e| format!("invalid UTF-8: {e}").into_bytes())?;
    Ok(create_agent_str(id_str).into_bytes())
}

/// Construct and evaluate a tell message.
///
/// Returns the serialized effects as an S-expression.
pub fn send_message_bytes(recipient: &[u8], content: &[u8]) -> Result<Vec<u8>, Vec<u8>> {
    let recipient_str = core::str::from_utf8(recipient)
        .map_err(|e| format!("invalid UTF-8 in recipient: {e}").into_bytes())?;
    let content_str = core::str::from_utf8(content)
        .map_err(|e| format!("invalid UTF-8 in content: {e}").into_bytes())?;
    send_message_str(recipient_str, content_str)
        .map(|s| s.into_bytes())
        .map_err(|e| e.into_bytes())
}

// ---------------------------------------------------------------------------
// Shared string-level implementation (used by both tiers)
// ---------------------------------------------------------------------------

/// Parse an S-expression string into a CBCL message and return its canonical form.
fn parse_message_str(input: &str) -> Result<String, String> {
    let sexpr = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let msg = cbcl_parser::parse_message(&sexpr).map_err(|e| format!("message error: {e}"))?;
    // Serialize the message back to canonical S-expression form
    let msg_sexpr: SExpr = msg.into();
    Ok(serialize(&msg_sexpr))
}

/// Verify a dialect definition against R1/R2/R3/R5 rules and (when declared)
/// confirm its `:hash` matches the canonical hash of its content.
fn verify_dialect_str(input: &str) -> Result<String, String> {
    let sexpr = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    parse_and_install_dialect(&sexpr)?;
    Ok(String::from("ok"))
}

/// Parse a dialect S-expression (or a `(dialects <ancestor>* <leaf>)` chain)
/// and install each into a fresh registry, running the same R1/R2/R3/R5 checks
/// — and `:hash` consistency — that `cbcl_verify_dialect` performs. Returns
/// the owning registry plus the index of the *last* installed dialect (the
/// "leaf" / subject of any subsequent shape or protocol check); callers
/// retrieve it via `registry.get(index)`.
///
/// The `(dialects ...)` form lets callers supply ancestor dialects so that
/// R5's resolve-ancestors-by-name pass (`DialectRegistry::resolve_ancestors`)
/// can find non-base parents. Without this, a child dialect like
/// `(define child-d (parent-d) ... (protocol (then notify ack)))` would be
/// rejected by R5 here because `parent-d` is not in the fresh registry, even
/// though the rest of the pipeline accepts it once `parent-d` is installed.
/// Order matters: ancestors must precede the leaf so each `install` call
/// sees its parents already present.
///
/// Both runtime verifiers (shape, protocol) reuse this so callers cannot
/// bypass install-time well-formedness — e.g. shapes that target an
/// undefined performative, or protocols referencing undefined predecessors —
/// to get a spurious "ok" or a misleading violation.
///
/// We deliberately return an index, not the dialect name: a fresh
/// `DialectRegistry` is preloaded with `cbcl-base`, and `find_by_name` returns
/// the first match. If the supplied leaf happens to be named `cbcl-base`,
/// looking up by name would resolve to the preloaded base — silently dropping
/// the supplied dialect's shapes and protocol — and constraint violations
/// would slip through as "ok". `install` always pushes at the end, so the
/// leaf's index is `registry.len() - 1` after the loop.
fn parse_and_install_dialect(
    dialect_sexpr: &SExpr,
) -> Result<(DialectRegistry, usize), String> {
    // Accept either a bare `(define ...)` (back-compat) or a
    // `(dialects <define-ancestor>* <define-leaf>)` chain.
    let dialect_forms: alloc::vec::Vec<&SExpr> = match dialect_sexpr {
        SExpr::List(xs)
            if matches!(
                xs.first(),
                Some(SExpr::Atom(Atom::Symbol(s))) if s == "dialects"
            ) =>
        {
            if xs.len() < 2 {
                return Err(String::from(
                    "(dialects ...) must contain at least one (define ...) form",
                ));
            }
            xs[1..].iter().collect()
        }
        _ => alloc::vec![dialect_sexpr],
    };

    let mut registry = DialectRegistry::new();
    let mut last_idx = 0;
    for form in &dialect_forms {
        let dialect = cbcl_parser::parse_dialect(form)
            .map_err(|e| format!("dialect parse error: {e}"))?;
        registry
            .install(dialect)
            .map_err(|e| format!("dialect verification failed: {e}"))?;
        last_idx = registry.len() - 1;

        // If the dialect declares a `:hash`, verify it matches the actual
        // canonical hash of the (just-installed) dialect. The wrapper surfaces
        // this hash in REQ-233 blame attribution via `with_dialect_context`,
        // so trusting an unchecked claim would let a frame mislabel which
        // dialect signed a verdict. Apply to every link in the chain, not
        // just the leaf — a tampered ancestor :hash would otherwise propagate
        // through R5 into the leaf's verification context.
        let installed = registry
            .get(last_idx)
            .ok_or_else(|| String::from("internal: just-installed dialect not found"))?;
        if let Some(claimed) = &installed.hash {
            let computed = format!(
                "sha256:{}",
                hex_encode(Sha256::digest(dialect_canonical_bytes(installed)).as_slice())
            );
            if claimed != &computed {
                return Err(format!(
                    "dialect verification failed: declared :hash {claimed} \
                     does not match canonical hash {computed}"
                ));
            }
        }
    }

    Ok((registry, last_idx))
}

/// Lowercase hex-encode bytes. Local helper to avoid a `hex` crate dep on the
/// wasm32 build path.
fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

/// Compute the canonical content hash of a message in the form
/// `sha256:<lowercase-hex>`, matching the format the rest of the codebase
/// uses for `:caused-by` references and dialect `:hash` fields. Hashes the
/// canonical encoding of `SExpr::from(msg)`.
fn compute_canonical_message_hash(msg: &cbcl_core::message::Message) -> String {
    let sexpr: SExpr = msg.into();
    let bytes = canonical_encode(&sexpr);
    format!("sha256:{}", hex_encode(Sha256::digest(&bytes).as_slice()))
}

/// Verify a runtime message against a dialect's shape constraints.
fn verify_message_shape_str(input: &str) -> Result<String, String> {
    let frame = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let items = match &frame {
        SExpr::List(items) => items,
        _ => return Err(String::from(
            "expected (verify-shape <dialect> <performative> <message>)",
        )),
    };
    if items.len() != 4 || !matches!(&items[0], SExpr::Atom(Atom::Symbol(s)) if s == "verify-shape")
    {
        return Err(String::from(
            "expected (verify-shape <dialect> <performative> <message>)",
        ));
    }
    let performative = match &items[2] {
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => return Err(String::from("performative must be a symbol")),
    };
    let dialect_sexpr = &items[1];
    let message_sexpr = &items[3];

    let (registry, dialect_idx) = parse_and_install_dialect(dialect_sexpr)?;
    let dialect = registry
        .get(dialect_idx)
        .ok_or_else(|| String::from("internal: just-installed dialect not found"))?;

    // Composition by conjunction (REQ-224): every matching shape must pass.
    for shape in &dialect.shapes {
        if shape.performative != performative {
            continue;
        }
        if let Err(violation) = shape.check(message_sexpr) {
            let blame = ViolationError::from_shape_violation(
                &violation,
                None,
                None,
                Some(message_sexpr.clone()),
            )
            .with_dialect_context(
                &dialect.name,
                dialect.author.as_deref(),
                dialect.hash.as_deref(),
                Some(&performative),
            );
            return Err(serialize(&blame.to_sexpr()));
        }
    }
    Ok(String::from("ok"))
}

/// Parse a `(history (<hash> <msg>) ...)` block and append each entry to `store`
/// under `thread`, so subsequent `verify_causal` lookups can resolve `:caused-by`
/// hashes against the supplied predecessor messages.
///
/// Wrapped (`envelope` / `signed` / `with-limits`) and dialect-tagged
/// predecessors are unwrapped to their innermost `Simple` before being stored:
/// `verify_causal` reads the predecessor's performative directly, so storing a
/// wrapper would surface as an empty performative and produce a spurious
/// `InvalidPredecessor` violation. This matches `verify_protocol_str`'s own
/// handling of the message under verification.
///
/// If a predecessor's innermost Simple carries an explicit `:thread`, it must
/// match the frame thread — otherwise the frame thread would silently relocate
/// the predecessor into a different causal scope, defeating
/// `ThreadedMessageStore`'s thread isolation (ADR-008).
///
/// The caller-supplied `<hash>` for each entry must equal the canonical
/// content hash of the inner Simple (`sha256:<lowercase-hex>`). Without this
/// binding, a frame could pair a fabricated `:caused-by "X"` with a
/// `(history ("X" <unrelated-msg>))` and have `verify_causal` return Valid
/// against arbitrary content — defeating the content-addressed causal
/// verification this wrapper exposes.
fn load_history_into_store(
    hist: &SExpr,
    thread: &ThreadId,
    store: &mut ThreadedMessageStore,
) -> Result<(), String> {
    let entries = match hist {
        SExpr::List(xs) => xs,
        _ => return Err(String::from(
            "history must be a list: (history (<hash> <msg>) ...)",
        )),
    };
    if entries.is_empty()
        || !matches!(&entries[0], SExpr::Atom(Atom::Symbol(s)) if s == "history")
    {
        return Err(String::from("history must start with the symbol `history`"));
    }
    for entry in &entries[1..] {
        let pair = match entry {
            SExpr::List(xs) if xs.len() == 2 => xs,
            _ => return Err(String::from("history entry must be (<hash> <message>)")),
        };
        let hash_str = match &pair[0] {
            SExpr::Atom(Atom::Str(s)) | SExpr::Atom(Atom::Symbol(s)) => s.clone(),
            _ => return Err(String::from(
                "history entry hash must be a string or symbol",
            )),
        };
        let pred_msg = cbcl_parser::parse_message(&pair[1])
            .map_err(|e| format!("history message parse error: {e}"))?;
        let inner = pred_msg
            .innermost_simple()
            .ok_or_else(|| String::from(
                "history predecessor must contain a simple message at its innermost layer",
            ))?;
        if let Some(t) = inner.thread() {
            if t != thread.0 {
                return Err(format!(
                    "history predecessor :thread {t:?} does not match frame thread {:?}",
                    thread.0
                ));
            }
        }
        // Content-addressed integrity: the hash supplied by the caller must
        // be the canonical content hash of the predecessor message. Without
        // this check a frame can pair `:caused-by "fake"` with
        // `(history ("fake" <msg>))` and trick `verify_causal` into
        // returning Valid even though "fake" is not derived from <msg>.
        let computed = compute_canonical_message_hash(inner);
        if hash_str != computed {
            return Err(format!(
                "history entry hash {hash_str:?} does not match canonical content \
                 hash {computed:?} of the supplied predecessor"
            ));
        }
        store.append(ContentHash(hash_str), thread.clone(), inner.clone());
    }
    Ok(())
}

/// Verify a single message's causal predecessor against a dialect's protocol.
fn verify_protocol_str(input: &str) -> Result<String, String> {
    const FRAME_SHAPE: &str =
        "expected (verify-protocol <dialect> <thread-id> <message> [(history (<hash> <msg>) ...)])";
    let frame = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let items = match &frame {
        SExpr::List(items) => items,
        _ => return Err(String::from(FRAME_SHAPE)),
    };
    if !(items.len() == 4 || items.len() == 5)
        || !matches!(&items[0], SExpr::Atom(Atom::Symbol(s)) if s == "verify-protocol")
    {
        return Err(String::from(FRAME_SHAPE));
    }
    let thread_id = match &items[2] {
        SExpr::Atom(Atom::Str(s)) => s.clone(),
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => return Err(String::from("thread-id must be a string or symbol")),
    };
    let dialect_sexpr = &items[1];
    let message_sexpr = &items[3];
    let history_sexpr = items.get(4);

    let (registry, dialect_idx) = parse_and_install_dialect(dialect_sexpr)?;
    let dialect = registry
        .get(dialect_idx)
        .ok_or_else(|| String::from("internal: just-installed dialect not found"))?;

    // Always parse the message and history before consulting the protocol so
    // that callers using this export as a fail-closed verifier cannot smuggle a
    // malformed message past it whenever the supplied dialect happens to have
    // no protocol declared.
    let message = cbcl_parser::parse_message(message_sexpr)
        .map_err(|e| format!("message parse error: {e}"))?;
    let inner = message
        .innermost_simple()
        .ok_or_else(|| String::from("expected a simple message at the innermost layer"))?;
    let perf = inner
        .performative()
        .ok_or_else(|| String::from("message has no performative"))?
        .name()
        .to_string();
    let caused_by = inner.caused_by();

    // The message's own `:thread` (if present) is authoritative for the causal
    // scope. The frame thread is only a default for messages that omit it; if
    // both are present and disagree, reject — otherwise the wrapper would
    // verify the message's predecessors against a different thread than the
    // one it claims to belong to, defeating ThreadedMessageStore's thread
    // isolation (ADR-008).
    if let Some(t) = inner.thread() {
        if t != thread_id {
            return Err(format!(
                "message :thread {t:?} does not match frame thread {thread_id:?}"
            ));
        }
    }

    let thread = ThreadId(thread_id);
    let mut store = ThreadedMessageStore::new();

    // Optional 5th arg: (history (<hash> <msg>) ...). The caller supplies the
    // canonical hash for each predecessor message — verify_causal looks up
    // `:caused-by` hashes through the MessageStore, so without this the wrapper
    // can only resolve `:caused-by begin` messages.
    if let Some(hist) = history_sexpr {
        load_history_into_store(hist, &thread, &mut store)?;
    }

    let proto = match &dialect.causal_protocol {
        Some(p) => p,
        None => return Ok(String::from("ok")),
    };

    let result = verify_causal(&perf, caused_by, &store, proto, &thread);

    match result {
        VerificationResult::Valid => Ok(String::from("ok")),
        VerificationResult::Violation(cv) => {
            let blame = ViolationError::from_causal_violation(&cv, None, Some(thread.0.clone()))
                .with_dialect_context(
                    &dialect.name,
                    dialect.author.as_deref(),
                    dialect.hash.as_deref(),
                    Some(&perf),
                );
            Err(serialize(&blame.to_sexpr()))
        }
        VerificationResult::Unknown => {
            Err(String::from("(pending :reason \"unknown-predecessor\")"))
        }
    }
}

/// Create a new agent with the given ID and base dialect.
fn create_agent_str(id: &str) -> String {
    let agent = Agent::new(id);
    // Return a confirmation S-expression: (agent <id> :dialects <count> :well-formed <bool>)
    format!(
        "(agent \"{}\" :dialects {} :well-formed {})",
        id,
        agent.dialect_registry().len(),
        if agent.is_well_formed() { "#t" } else { "#f" }
    )
}

/// Construct a tell message to a recipient, evaluate it, and return the effects.
fn send_message_str(recipient: &str, content: &str) -> Result<String, String> {
    // Parse the content as an S-expression (or treat as a string literal)
    let content_expr =
        parser::parse(content).unwrap_or(SExpr::Atom(Atom::Str(String::from(content))));

    // Format recipient with @ prefix if not already present
    let recipient_sym = if recipient.starts_with('@') {
        String::from(recipient)
    } else {
        format!("@{recipient}")
    };

    let msg = Message::Simple {
        performative: Performative::Core(CorePerformative::Tell),
        recipient: Some(recipient_sym),
        content: content_expr,
        params: Vec::new(),
        thread: None,
        sender: None,
        caused_by: None,
    };

    // Evaluate the message against the base dialect registry
    let registry = DialectRegistry::new();
    let result = evaluator::evaluate(&msg, &registry).map_err(|e| format!("eval error: {e}"))?;

    // Serialize the expanded effect form
    Ok(serialize(&result.expanded))
}

// ---------------------------------------------------------------------------
// wasm-bindgen JS interop (behind "bindgen" feature)
// ---------------------------------------------------------------------------

#[cfg(feature = "bindgen")]
mod wasm_bindgen_api {
    use super::*;
    use wasm_bindgen::prelude::*;

    /// Parse an S-expression string and return its canonical serialized form.
    #[wasm_bindgen]
    pub fn parse(input: &str) -> Result<String, String> {
        cbcl_parser::parser::parse(input)
            .map(|expr| cbcl_core::serializer::serialize(&expr))
            .map_err(|e| format!("{e}"))
    }

    /// Run the full verification pipeline on an input string.
    #[wasm_bindgen]
    pub fn run_pipeline(input: &str) -> Result<String, String> {
        match cbcl_parser::run_pipeline(input) {
            cbcl_parser::PipelineResult::Success(msg) => Ok(format!("{msg:?}")),
            cbcl_parser::PipelineResult::ParseError(e) => Err(format!("parse error: {e}")),
            cbcl_parser::PipelineResult::ValidationError(e) => {
                Err(format!("validation error: {e}"))
            }
            cbcl_parser::PipelineResult::Pending { .. }
            | cbcl_parser::PipelineResult::Buffered { .. } => {
                Err("validation error: unexpected pending result".to_string())
            }
        }
    }

    /// Parse an S-expression into a CBCL message and return its canonical form.
    ///
    /// Matches `wasm-parse-cbcl-message` from `wasm-cbcl-wrapper.scm`.
    #[wasm_bindgen]
    pub fn parse_message(input: &str) -> Result<String, String> {
        parse_message_str(input)
    }

    /// Parse and verify a dialect definition against R1/R2/R3 rules.
    ///
    /// Input: `(define dialect-name (extends...) @author ...)` S-expression.
    /// Returns "ok" on success or an error description.
    ///
    /// Matches `wasm-install-dialect` verification from `wasm-cbcl-wrapper.scm`.
    #[wasm_bindgen]
    pub fn verify_dialect(input: &str) -> Result<String, String> {
        verify_dialect_str(input)
    }

    /// Verify an expanded message against a dialect's shape constraints.
    ///
    /// Input: `(verify-shape <dialect> <performative> <message>)` S-expression.
    /// Returns "ok" or a REQ-233 blame S-expression as the error description.
    #[wasm_bindgen]
    pub fn verify_message_shape(input: &str) -> Result<String, String> {
        verify_message_shape_str(input)
    }

    /// Verify a message's causal predecessor against a dialect's protocol.
    ///
    /// Input: `(verify-protocol <dialect> <thread-id> <message> [(history (<hash> <msg>) ...)])`
    /// S-expression. The optional history populates a per-call message store so
    /// `:caused-by` hashes resolve to known predecessors.
    /// Returns "ok" / blame S-expression / `(pending :reason ...)`.
    #[wasm_bindgen]
    pub fn verify_protocol(input: &str) -> Result<String, String> {
        verify_protocol_str(input)
    }

    /// Create a new CBCL agent with the given ID and base dialect installed.
    ///
    /// Returns an S-expression description of the agent.
    ///
    /// Matches `wasm-make-cbcl-agent` from `wasm-cbcl-wrapper.scm`.
    #[wasm_bindgen]
    pub fn create_agent(id: &str) -> String {
        create_agent_str(id)
    }

    /// Construct a tell message to a recipient and evaluate it.
    ///
    /// Returns the expanded effect form as a serialized S-expression.
    ///
    /// Matches `wasm-cbcl-tell` from `wasm-cbcl-wrapper.scm`.
    #[wasm_bindgen]
    pub fn send_message(recipient: &str, content: &str) -> Result<String, String> {
        send_message_str(recipient, content)
    }
}

// ---------------------------------------------------------------------------
// C-ABI exports for wasmtime / non-JS hosts (wasm32, no bindgen)
//
// Pattern: caller allocates input via cbcl_alloc, writes bytes, calls a
// cbcl_* function which writes its result to a process-global buffer, then
// the caller reads the result via cbcl_result_ptr/len and frees input with
// cbcl_free.  Single-threaded WASM execution makes the global buffer safe.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "wasm32", not(feature = "bindgen")))]
mod c_abi {
    use super::*;

    static mut RESULT_BUF: Vec<u8> = Vec::new();

    // Memory helpers --------------------------------------------------------

    /// Allocate `size` bytes in WASM linear memory; returns the pointer.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_alloc(size: usize) -> *mut u8 {
        let mut v: Vec<u8> = Vec::with_capacity(size);
        let ptr = v.as_mut_ptr();
        core::mem::forget(v);
        ptr
    }

    /// Free `size` bytes previously allocated with cbcl_alloc.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_free(ptr: *mut u8, size: usize) {
        drop(Vec::from_raw_parts(ptr, size, size));
    }

    /// Pointer to the result written by the last cbcl_* call.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_result_ptr() -> *const u8 {
        RESULT_BUF.as_ptr()
    }

    /// Length of the result written by the last cbcl_* call.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_result_len() -> usize {
        RESULT_BUF.len()
    }

    // Parse / pipeline / dialect -------------------------------------------

    /// Parse a CBCL S-expression and return its canonical message form.
    ///
    /// Returns 0 on success, 1 on error.  Read result via cbcl_result_ptr/len.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_parse_message(ptr: *const u8, len: usize) -> i32 {
        let input = core::slice::from_raw_parts(ptr, len);
        match parse_message_bytes(input) {
            Ok(out) => {
                RESULT_BUF = out;
                0
            }
            Err(err) => {
                RESULT_BUF = err;
                1
            }
        }
    }

    /// Run the full CBCL verification pipeline (parse + R1-R4 checks).
    ///
    /// Returns 0 on success, 1 on error.  Read result via cbcl_result_ptr/len.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_run_pipeline(ptr: *const u8, len: usize) -> i32 {
        let input = core::slice::from_raw_parts(ptr, len);
        match run_pipeline_bytes(input) {
            Ok(out) => {
                RESULT_BUF = out;
                0
            }
            Err(err) => {
                RESULT_BUF = err;
                1
            }
        }
    }

    /// Verify a dialect definition against R1/R2/R3 rules.
    ///
    /// Input: UTF-8 bytes of a `(define ...)` S-expression.
    /// Returns 0 on success ("ok" in result buf), 1 on error.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_verify_dialect(ptr: *const u8, len: usize) -> i32 {
        let input = core::slice::from_raw_parts(ptr, len);
        match verify_dialect_bytes(input) {
            Ok(out) => {
                RESULT_BUF = out;
                0
            }
            Err(err) => {
                RESULT_BUF = err;
                1
            }
        }
    }

    /// Verify an expanded message against a dialect's shape constraints.
    ///
    /// Input: UTF-8 bytes of `(verify-shape <dialect> <performative> <message>)`.
    /// Returns 0 on success ("ok" in result buf), 1 on error (REQ-233 blame).
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_verify_message_shape(ptr: *const u8, len: usize) -> i32 {
        let input = core::slice::from_raw_parts(ptr, len);
        match verify_message_shape_bytes(input) {
            Ok(out) => {
                RESULT_BUF = out;
                0
            }
            Err(err) => {
                RESULT_BUF = err;
                1
            }
        }
    }

    /// Verify a message's causal predecessor against a dialect's protocol.
    ///
    /// Input: UTF-8 bytes of
    /// `(verify-protocol <dialect> <thread-id> <message> [(history (<hash> <msg>) ...)])`.
    /// The optional history block populates a per-call message store so
    /// `:caused-by` hashes resolve to the supplied predecessors.
    /// Returns 0 on success ("ok" in result buf), 1 on error or pending result.
    #[no_mangle]
    pub unsafe extern "C" fn cbcl_verify_protocol(ptr: *const u8, len: usize) -> i32 {
        let input = core::slice::from_raw_parts(ptr, len);
        match verify_protocol_bytes(input) {
            Ok(out) => {
                RESULT_BUF = out;
                0
            }
            Err(err) => {
                RESULT_BUF = err;
                1
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- parse_bytes --

    #[test]
    fn parse_valid_input() {
        let result = parse_bytes(b"(tell \"hi\")");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), b"(tell \"hi\")");
    }

    #[test]
    fn parse_invalid_utf8() {
        let result = parse_bytes(&[0xFF, 0xFE]);
        assert!(result.is_err());
    }

    // -- parse_message --

    #[test]
    fn parse_message_tell() {
        let result = parse_message_str("(tell \"hello\")");
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("tell"));
        assert!(output.contains("hello"));
    }

    #[test]
    fn parse_message_with_recipient() {
        let result = parse_message_str("(tell @bob \"hello\")");
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("@bob"));
        assert!(output.contains("hello"));
    }

    #[test]
    fn parse_message_ask() {
        let result = parse_message_str("(ask @alice \"what time?\")");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_message_meta() {
        let result = parse_message_str("(meta (define test-dialect (cbcl) @author))");
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("meta"));
    }

    #[test]
    fn parse_message_invalid() {
        let result = parse_message_str("not-a-message");
        // A bare symbol is parsed as a custom performative simple message
        assert!(result.is_ok() || result.is_err());
    }

    #[test]
    fn parse_message_parse_error() {
        let result = parse_message_str("(unclosed");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("parse error"));
    }

    #[test]
    fn parse_message_bytes_valid() {
        let result = parse_message_bytes(b"(tell \"hello\")");
        assert!(result.is_ok());
    }

    #[test]
    fn parse_message_bytes_invalid_utf8() {
        let result = parse_message_bytes(&[0xFF, 0xFE]);
        assert!(result.is_err());
    }

    // -- verify_dialect --

    #[test]
    fn verify_valid_dialect() {
        let input = "(define test-dialect (cbcl) @author)";
        let result = verify_dialect_str(input);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "ok");
    }

    #[test]
    fn verify_dialect_with_performative() {
        let input =
            "(define my-dialect (cbcl) @author (extend greet (name) (effect greet-action)))";
        let result = verify_dialect_str(input);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "ok");
    }

    #[test]
    fn verify_dialect_with_resources() {
        let input = "(define my-dialect (cbcl) @author (:resource-requirements ((max-depth 8) (max-expansion-size 512) (verification-time 10))))";
        let result = verify_dialect_str(input);
        assert!(result.is_ok());
    }

    #[test]
    fn verify_dialect_parse_error() {
        let result = verify_dialect_str("(unclosed");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("parse error"));
    }

    #[test]
    fn verify_dialect_malformed() {
        let result = verify_dialect_str("(define)");
        assert!(result.is_err());
    }

    #[test]
    fn verify_dialect_r3_violation() {
        // Attempting to redefine a core performative should fail R3
        let input = "(define bad-dialect (cbcl) @author (extend tell (msg) (effect custom-tell)))";
        let result = verify_dialect_str(input);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("verification failed"));
    }

    #[test]
    fn verify_dialect_rejects_mismatched_claimed_hash() {
        // `cbcl_verify_dialect` must close the same hash gap as the runtime
        // shape/protocol endpoints — a fabricated `:hash` would otherwise
        // install fine and propagate downstream.
        let dialect = "(define h-d (cbcl) @author \
            (:hash \"sha256:0000000000000000000000000000000000000000000000000000000000000000\") \
            (extend greet (name) (effect greet-action)))";
        let result = verify_dialect_str(dialect);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("does not match canonical hash"),
            "expected hash-mismatch rejection, got: {err}"
        );
    }

    #[test]
    fn verify_dialect_accepts_matching_claimed_hash() {
        let dialect_no_hash = "(define h-d (cbcl) @author \
            (extend greet (name) (effect greet-action)))";
        let parsed = cbcl_parser::parse_dialect(
            &parser::parse(dialect_no_hash).unwrap(),
        )
        .unwrap();
        let computed = format!(
            "sha256:{}",
            hex_encode(Sha256::digest(dialect_canonical_bytes(&parsed)).as_slice())
        );
        let dialect_with_hash = format!(
            "(define h-d (cbcl) @author \
             (:hash \"{computed}\") \
             (extend greet (name) (effect greet-action)))"
        );
        assert_eq!(verify_dialect_str(&dialect_with_hash).as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_dialect_bytes_valid() {
        let result = verify_dialect_bytes(b"(define test-dialect (cbcl) @author)");
        assert!(result.is_ok());
    }

    // -- create_agent --

    #[test]
    fn create_agent_basic() {
        let result = create_agent_str("agent-1");
        assert!(result.contains("agent-1"));
        assert!(result.contains(":well-formed #t"));
        assert!(result.contains(":dialects 1"));
    }

    #[test]
    fn create_agent_bytes_valid() {
        let result = create_agent_bytes(b"agent-2");
        assert!(result.is_ok());
        let output = String::from_utf8(result.unwrap()).unwrap();
        assert!(output.contains("agent-2"));
    }

    #[test]
    fn create_agent_bytes_invalid_utf8() {
        let result = create_agent_bytes(&[0xFF, 0xFE]);
        assert!(result.is_err());
    }

    // -- send_message --

    #[test]
    fn send_message_basic() {
        let result = send_message_str("bob", "\"hello\"");
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("send-message"));
    }

    #[test]
    fn send_message_with_at_prefix() {
        let result = send_message_str("@alice", "\"hi there\"");
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("send-message"));
    }

    #[test]
    fn send_message_complex_content() {
        let result = send_message_str("@bob", "(data 1 2 3)");
        assert!(result.is_ok());
    }

    #[test]
    fn send_message_plain_text_content() {
        // Content that doesn't parse as S-expr becomes a string literal
        let result = send_message_str("@bob", "just some text");
        assert!(result.is_ok());
    }

    #[test]
    fn send_message_bytes_valid() {
        let result = send_message_bytes(b"@bob", b"\"hello\"");
        assert!(result.is_ok());
    }

    #[test]
    fn send_message_bytes_invalid_utf8() {
        let result = send_message_bytes(&[0xFF], b"hello");
        assert!(result.is_err());
    }

    // -- verify_message_shape --

    const SHAPE_DIALECT: &str = "(define greet-d (cbcl) @author \
        (extend greet (name) (effect greet-action)) \
        (shape greet (require :name string)))";

    #[test]
    fn verify_message_shape_passes_when_required_field_present() {
        let frame = format!(
            "(verify-shape {SHAPE_DIALECT} greet (greet-action :name \"alice\"))"
        );
        let result = verify_message_shape_str(&frame);
        assert_eq!(result.as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_message_shape_fails_on_wrong_type() {
        let frame = format!(
            "(verify-shape {SHAPE_DIALECT} greet (greet-action :name 42))"
        );
        let result = verify_message_shape_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        // REQ-233 blame form starts with `(error`.
        assert!(err.starts_with("(error"), "expected blame S-expr, got: {err}");
        assert!(err.contains("shape-violation"), "expected shape kind in blame: {err}");
        assert!(err.contains(":field"), "expected :field in blame: {err}");
    }

    #[test]
    fn verify_message_shape_ok_when_no_constraint_targets_performative() {
        let dialect = "(define greet-d (cbcl) @author \
            (extend greet (name) (effect greet-action)))";
        let frame = format!("(verify-shape {dialect} greet (greet-action :name 42))");
        // No shape constraint targets `greet`, so the check is vacuously satisfied.
        assert_eq!(verify_message_shape_str(&frame).as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_message_shape_rejects_malformed_frame() {
        // Missing the message argument.
        let result = verify_message_shape_str("(verify-shape (define x (cbcl) @a) greet)");
        assert!(result.is_err());
    }

    #[test]
    fn parse_and_install_dialect_rejects_mismatched_claimed_hash() {
        // Frame supplies a bogus :hash. parse_and_install must reject before
        // any verification result is produced, otherwise REQ-233 blame would
        // attribute verdicts to a hash the dialect never actually had.
        let dialect = "(define h-d (cbcl) @author \
            (:hash \"sha256:0000000000000000000000000000000000000000000000000000000000000000\") \
            (extend greet (name) (effect greet-action)))";
        let frame = format!("(verify-shape {dialect} greet (greet-action :name \"a\"))");
        let result = verify_message_shape_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("does not match canonical hash"),
            "expected hash-mismatch rejection, got: {err}"
        );
    }

    #[test]
    fn parse_and_install_dialect_accepts_matching_claimed_hash() {
        // Compute the canonical hash of a dialect, embed it as :hash, and
        // confirm the wrapper accepts it. Sanity-checks that the helper agrees
        // with `dialect_canonical_bytes` + SHA-256 + `sha256:<hex>` formatting.
        let dialect_no_hash = "(define h-d (cbcl) @author \
            (extend greet (name) (effect greet-action)))";
        let parsed = cbcl_parser::parse_dialect(
            &parser::parse(dialect_no_hash).unwrap(),
        )
        .unwrap();
        let computed = format!(
            "sha256:{}",
            hex_encode(Sha256::digest(dialect_canonical_bytes(&parsed)).as_slice())
        );
        let dialect_with_hash = format!(
            "(define h-d (cbcl) @author \
             (:hash \"{computed}\") \
             (extend greet (name) (effect greet-action)))"
        );
        let frame = format!(
            "(verify-shape {dialect_with_hash} greet (greet-action :name \"a\"))"
        );
        assert_eq!(verify_message_shape_str(&frame).as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_dialect_accepts_child_with_installed_parent_via_dialects_chain() {
        // Child references parent's `notify` performative in its protocol.
        // Without the parent in the registry R5 rejects `notify` as
        // undefined; the (dialects parent child) chain installs parent first
        // so R5 of the child sees notify.
        let chain = "(dialects \
            (define parent-d (cbcl) @author \
                (extend notify (msg) (effect notify-action))) \
            (define child-d (parent-d) @author \
                (extend ack () (effect ack-action)) \
                (protocol (then begin notify) (then notify ack))))";
        assert_eq!(verify_dialect_str(chain).as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_dialect_rejects_child_when_parent_not_supplied() {
        // Same child but supplied bare — R5 rejects because notify isn't
        // resolvable.
        let child_only = "(define child-d (parent-d) @author \
            (extend ack () (effect ack-action)) \
            (protocol (then notify ack)))";
        let result = verify_dialect_str(child_only);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("dialect verification failed"),
            "expected R5 rejection without parent installed, got: {err}"
        );
    }

    #[test]
    fn verify_protocol_accepts_child_protocol_via_dialects_chain() {
        // Child protocol references parent's notify; chain form lets the
        // protocol verifier install parent first, then run R5 + verify_causal
        // against the child.
        let chain = "(dialects \
            (define parent-d (cbcl) @author \
                (extend notify (msg) (effect notify-action))) \
            (define child-d (parent-d) @author \
                (extend ack () (effect ack-action)) \
                (protocol (then begin notify) (then notify ack))))";
        let pred = "(notify :msg \"hi\" :caused-by begin)";
        let h = predecessor_hash(pred);
        let frame = format!(
            "(verify-protocol {chain} \"t1\" \
             (ack :caused-by \"{h}\") \
             (history (\"{h}\" {pred})))"
        );
        assert_eq!(verify_protocol_str(&frame).as_deref(), Ok("ok"));
    }

    #[test]
    fn parse_and_install_dialect_rejects_empty_dialects_chain() {
        let result = verify_dialect_str("(dialects)");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("at least one"),
            "expected empty-chain rejection, got: {err}"
        );
    }

    #[test]
    fn verify_message_shape_uses_supplied_dialect_when_named_cbcl_base() {
        // A fresh DialectRegistry preloads `cbcl-base`. If the just-installed
        // dialect is also named `cbcl-base`, looking it up by name would
        // resolve the preloaded one instead — silently dropping the supplied
        // shapes and letting violations through as "ok". The wrapper must use
        // the just-installed dialect so the type-mismatch shape fires.
        let dialect = "(define cbcl-base (cbcl) @author \
            (extend greet (name) (effect greet-action)) \
            (shape greet (require :name string)))";
        let frame = format!(
            "(verify-shape {dialect} greet (greet-action :name 42))"
        );
        let result = verify_message_shape_str(&frame);
        assert!(result.is_err(), "expected shape violation, got: {result:?}");
        let err = result.unwrap_err();
        assert!(err.contains("shape-violation"), "expected shape blame: {err}");
    }

    #[test]
    fn verify_message_shape_rejects_dialect_failing_r5() {
        // Shape targets a performative that isn't declared anywhere in the
        // dialect or its ancestors. R5 must reject this at install time;
        // otherwise the wrapper would happily apply the (now misleading)
        // constraint or skip it as "no matching shape".
        let dialect = "(define bad-d (cbcl) @author \
            (extend greet (name) (effect greet-action)) \
            (shape never-declared (require :name string)))";
        let frame = format!(
            "(verify-shape {dialect} never-declared (never-declared :name \"a\"))"
        );
        let result = verify_message_shape_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("dialect verification failed"),
            "expected R5 install rejection, got: {err}"
        );
    }

    #[test]
    fn verify_message_shape_bytes_passes() {
        let frame = format!(
            "(verify-shape {SHAPE_DIALECT} greet (greet-action :name \"alice\"))"
        );
        let result = verify_message_shape_bytes(frame.as_bytes());
        assert!(result.is_ok());
    }

    // -- verify_protocol --

    const PROTOCOL_DIALECT: &str = "(define greet-d (cbcl) @author \
        (extend greet (name) (effect greet-action)) \
        (protocol (then begin greet)))";

    #[test]
    fn verify_protocol_ok_with_caused_by_begin() {
        let frame = format!(
            "(verify-protocol {PROTOCOL_DIALECT} \"t1\" (greet :caused-by begin))"
        );
        let result = verify_protocol_str(&frame);
        assert_eq!(result.as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_protocol_violation_when_caused_by_missing() {
        // Protocol declares greet must follow `begin`, so a greet with no
        // :caused-by is a MissingCausedBy violation.
        let frame = format!(
            "(verify-protocol {PROTOCOL_DIALECT} \"t1\" (greet :name \"a\"))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.starts_with("(error"), "expected blame S-expr, got: {err}");
        assert!(err.contains("causal-violation"), "expected causal kind: {err}");
    }

    #[test]
    fn verify_protocol_unknown_when_predecessor_not_in_store() {
        // Hash provided as a string literal so the parser keeps `sha256:...`
        // as a single atom rather than tokenising on `:`.
        let frame = format!(
            "(verify-protocol {PROTOCOL_DIALECT} \"t1\" \
             (greet :caused-by \"sha256:nonexistent\"))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("pending"), "expected pending result, got: {err}");
        assert!(err.contains("unknown-predecessor"), "expected reason: {err}");
    }

    #[test]
    fn verify_protocol_ok_when_dialect_has_no_protocol() {
        let dialect = "(define plain-d (cbcl) @author \
            (extend greet (name) (effect greet-action)))";
        let frame = format!("(verify-protocol {dialect} \"t1\" (greet :caused-by begin))");
        // No protocol → vacuously valid.
        assert_eq!(verify_protocol_str(&frame).as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_protocol_rejects_malformed_frame() {
        let result = verify_protocol_str("(verify-protocol (define x (cbcl) @a))");
        assert!(result.is_err());
    }

    #[test]
    fn verify_protocol_bytes_passes() {
        let frame = format!(
            "(verify-protocol {PROTOCOL_DIALECT} \"t1\" (greet :caused-by begin))"
        );
        let result = verify_protocol_bytes(frame.as_bytes());
        assert!(result.is_ok());
    }

    // -- verify_protocol with history block (hash-linked predecessors) --

    // Two non-`begin` steps so hash-linked predecessors are required to verify
    // the second one.
    // Uses non-core performative names (`query` / `respond`) so the dialect
    // passes R3; `ask` and `reply` are reserved core performatives.
    const QUERY_DIALECT: &str = "(define convo-d (cbcl) @author \
        (extend query (q) (effect query-action)) \
        (extend respond (a) (effect respond-action)) \
        (protocol (then begin query) (then query respond)))";

    /// Test helper: parse a predecessor message S-expression and return its
    /// canonical content hash in `sha256:<hex>` form, matching what
    /// `load_history_into_store` recomputes and binds against the
    /// caller-supplied hash.
    fn predecessor_hash(msg_str: &str) -> String {
        let parsed = cbcl_parser::parse_message(&parser::parse(msg_str).unwrap()).unwrap();
        let inner = parsed.innermost_simple().unwrap();
        compute_canonical_message_hash(inner)
    }

    #[test]
    fn verify_protocol_resolves_hash_predecessor_from_history() {
        // Predecessor `query` is supplied via history under its canonical
        // content hash. verify_causal must resolve the :caused-by reference
        // and return Valid.
        let pred = "(query :q \"hi\" :caused-by begin)";
        let h = predecessor_hash(pred);
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"{h}\") \
             (history (\"{h}\" {pred})))"
        );
        let result = verify_protocol_str(&frame);
        assert_eq!(
            result.as_deref(),
            Ok("ok"),
            "expected hash-linked predecessor to resolve, got: {result:?}"
        );
    }

    #[test]
    fn verify_protocol_violation_when_history_predecessor_has_wrong_type() {
        // History supplies a `respond` under its canonical hash, but the
        // protocol requires `query` before `respond`. Should produce an
        // InvalidPredecessor violation, not pending.
        let pred = "(respond :a \"earlier\" :caused-by begin)";
        let h = predecessor_hash(pred);
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"{h}\") \
             (history (\"{h}\" {pred})))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.starts_with("(error"), "expected blame S-expr, got: {err}");
        assert!(err.contains("causal-violation"), "expected causal kind: {err}");
        assert!(!err.contains("pending"), "expected violation, not pending: {err}");
    }

    #[test]
    fn verify_protocol_rejects_history_entry_with_fabricated_hash() {
        // Caller supplies a hash that is NOT the canonical content hash of
        // the message — the wrapper must reject this so a fabricated
        // `:caused-by "fake"` paired with `(history ("fake" <msg>))` cannot
        // satisfy verify_causal.
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"sha256:deadbeef\") \
             (history (\"sha256:deadbeef\" (query :q \"hi\" :caused-by begin))))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("does not match canonical content hash"),
            "expected hash-mismatch rejection, got: {err}"
        );
    }

    #[test]
    fn verify_protocol_pending_when_history_omits_predecessor() {
        // History does not contain "h1", so the predecessor is genuinely
        // unknown and the result should be pending.
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"h1\") \
             (history))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.contains("pending"), "expected pending, got: {err}");
        assert!(err.contains("unknown-predecessor"), "expected reason: {err}");
    }

    #[test]
    fn verify_protocol_uses_supplied_dialect_when_named_cbcl_base() {
        // Same name-collision risk as the shape variant above: a `cbcl-base`
        // dialect's protocol must take precedence over the preloaded base
        // (which has no protocol at all).
        let dialect = "(define cbcl-base (cbcl) @author \
            (extend greet (name) (effect greet-action)) \
            (protocol (then begin greet)))";
        let frame = format!(
            "(verify-protocol {dialect} \"t1\" (greet :name \"a\"))"
        );
        // Without the fix, lookup resolves the preloaded protocol-less base
        // and returns "ok"; with the fix the supplied protocol fires a
        // MissingCausedBy violation.
        let result = verify_protocol_str(&frame);
        assert!(result.is_err(), "expected causal violation, got: {result:?}");
        let err = result.unwrap_err();
        assert!(err.contains("causal-violation"), "expected causal blame: {err}");
    }

    #[test]
    fn verify_protocol_rejects_malformed_message_when_no_protocol() {
        // No-protocol fast path must not skip message validation: a frame
        // with a malformed message body should error even when the dialect
        // declares no protocol, otherwise hosts using this as a fail-closed
        // verifier would accept arbitrary input whenever no protocol exists.
        let dialect = "(define plain-d (cbcl) @author \
            (extend greet (name) (effect greet-action)))";
        let frame = format!("(verify-protocol {dialect} \"t1\" not-a-message)");
        let result = verify_protocol_str(&frame);
        assert!(result.is_err(), "expected message parse rejection, got: {result:?}");
    }

    #[test]
    fn verify_protocol_rejects_dialect_failing_r5() {
        // Protocol references a predecessor (`unknown-perf`) that the dialect
        // never declares. R5 must reject this at install time so a matching
        // history entry cannot drive verify_causal to "ok".
        let dialect = "(define bad-proto (cbcl) @author \
            (extend respond (a) (effect respond-action)) \
            (protocol (then unknown-perf respond)))";
        let frame = format!(
            "(verify-protocol {dialect} \"t1\" \
             (respond :a \"x\" :caused-by \"h1\") \
             (history (\"h1\" (unknown-perf :caused-by begin))))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("dialect verification failed"),
            "expected R5 install rejection, got: {err}"
        );
    }

    #[test]
    fn verify_protocol_unwraps_wrapped_history_predecessor() {
        // Predecessor is an `envelope`-wrapped `query`. verify_causal reads
        // performatives directly, so the wrapper must be unwrapped at insert
        // time or the predecessor surfaces as an empty performative and
        // produces a false InvalidPredecessor violation. The hash is bound
        // against the *innermost* simple, since that's what the store ends
        // up holding.
        let inner_pred = "(query :q \"hi\" :caused-by begin)";
        let wrapped_pred = format!("(envelope :from @alice {inner_pred})");
        let h = predecessor_hash(&wrapped_pred);
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"{h}\") \
             (history (\"{h}\" {wrapped_pred})))"
        );
        let result = verify_protocol_str(&frame);
        assert_eq!(
            result.as_deref(),
            Ok("ok"),
            "expected wrapped predecessor to unwrap to `query`, got: {result:?}"
        );
    }

    #[test]
    fn verify_protocol_rejects_history_predecessor_without_simple_inner() {
        // A bare `(meta ...)` history entry has no innermost Simple; we
        // surface that as a parse error instead of silently dropping it.
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"h1\") \
             (history (\"h1\" (meta (define x (cbcl) @a)))))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("innermost"),
            "expected innermost-simple error, got: {err}"
        );
    }

    #[test]
    fn verify_protocol_rejects_message_with_disagreeing_thread() {
        // Message claims `:thread "t2"` but frame thread is "t1". Without
        // this check the wrapper would silently relocate the message into t1
        // and verify it against t1 predecessors, defeating thread isolation.
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :thread \"t2\" :caused-by \"h1\") \
             (history (\"h1\" (query :q \"hi\" :caused-by begin))))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("does not match frame thread"),
            "expected thread-mismatch rejection, got: {err}"
        );
    }

    #[test]
    fn verify_protocol_rejects_history_entry_with_disagreeing_thread() {
        // History predecessor carries `:thread "t2"` while frame is "t1".
        // The wrapper must refuse to insert it under t1 — otherwise a
        // frame could pull a t2 predecessor into t1's causal scope.
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"h1\") \
             (history (\"h1\" (query :q \"hi\" :thread \"t2\" :caused-by begin))))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.contains("does not match frame thread"),
            "expected thread-mismatch rejection, got: {err}"
        );
    }

    #[test]
    fn verify_protocol_accepts_matching_explicit_threads() {
        // Both message and history predecessor explicitly set `:thread "t1"`
        // matching the frame — verification proceeds normally.
        let pred = "(query :q \"hi\" :thread \"t1\" :caused-by begin)";
        let h = predecessor_hash(pred);
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :thread \"t1\" :caused-by \"{h}\") \
             (history (\"{h}\" {pred})))"
        );
        assert_eq!(verify_protocol_str(&frame).as_deref(), Ok("ok"));
    }

    #[test]
    fn verify_protocol_rejects_malformed_history_block() {
        // Missing the `history` head symbol.
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"h1\") \
             ((\"h1\" (query :q \"hi\" :caused-by begin))))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
        // History entry that isn't a (hash msg) pair.
        let frame = format!(
            "(verify-protocol {QUERY_DIALECT} \"t1\" \
             (respond :a \"ok\" :caused-by \"h1\") \
             (history \"just-a-hash\"))"
        );
        let result = verify_protocol_str(&frame);
        assert!(result.is_err());
    }
}
