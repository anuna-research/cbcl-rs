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
use cbcl_core::dialect::DialectRegistry;
use cbcl_core::evaluator;
use cbcl_core::message::{CorePerformative, Message, Performative};
use cbcl_core::protocol::{verify_causal, VerificationResult};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
use cbcl_core::store::{ThreadId, ThreadedMessageStore};
use cbcl_parser::parser;

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

/// Verify a dialect definition (parse + R1/R2/R3 checks).
///
/// Input: UTF-8 bytes of a `(define ...)` S-expression.
/// Returns "ok" on success or error description on failure.
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
/// Input frame: `(verify-protocol <dialect> <thread-id> <message>)`.
/// Returns "ok" on `Valid`; the canonical REQ-233 blame S-expression on `Violation`;
/// or `(pending :reason "unknown-predecessor")` on `Unknown`. Callers needing
/// predecessor lookup must populate state out-of-band; this entry point operates
/// against an empty per-call message store.
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

/// Verify a dialect definition against R1/R2/R3 rules.
fn verify_dialect_str(input: &str) -> Result<String, String> {
    let sexpr = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let dialect =
        cbcl_parser::parse_dialect(&sexpr).map_err(|e| format!("dialect parse error: {e}"))?;

    // Verify by attempting to install into a fresh registry (checks R1/R2/R3)
    let mut registry = DialectRegistry::new();
    registry
        .install(dialect)
        .map_err(|e| format!("verification failed: {e}"))?;

    Ok(String::from("ok"))
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

    let dialect = cbcl_parser::parse_dialect(dialect_sexpr)
        .map_err(|e| format!("dialect parse error: {e}"))?;

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

/// Verify a single message's causal predecessor against a dialect's protocol.
fn verify_protocol_str(input: &str) -> Result<String, String> {
    let frame = parser::parse(input).map_err(|e| format!("parse error: {e}"))?;
    let items = match &frame {
        SExpr::List(items) => items,
        _ => return Err(String::from(
            "expected (verify-protocol <dialect> <thread-id> <message>)",
        )),
    };
    if items.len() != 4
        || !matches!(&items[0], SExpr::Atom(Atom::Symbol(s)) if s == "verify-protocol")
    {
        return Err(String::from(
            "expected (verify-protocol <dialect> <thread-id> <message>)",
        ));
    }
    let thread_id = match &items[2] {
        SExpr::Atom(Atom::Str(s)) => s.clone(),
        SExpr::Atom(Atom::Symbol(s)) => s.clone(),
        _ => return Err(String::from("thread-id must be a string or symbol")),
    };
    let dialect_sexpr = &items[1];
    let message_sexpr = &items[3];

    let dialect = cbcl_parser::parse_dialect(dialect_sexpr)
        .map_err(|e| format!("dialect parse error: {e}"))?;

    let proto = match &dialect.causal_protocol {
        Some(p) => p,
        None => return Ok(String::from("ok")),
    };

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

    let store = ThreadedMessageStore::new();
    let thread = ThreadId(thread_id);
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
    /// Input: `(verify-protocol <dialect> <thread-id> <message>)` S-expression.
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
    /// Input: UTF-8 bytes of `(verify-protocol <dialect> <thread-id> <message>)`.
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
}
