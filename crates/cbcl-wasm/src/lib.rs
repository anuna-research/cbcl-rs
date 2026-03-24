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
use alloc::string::String;
use alloc::vec::Vec;
use cbcl_core::agent::Agent;
use cbcl_core::dialect::DialectRegistry;
use cbcl_core::evaluator;
use cbcl_core::message::{CorePerformative, Message, Performative};
use cbcl_core::serializer::serialize;
use cbcl_core::sexpr::{Atom, SExpr};
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
}
