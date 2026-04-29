//! SPEC-009 OBS-002 — feature-gated tracing helpers for the NIF surface.
//!
//! When the `tracing` feature is enabled, NIF wrappers wrap each call in a
//! span (`name`, `input_size`) and emit one terminal event with an `outcome`
//! field set to either `"ok"` or an error category string. When the feature
//! is disabled these helpers are zero-cost no-ops returning `()`.
//!
//! The wrappers are not used yet — the panic-guard NIF wrapping task wires
//! `parse_message` / `verify_dialect` to call `enter` / `exit_ok` / `exit_err`.

#[cfg(feature = "tracing")]
pub(crate) type SpanHandle = tracing::span::EnteredSpan;

#[cfg(not(feature = "tracing"))]
pub(crate) type SpanHandle = ();

/// Enter a span for an NIF call. Returns an opaque handle the caller must
/// pass back to [`exit_ok`] or [`exit_err`].
#[cfg(feature = "tracing")]
#[inline]
pub(crate) fn enter(name: &'static str, input_size: usize) -> SpanHandle {
    tracing::info_span!("cbcl_erl_nif", nif = name, input_size = input_size).entered()
}

#[cfg(not(feature = "tracing"))]
#[inline]
pub(crate) fn enter(_name: &'static str, _input_size: usize) -> SpanHandle {}

/// Record a successful NIF outcome and exit the span.
#[cfg(feature = "tracing")]
#[inline]
pub(crate) fn exit_ok(span: SpanHandle) {
    tracing::event!(parent: &*span, tracing::Level::INFO, outcome = "ok");
    drop(span);
}

#[cfg(not(feature = "tracing"))]
#[inline]
pub(crate) fn exit_ok(_span: SpanHandle) {}

/// Record an error outcome (using the SPEC-009 error category string) and
/// exit the span.
#[cfg(feature = "tracing")]
#[inline]
pub(crate) fn exit_err(span: SpanHandle, category: &'static str) {
    tracing::event!(
        parent: &*span,
        tracing::Level::WARN,
        outcome = "error",
        category = category
    );
    drop(span);
}

#[cfg(not(feature = "tracing"))]
#[inline]
pub(crate) fn exit_err(_span: SpanHandle, _category: &'static str) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enter_and_exit_compile_under_default_features() {
        // Smoke: with the default feature set (`tracing` off) the helpers
        // are zero-sized no-ops and must round-trip cleanly.
        let span = enter("test_nif", 42);
        exit_ok(span);

        let span = enter("test_nif", 0);
        exit_err(span, "parse_error");
    }

    // TODO: assert event content once a downstream consumer needs it
    // (would use `tracing_subscriber::fmt::test::default_collector()` or
    // `tracing-test`'s `traced_test` macro). For v0.1.0, `cargo build
    // --features tracing` is the acceptance check — see SPEC-009 OBS-002.
    #[cfg(feature = "tracing")]
    #[test]
    fn enter_and_exit_compile_with_tracing_feature() {
        let span = enter("test_nif", 7);
        exit_ok(span);
        let span = enter("test_nif", 0);
        exit_err(span, "parse_error");
    }
}
