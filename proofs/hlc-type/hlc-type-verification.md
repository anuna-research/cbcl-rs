# Declared HLC type verification

Implements [[SPEC-035-register-semantics#ADR-3504]] and
[[SPEC-035-register-semantics#REQ-3506]] through [[IMPL-026-hlc-shape-type]].
Parent: `47ca59b`, branch `draft/state-register-semantics`, PR #20.
Date: 2026-11-06. Steward: Codex `/root`.

## Behavior and boundaries

`hlc` is a declared shape type. TypeConstraint parsing, display, canonicalization
and scalar schema preserve its name. TypeConstraint::Hlc.matches owns canonical
syntax recognition by invoking the shared Hlc parser. It accepts only strings in
the existing fixed-width wire format. Ordinary required, optional and nested shape
rules use this check independently of field name, state clauses or LWW rules.

LWW clock references must resolve to a top-level required `hlc` declaration. A plain
`string` or optional field is rejected. The R7-only shape export delegates its LWW
clock checks to the same type validator, preserving its earlier API guarantee
without a second lexical parser. JSON/JS authoring and descriptions preserve `hlc`.

Declaration compatibility remains exact; rules specifically requiring `string`
do not implicitly accept `hlc`. Values still use the string wire representation.
Changing the declared type changes the signed dialect body and identity. Corpus
message bodies, references, intent data and expected observations are unchanged;
only the relevant contract declarations change. This is within the unreleased
version-4 grammar. Canonical form stays 5 and JSON authoring stays 3.

The type guarantees syntax, not honest time, monotonic host issuance, freshness,
authority or finality. Existing typed Lean kernel/SEC statements and proofs are
unchanged. The new Rust shape recognizer is tested, not universally proved equivalent
to a Lean byte/shape decoder. Existing resource/fairness/Rust boundaries remain.

## Executed verification

Exact commands and fingerprints are in `checks.json`.

- Core/parser/FFI/Erlang tests pass, including the version-4 corpus. Existing
  ignored Erlang VM tests remain ignored. Three new Rust tests cover canonical
  strings and other atoms, arbitrary keyword names, required/optional/nested
  standalone shapes, missing data, identity, schema and authoring/read-back.
- Existing LWW installation tests now explicitly reject `string` clock declarations
  and optional clocks. Clock ordering and replacement behavior are unchanged.
- Rebuilt WASM, TypeScript checks and 27 targeted JS tests pass. The new JS test
  validates an `hlc` initializer field without any LWW rule and observes a string.
- Workspace/no-default-features checks and the unchanged Lean build pass.
- Seven isolated runtime/model mutations are rejected, including a new mutation
  accepting every string as `hlc`. Full diagnostics are in `mutations.json`.
- A structural comparison against the parent confirms every corpus message,
  reference, intent and expected observation is unchanged by this type addition.
- Formatting, diff checks, specification lint and new links/anchors are checked.
  Repository documentation retains the known unrelated dead links/older SPL errors.

The first broad test link failed for lack of disk space (errno 28). Generated
package build artifacts were cleaned; the complete Rust suite then passed with
CARGO_PROFILE_TEST_DEBUG=0, CARGO_PROFILE_DEV_DEBUG=0 and two compilation jobs.
No source or user artifacts were removed. Mutation caches remain isolated.

## Independent review

`/root/whole_kernel_spec_review` reviewed the type/shape/R7/canonical/schema/authoring
changes and new tests. It found no blockers. It requested explicit declaration
compatibility rather than implying automatic subtype coercion; the contract now
states exact compatibility. It confirmed message locality and the clock-honesty,
identity and Lean-boundary qualifications. Review was read-only, with no builds.

`/root/hlc_orientation_check` correctly recovered declared `hlc` versus string wire
values, host trust, unchanged ordering, initializer behavior and retired names.
Its minor uncertainty about who generates clocks was resolved by stating hosts
generate, advance and persist evidence. These are independent tool sessions under
one steward, not distinct cryptographic peer identities.
