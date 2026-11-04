# Fixture/semantics observations

The pinned native kernel is main c45b468, unmodified. The guest image additionally
binds the compiled wrapper and all dependencies. SDK WASM provenance is saved in
fixture-provenance.json; it must not be assumed identical to this native revision.

- SDK drawing opener text parses but omits empty content and uses a different
  keyword order than native canonical serialization. Offline fixture preparation
  uses native canonical_text before committing input. The exact changed wire
  strings are retained in fixture-canonicalization.json. Noncanonical input is
  still rejected by the guest; it does not silently normalize received bytes.
- An SDK-generated status definition's self-address did not pass the pinned
  native kernel's installation check (native-tests.log). Its repeated write trace
  also differed from native replacement generation: SDK fold counted six distinct
  messages where native intent generation produced eight distinct writes. The
  received SDK status-8 input/state are preserved separately. This experiment
  does not diagnose those differences as a kernel bug or claim the two histories
  are equivalent.
- Status fixtures are therefore regenerated using native intend and a human-named
  dialect with the same declared state operators. Their expected states are
  literal independently specified values checked by the generator. Drawing
  expected states remain the actual SDK fold output, compared byte-for-byte.
- Checklist role/cast fixture is a native authored-dialect trace; its expectation
  is a native reference result. The ancestor fixture extends an explicitly
  supplied parent definition; omission of the parent is a negative test.

These changes correct fixture identity and provenance, not proof semantics. No
production cbcl-bus code or CBCL kernel source was modified. The proof establishes
native state_exports::admit plus escrow::fold_instance computation. It does not
establish Ed25519 authentication, freshness/completeness of the chosen set, or
resource authorization for external side effects.

A later negative test changed only Record.signer while leaving the wire :from
and signed-wrapper label unchanged. Native consumer admission correctly did not
perform transport authentication: its endpoint verdict is independent of that
argument in v1, and role conformance uses wire metadata. The meaningful role
negative changes the sender metadata and matching asserted label together to an
agent outside the cast. That test passes. The record/wire authentication relation
is explicitly part of the host assumption; the experiment does not claim to prove
full signed-message validity. No guest/kernel change was made to invent a stricter
interpretation. This finding is retained in acceptance-final.log; corrected
acceptance and direct guest checks supersede that invalid test expectation.
