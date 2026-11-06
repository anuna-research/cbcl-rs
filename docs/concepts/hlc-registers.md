---
title: HLC registers
mode: explanation
---

# HLC registers

[[SPEC-035-register-semantics#ADR-3503]] defines one explicit trusted-host LWW
family: `lww-register`, `lww-per-signer`, and `lww-map`. The retired `last`,
`latest-per-key`, `latest-per-signer`, and `register-per-key` heads are rejected.
Use `initial` for immutable opener fields; it never arbitrates between writers.

```lisp
(state (title (initial open :title)))
```

Installation requires the protocol's opener verb. A sole distinct raw accepted
opener supplies the field; no opener or several candidates yields Absent. Repeated
receipt of the same opener preserves its value. Missing payloads do not reduce the
candidate count. No hash winner is selected, and domains use the same raw evidence.

## Declaring clock evidence

```lisp
(shape write
  (require :item string)
  (require :value string)
  (require :clock hlc))

(state
  (announcement (lww-register write :value :clock))
  (members (lww-per-signer write :value :clock))
  (items (lww-map write :item :value :clock))
  (conflicts (multi-value-map write :item :value)))
```

`hlc` is a declared shape type, not a field-name convention. It works with any
keyword and in required, optional or nested shapes. Normal shape validation owns
canonical recognition. LWW rules require a top-level required `hlc` field; plain
`string` is rejected for that clock reference. JSON/JavaScript declares
`fields: { clock: 'hlc' }`. Schema and read-back retain that type.

Each write supplies a canonical string such as
`"hlc-000001a3185c5000-00000000"`. Physical milliseconds occupy unsigned 64-bit
lowercase hexadecimal; the logical component occupies unsigned 32-bit lowercase
hexadecimal. Widths and leading zeroes are fixed. Admission rejects missing or
malformed clock strings without consulting the current time or other state.

`lww-register` chooses across all admitted writes of its verb. `lww-per-signer`
first removes explicitly superseded own writes and chooses within each signer's
surviving candidates. `lww-map` performs keyed replacement, then chooses per key.
Its optional final argument names a delete verb with the existing observed-delete
contract: the delete names observed candidates and carries no clock; an unnamed
concurrent write survives. Timestamp ties use signer bytes, then content address.
These tie-breakers establish reproducibility, not fairness.

## Generating timestamps in the host

The pure Rust helper `cbcl_core::hlc::Hlc` parses/renders evidence and advances a
clock from explicit inputs:

```rust
use cbcl_core::hlc::Hlc;

// Load the previous HLC from host-owned durable storage.
let previous = Hlc::new(1_800_000_000_000, 4);
// The host supplies wall time and optional received HLC evidence.
let received = Hlc::new(1_800_000_000_000, 9);
let next = previous.advance(1_799_999_999_999, Some(received))
    .expect("logical overflow refuses issuance");
let field_value = next.render();
```

The host durably retains the result before issuing a write and merges relevant
received timestamps before later writes. Multiple devices sharing a signer need
an issuance policy; this library is not a cross-device clock service. Neither
`intend` nor `fold` reads a clock. The clock field remains explicit caller data.

JavaScript authoring uses `c.lwwRegister(verb, value, clock)`,
`c.lwwPerSigner(verb, value, clock)` and
`c.lwwMap(verb, key, value, clock, deleteVerb?)`. Pass the host's timestamp string
in the declared field when constructing the intent. `c.multiValueRegister` and
`c.multiValueMap` provide conflict-preserving alternatives without clock evidence.
These aliases describe back as `values` and `valuesPerKey`, their canonical forms.

## What the assumptions mean

Clock shape recognition does not authenticate time. An authorized malicious sender
can use a far-future timestamp to dominate a last-writer-wins register. Approximate
recency and causal-order claims assume correct clock generation/update. Protocol
roles still determine permitted senders; a timestamp supplies no overwrite authority.
If silently choosing among concurrent writes is unsuitable, use the multi-value
rules and an explicit resolution policy instead.

[[SPEC-025-consensus-free-refinement]] has separate resource-certification premises.
An HLC is not a resource authorization or finality certificate.

Changing an earlier LWW clock declaration from `string` to `hlc` changes the
dialect identity. The serialized timestamp value is unchanged.

The model in `LeanCbcl/HlcRegister.lean` proves greatest-candidate arbitration,
set invariance and composition with signer/keyed candidate selection over typed
clock evidence. Whole-clause correctness and conditional SEC are mechanised in SPEC-036/037.
Clock honesty, wire/Rust correspondence and resource classification remain separate. Evidence is
[[register-semantics-implementation-review]].

## Compatibility

The state specification and corpus are version 4.0.0. Retired definitions do not
install; no legacy interpreter is bundled. Pin old histories to their old runtime,
or explicitly migrate to a new definition and instance. The new `initial` head
changes definition identity. Surviving unchanged rule bodies keep canonical form
version 5. Multi-value aliases canonicalize to `values` and `values-per-key`.
The JSON authoring contract stays version 3 but rejects retired operation names.
