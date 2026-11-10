# Checkpoint summary wire format, version 2

This describes `Summary::encode`/`decode_for` and their nested resume records.
Certificates and offers retain their separate version-1 envelopes; their summary
payload is version 2. Version-1 summary payloads are rejected.

`u32`, `u64` and `i128` use big-endian bytes; signed integers use two's complement.
`bytes(x)` is a `u32` byte length followed by exactly those bytes. `string` is
`bytes(UTF-8)`. `vector(T)` is a `u32` count followed by that many `T` records.
`hash` is exactly 32 bytes. Counts and lengths are checked before allocation.
`expr` means native canonical S-expression bytes in a `bytes` frame, not JSON.
`optional-expr` is `u32(0)` or `u32(1), expr`; all other tags are invalid.

## Summary

```text
u32(2), schema-hash,
global-resume: u32(0) | (u32(1), bytes(progress-record)),
vector(row)
```

The schema hash is `hash("cbcl/checkpoint/summary-schema/v2", canonical(base
dialect with the pinned state clause and causal protocol))`. The installed schema
is supplied independently; clauses and protocols are not accepted from this frame.
The summary commitment uses domain `cbcl/checkpoint/summary/v2`. The row count,
row order and expected variant must match that clause exactly.

| Row tag | Native heads | Payload after `u32(tag)` |
|---|---|---|
| 0 | initial | `vector(contribution)`, at most two |
| 1 | values, values-per-key, observed-set, lww-map, lww-per-signer | `vector(contribution), vector(pending)` |
| 2 | lww-register | `vector(contribution)`, at most one |
| 3 | exists | `u32(0)` or `u32(1)` |
| 4 | count | `u64` |
| 5 | counter | `i128` |
| 6 | set-union | `vector(expr)` |
| 7 | events | `vector(event)` |
| 8 | histogram, sum | empty; source is an earlier schema field |
| 9 | progress | `bytes(progress-record)` |
| 10 | bounded-counter | `bytes(resource-record)` |

A contribution is `string(id), string(signer), optional-expr(key),
optional-expr(value), optional-expr(clock)`. A present clock is a canonical string
expression. An event is `string(id), string(signer), expr(selected-value)`;
it contains no message body, signature, causal header or unrelated field.
A pending reference is `bytes(scope), string(target)`; scope is empty for the
unscoped case or the canonical selected scope expression.

Contribution/event IDs use `f1220<64 lowercase hexadecimal characters>` and are
strictly increasing. Pending records sort by their complete encoded bytes.
Set-union values sort by canonical expression bytes. Duplicate entries and
noncanonical expressions are invalid. Only rule-read contribution fields may be
present, with rule-specific scope, HLC and pending-reference checks.

The complete summary is limited to 16 MiB, 1,024 rows and 65,536 entries per
unbounded row. Individual expressions are limited to 256 KiB. Sender strings are
limited to 4,096 bytes. Recognition additionally validates native canonical
syntax and closes every option/tag/length. Trailing bytes are invalid.

## Progress record

```text
u32(1), protocol-code-hash, string(verb),
presence: u32(0) | u32(1), string(root), string(thread), vector(metadata)
metadata := string(native-id), string(wire-verb), cause
cause := u32(0)                         // absent
       | u32(1)                        // begin
       | u32(2), string(parent)
       | u32(3), vector(string(parent))
```

The fields following the presence tag occur only for tag 1. Metadata IDs and
the root use `f1220<64 lowercase hexadecimal characters>`. Parent references
also accept the corresponding `f1220` state-wire spelling; the native resolver
normalizes that alias. Multi-parent lists are nonempty, sorted and unique, with
at most 256 entries. Metadata records sort by ID. Positions are recomputed from
these headers under the independently pinned protocol; ranks are never encoded.
The protocol code hash uses `cbcl/checkpoint/progress-resume/schema-v1` and the
native dialect hash of a base dialect with that protocol.

The record is limited to 16 MiB and 65,536 headers; IDs are limited to 256 bytes,
thread/verb strings to 4,096 bytes. Native identity syntax imposes a tighter ID
length. Restore verifies the causal relation and declared root. Authentication
of the cast-bearing root belongs to the enclosing context and certificate. The
global resume verb is empty; a progress row uses its declared verb. A missing
protocol yields native progress zero without retaining headers. Ordinary protocols
without repeats or progress output omit the global cache entirely.

Decoded headers alone cannot install a trusted store port. Public installation
requires the native certificate and exact summary/context binding; subsequent
client updates maintain that provenance through native admission.

## Resource record

```text
u32(1), bound: u8(0) | u8(1), [rule-hash if bound],
vector(expr(resource-fact)), vector(string(known-reference))
```

The rule hash uses `cbcl/checkpoint/resource-rule/v1` over the native canonical
list of that counter's options. Facts sort by state-wire ID and known references
sort lexicographically. A resource fact is the following exact ten-element
canonical expression list:

```text
(id verb signer identity-digest predecessors language thread from bindings fields)
```

ID, verb, signer and digest are string atoms. The digest is 64 lowercase hex
characters committing the canonical native Simple identity. Predecessors are a
list of strings. Language/thread/from/bindings are zero-or-one-element lists;
bindings, when present, contain the native cast binding list. Fields is a sorted
list of `(string-key selected-expression)` pairs, without duplicate keys.
Only that rule's data fields and escrow previous/dependency fields are allowed.
Native and state links use the same canonical multibase multihash spelling.
Malformed links remain data for the native fault classifier rather than proof queries.

The record is limited to 16 MiB, 65,536 facts and 65,536 known references, with
256 KiB per fact. Fact IDs/references are limited to 128 bytes, signer/verb strings
to 2,048 bytes, predecessor lists to 64 and selected field maps to 1,024 entries.
The native verifier recomputes the observation on recognition; cached outcomes
are not transported as authoritative values. Unbound records must be empty.
Presence tracks only needed accepted identities lacking a retained resource fact.

Resource records carry observations, not spend authority or resource finality.
Native collective/quorum legacy-fold faults remain faults. The input cut must be
an identity-consistent accepted store; raw conflicting duplicate attempts retain
the native verifier's diagnostics and are not an alternative history model.

## Canonical recognition and vectors

All three decoders must consume the frame exactly and reproduce the original
bytes on encoding. `closed_grammar_tests` constructs canonical seeds covering all
16 heads, all 11 row tags, and both nested resume formats. It mutates lengths,
tags, truncations and splices, and checks canonical roundtrips. Summary, progress
and resource unit tests also exercise duplicate/order/schema/budget rejection.
