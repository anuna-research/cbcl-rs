State observations (SPEC-038): `state_schema` marks current field values with
`"observation":"snapshot"`. An external effect fired on a snapshot has no
finality guarantee from the kernel. Use a reached threshold to establish a
stable successful fact, or wait for the declared freeze and inspect the folded
`{frozen, superseded, value}` result for its exact causal cut. A `freeze` entry
in the schema describes that capability; before the freezer arrives the value
is still a snapshot. Thresholds and frozen reads can report a terminal fault;
handle its evidence explicitly. The host remains responsible for effect
idempotency, delivery and any external transaction or finality policy.

`recipient_of(text)` returns the canonical signed-frame audience with `@` retained,
using the shared core rule also exposed by `cbcl_erl:recipient_of/1`. It descends
message wrappers and honors an outer envelope's symbol `:to` for role routing.
Recipient-less terminals, meta/teach operations without a message recipient,
ambiguous envelope recipients, and multicast without an envelope return errors.
No dialect installation or declaration order is needed.
`recipient_of_lax(text)` additionally recognizes bare custom host control verbs;
the host remains responsible for authorizing those verbs.

Both accessors enforce the current message grammar. A wrapper body must be its
final item, and a keyword value cannot serve as the body. Legacy frames carrying
proof fields after the body are rejected, rather than routed from a partially
parsed frame. `test-vectors/frame-rooms.json` preserves legacy hub answers in
`room` and explicitly records these stricter results in `parserRoom`.
