# State language for dialect authors

Use `(state …)` inside a dialect's `(define …)` to declare observations of its
accepted acts. The [EBNF](../cbcl-grammar.ebnf) lists the concrete syntax, including
protocols, roles, shapes, and all state forms. This reference explains the state
keywords and their semantics. The parser is
[state_parser.rs](../../crates/cbcl-parser/src/state_parser.rs); installation adds
name, type, protocol, and lattice checks beyond parsing.

## A complete example

```lisp
(define approval-count (cbcl) @author
  (:roles (chair (* reviewer)))
  (extend open (to) :from chair :to reviewer (tell to))
  (extend approve (to) :from reviewer :to chair (tell to))
  (extend close (to) :from chair :to reviewer (tell to))
  (protocol (then begin open) (then open (repeat 8 approve close)))
  (state
    (reviewers (context thread roles reviewer))
    (approvals (count approve))
    (threshold enough approvals (count 3))
    (sealed-approvals (count approve))
    (freeze sealed-approvals close supersede)))
```

`approvals` counts distinct accepted acts, not distinct reviewers. Three approvals
can therefore reach `enough` without establishing a quorum of three people.
`reviewers` exposes the sealed role roster as data; the author must define the
policy relating that roster to approvals. `sealed-approvals` reads the count in
`close`'s causal cut. Only an accepted `close` from the declared chair role can
freeze it. Concurrent earliest closes fault instead of electing one by arrival.

Verify a complete dialect with:

```sh
cargo run -p cbcl-cli -- verify < approval-count.cbcl
```

## Names, arguments, and installation

In the forms below, `name` and `source` are state field names, `verb` is a declared
performative, and `:key` is a message keyword. State field and lattice names match
`[a-z][a-z0-9-]{0,47}`. Strings use quotes, integers are signed 64-bit literals,
and booleans are `#t` and `#f`. Keywords, symbols, and strings are different atom
types: `:target`, `target`, and `"target"` are not interchangeable.

Each ordinary field is `(name (rule arguments…))`. Field names must be unique.
Derived fields and thresholds reference earlier source fields; an unknown or
forward reference rejects installation. Freeze decorations apply to their source
throughout the clause, including earlier dependencies. Domain declarations apply
to every data rule selecting the named verb. Domain sources must be an opener
list field or a declared thread-role roster, and domain keys must be typed strings.
Unknown heads, wrong arities, invalid paths, and unsupported reads reject; the
installer does not guess an intended meaning.

## State rule keywords

Brackets in this table mean an optional argument, not literal CBCL brackets.
Map arguments are key, value, then clock where applicable.

| Field rule | Observation |
|---|---|
| `(initial open :key)` | Read the sole distinct accepted opener's field. No opener yields absence; competing openers fault, even if their payloads agree. |
| `(exists verb)` | Whether any eligible act of this verb exists. |
| `(count verb)` | Number of distinct eligible act addresses. |
| `(set-union verb :key)` | Distinct contributed values, without removal. |
| `(events verb :key)` | Events retaining their act identity, signer, and selected value. |
| `(values verb :key)` | Distinct surviving values after explicit supersession. Alias: `multi-value-register`. |
| `(values-per-key verb :key :value [delete-verb])` | Surviving values grouped by key, with optional observed deletion. Alias: `multi-value-map`. |
| `(lww-register verb :value :clock)` | Greatest eligible HLC/signer/address candidate. |
| `(lww-per-signer verb :value :clock)` | Greatest surviving candidate separately for each signer. |
| `(lww-map verb :key :value :clock [delete-verb])` | Greatest surviving candidate per key, with optional observed deletion. |
| `(observed-set add-verb remove-verb :key)` | Values from surviving additions; removals cite the additions they observed. |
| `(counter increment-verb decrement-verb :amount)` | Sum increments minus decrements; unrestricted arithmetic, not spending authorization. |
| `(histogram source)` | Count occurrences of values in an earlier supported map source. |
| `(sum source)` | Sum integer values in an earlier supported map source. |
| `(progress verb)` | Greatest established occurrence in the installed finite protocol, rather than the number of acts. |
| `(bounded-counter options…)` | Resource value and account budgets checked against causal evidence. See the resource options below. |
| `(context [path…])` | Read installed dialect, sealed thread, or current observation metadata. |
| `(lift verb (into lattice-name) (contribute rows…) [projection])` | Join declared finite-lattice contributions; optionally project the resulting element. |

The retired heads `last`, `latest-per-signer`, `latest-per-key`, and
`register-per-key` reject. Choose `initial`, a multi-value rule, or an explicit
`lww-*` rule. Trusted-host HLC assumptions and `:replaces` behavior are explained
in [HLC registers](../concepts/hlc-registers.md). Progress installation requires
the selected verb's protocol occurrences to be causally ordered; see
[protocol progress](../concepts/protocol-progress.md).

## Read guarantees and additional entries

Equal accepted sets under the same installed interpretation give equal
observations. This does not make every observation final as history grows.
Ordinary displayed values are snapshots unless their schema identifies a
threshold, frozen read, or immutable context projection. Inspect `state_schema`
for a field's read classification.

### Thresholds

```lisp
(threshold name source element…)
```

A threshold starts pending, then reaches an alternative, or faults. A successful
answer never changes to another successful answer or returns to pending. Later
inconsistent evidence can make it fault. The source's fault takes precedence.
Alternatives must be nonempty, distinct, correctly typed, and pairwise
incompatible: two different answers cannot both be reached without conflict.

| Element syntax | Eligible source and meaning |
|---|---|
| `#t` | `exists`: at least one eligible act exists. |
| `(count n)` | `count`: at least `n` distinct acts, with `n ≥ 0`. |
| `(member scalar)` | `set-union`, `events`, or a sealed thread-role roster: the scalar is present. |
| `(sum n)` | Numeric `events` whose writer shape requires a `nonnegative` field: sum at least `n`. |
| `(progress n)` | `progress`: established position at least `n`, with `n ≥ 0`. |
| `"element-name"` | A finite `lift`: its carrier has reached that named non-top element or something above it. |
| Integer or `#t` on a finite projection | A checked `stable` projection of uniform integer or boolean type: projected value at least the integer, or true. |

`scalar` means string, integer, or boolean. A bare `fault` is never an alternative.
For an ordinary growing count, `(count 2)` and `(count 3)` cannot be alternatives
in one read: both can hold without conflict. Signed counters, balances, removable
sets, and displayed LWW winners are not generally stable threshold sources.
A sum threshold requires the actual source's nonnegative contributions; it cannot
silently read only the credit half of a signed balance.

Rendered thresholds use `{"status":"pending"}` or
`{"element":…,"status":"reached"}`. Faults use
`{"evidence":[addresses],"reason":…,"status":"fault"}`. Unsupported resource
profiles may have empty evidence; an empty list does not turn a fault into pending.

### Freezes

```lisp
(freeze source verb)             ; default policy: supersede
(freeze source verb supersede)
(freeze source verb fault)
```

The verb must have an explicit `:from` role. Before a freezer arrives, the source
is an ordinary observation. The earliest accepted freezer selects the exact
causal cut, including itself. Causally later freezers do not replace it;
concurrent earliest freezers fault with their evidence.

Contributions outside the cut are excluded and recorded under `supersede`, or
produce a terminal fault under `fault`. Freezing does not reject otherwise valid
acts from protocol admission. Frozen output carries `frozen` (the freezer
address), `superseded` (excluded contributors), and `value`. Derived functions
consume the frozen value. Thresholds over factored sources test the current raw
carrier after checking source errors; installation rejects a threshold on a
`supersede`-frozen source. Use separate fields, as in the example, or a `fault`
freeze where appropriate.

### Domains

```lisp
(allowed (initial open :targets))
(domain approve :target allowed)
```

Only acts whose `:target` belongs to the declared list contribute to data rules
selecting `approve`. This filters observations, not acceptance. A conflicting
initializer faults dependent observations; it does not silently erase their
history. A domain can instead reference a field declared as
`(context thread roles role-name)`. Progress and resource validators retain the
accepted causal history rather than hiding dependencies with data filters.

## Context paths

All path segments are unquoted symbols. `(context)` returns the complete map;
`(context dialect)`, `(context thread)`, and `(context observation)` return its
three submaps. Supported deeper paths are:

| Prefix | Supported remainder | Meaning |
|---|---|---|
| `dialect` | `name`, `address`, `body-address`, `author` | Installed identity metadata. |
| `dialect` | `roles` or `roles role-name` | Declared roles and their singleton/indexed cardinality. |
| `dialect` | `bounds` or `bounds max-fields|max-list|max-number|max-string` | Installed state bounds; choose one bound name as a path segment. |
| `thread` | `id`, `root`, `initiator`, `opener` | Sealed thread identity and the accepted opener address when available. |
| `thread` | `roles` or `roles role-name` | Authenticated sealed account rosters. |
| `observation` | `accepted-count`, `frontier` | Current accepted-history size and unreferenced accepted addresses. |

Nested role paths must name a declared role. Missing thread evidence can leave
values absent; malformed casts, conflicting roots, mixed-thread histories, or
conflicting relevant openers fault the affected projections. Fault scope follows
the requested path: reading a role roster does not depend on opener uniqueness.
Dialect projections and supported sealed thread leaf paths are contextual;
whole context/thread maps and observation paths are snapshots. The map contains
no built-in quorum formula, authorization override, clock, or mutable host state.

## Finite lattices and contribution tables

The author supplies finite data tables, not executable merge code:

```lisp
(lattice phase
  (elements empty ready conflict)
  (bottom empty)
  (top conflict)
  (join
    (empty empty empty) (empty ready ready) (empty conflict conflict)
    (ready empty ready) (ready ready ready) (ready conflict conflict)
    (conflict empty conflict) (conflict ready conflict) (conflict conflict conflict)))
(stage (lift mark (into phase)
  (contribute (:phase "ready" ready))
  (project stable ((empty 0) (ready 1) (conflict 2)))))
(threshold ready-now stage "ready")
```

These entries belong inside `(state …)` and require a declared `mark` with a
shaped `:phase` field. `elements`, `bottom`, `top`, and `join` occur in that order.
Every ordered element pair needs exactly one join row. Installation checks
closure, distinct bottom/top, identity/absorption, associativity, commutativity,
and idempotence. The carrier is limited to 64 elements and the installed
`max-list` bound.

Every matching `contribute` row joins its element; rows are not first-match
branches. A nonmatching act contributes bottom. A `project` table maps every
element exactly once to a string, integer, or boolean; without it the display is
the element's name. `stable` additionally checks an order-preserving projection
into integers or booleans. It enables corresponding scalar thresholds but does
not make every displayed value final. Top always produces a fault.

## Resource options and bounds

`bounded-counter` accepts the following option lists in any order. Unknown or
duplicate options reject installation.

| Option | Meaning |
|---|---|
| `(floor n)` | Required lower bound. |
| `(initial-rights open :allocations)` | Required account allocations from the opener. |
| `(issuers role)` or `(issuers ())` | Required minting role, or disable issuance. |
| `(increment verb :amount)` | Required increment operation. |
| `(decrement verb :amount)` | Required decrement operation. |
| `(transfer verb :recipient :amount)` | Required account-rights transfer. |
| `(ceiling n)` and `(initial-headroom open :space)` | Optional upper bound and matching account headroom; supplied together in account mode. |
| `(transfer-headroom verb :recipient :amount)` | Optional headroom transfer; requires a ceiling. |
| `(ownership account)` | Default account ownership mode. |
| `(ownership collective)` and `(initial open :amount)` | Collective scalar initialization; requires quorum-budget and forbids account allocation/transfer options. |
| `(certification host-gate)` | Default host issuance-gate profile. |
| `(certification quorum-budget (validators key…) (faults f))` | Explicit certificate-runtime profile. |

Collective and quorum-budget profiles need the certificate runtime; plain `fold`
does not establish their finality. See [bounded counters](../concepts/bounded-counter.md),
[example coin](../concepts/example-coin.md), and the
[quorum runtime reference](quorum-runtime.md) for authority, message fields,
certification, and recovery contracts.

The separate dialect clause `(:state-bounds (max-string n) (max-list n)
(max-number n) (max-fields n))` sets positive bounds. Options may be omitted to
use defaults; unknown or duplicate bounds reject.

## Contracts and implementation status

[SPEC-019](../../specs/SPEC-019-state-rules.md) defines the base state contract;
[SPEC-035](../../specs/SPEC-035-register-semantics.md) covers HLC registers;
[SPEC-038](../../specs/SPEC-038-lvar-state-kernel.md) covers the LVar extensions.
SPEC-038 remains draft: implemented syntax and executable checks do not imply
that every concrete Rust source binding has a completed universal refinement
proof. See the [Lean proof status](../../lean-cbcl/README.md#lvar-state-kernel).
