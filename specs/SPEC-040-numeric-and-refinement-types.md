---
id: SPEC-040
title: Numeric Types and Named Flat Contracts
status: implemented
mode: reference
version: 1.0.0
last-updated: 2026-11-10
owner: CBCL maintainer
---

# Numeric Types and Named Flat Contracts

| Field | Value |
|---|---|
| ID | SPEC-040 |
| Title | Numeric Types and Named Flat Contracts |
| Status | Implemented on PR 29; verification evidence linked below |
| Branch | feat/issue-21-numeric-types; PR 29 |
| Next actor | Maintainer: review PR 29 and the recorded verification evidence |

## Orientation

Intent: give dialect authors precise numeric names and reusable value checks without requiring them to order their declarations.
The [[SPEC-040-numeric-and-refinement-types#Vocabulary|flat contract]] model draws inspiration from [[SPEC-040-numeric-and-refinement-types#Racket inspiration|Racket contracts]].
A named contract validates an existing value; it does not execute author code, construct a new wire value, or coerce representations.
Enumerations admit explicit scalar values using canonical identity, preserving distinctions between numeric representations.
Length bounds constrain Unicode scalar counts or immediate list-element counts, with inclusive and exclusive endpoints.
Numeric refinements support inclusive and exclusive literal bounds without changing the checked representation.
Regex refinements use [[SPEC-040-numeric-and-refinement-types#RFC 9485|RFC 9485 I-Regexp]], with checking, full-string matching, and explicit resource limits.

```lisp
(type postal-code (string (matches "[0-9]{4}")))
(type quantity integer)
(shape quote (require :quantity quantity)
             (require :price number)
             (require :postcode postal-code))
```

`integer` accepts signed 64-bit integer atoms. `float` accepts finite binary64 atoms, and `decimal` accepts exact decimal atoms.
`number` accepts any of those representations without conversion; examples are integer `12`, float `12.0`, and decimal `12m`.
`postal-code` accepts `"2000"`, rejects `2000`, and rejects `"x2000y"` because matching covers the entire string.
Shapes can precede their type declarations. Installation gathers declarations and resolves references before checking any message.

Decisions: [[SPEC-040-numeric-and-refinement-types#ADR-4000]] uses flat declarative contracts;
[[SPEC-040-numeric-and-refinement-types#ADR-4001]] resolves names across the complete dialect;
[[SPEC-040-numeric-and-refinement-types#ADR-4002]] binds type semantics into signed dialects;
[[SPEC-040-numeric-and-refinement-types#ADR-4003]] adopts the documented I-Regexp language.

Load-bearing: [[SPEC-040-numeric-and-refinement-types#REQ-4000]] numeric hierarchy;
[[SPEC-040-numeric-and-refinement-types#REQ-4001]] named composition;
[[SPEC-040-numeric-and-refinement-types#REQ-4002]] declaration order;
[[SPEC-040-numeric-and-refinement-types#REQ-4003]] full-string matching;
[[SPEC-040-numeric-and-refinement-types#REQ-4005]] signed semantics.

Controls:
- [[SPEC-040-numeric-and-refinement-types#REQ-4000]] forbids coercion and fractional values in integer-only arithmetic positions.
- [[SPEC-040-numeric-and-refinement-types#REQ-4002]] rejects duplicate, unknown, shadowed, cyclic, or ill-typed definitions before installation.
- [[SPEC-040-numeric-and-refinement-types#REQ-4003]] requires checking I-Regexp recognition; compile and input budgets apply before matching.
- [[SPEC-040-numeric-and-refinement-types#REQ-4004]] prohibits author procedures, I/O, callbacks, mutable-state reads, and value rewriting.
- [[SPEC-040-numeric-and-refinement-types#REQ-4005]] prohibits using old signatures under changed type semantics.
- [[SPEC-040-numeric-and-refinement-types#REQ-4006]] rejects invalid values and defaults at their defined boundary with attributable diagnostics.

Profile: [[SPEC-040-numeric-and-refinement-types#Implementation profile]] fixes the default migration, engine, Unicode data, and resource accounting.
The implementation uses the shared core checker across native and binding surfaces. Verification evidence records core coverage and explicit depth follow-up.

Detail: [[SPEC-040-numeric-and-refinement-types#CON-4000]] defines type declarations, enumerations, length bounds, and numeric range syntax;
[[SPEC-040-numeric-and-refinement-types#CON-4001]] defines the bounded regex language;
[[SPEC-040-numeric-and-refinement-types#CON-4002]] defines installation and boundary checks.

## Context and user intent

The named failure is **a type name that obscures which values a contract permits**.
Calling only integers `number` prevents an author from requesting either a specific representation or the general numeric category.
Repeating unnamed validation in each host creates a second failure: replicas can disagree about whether a string satisfies the same declared requirement.

The user requests `integer` as a specific type, `number` as its numeric supertype, and reusable types such as regex-constrained strings.
The user also requires type declarations to work without imposing a declaration order on dialect authors.
They request the design on the numeric-types branch before custom-type implementation.

The design extends shape constraints from [[SPEC-002-structural-contracts]] and state-field typing from [[SPEC-019-state-rules]].
It preserves the distinction between shape validation and causal admission in [[SPEC-003-verification-lattice]].
It does not add executable predicates or general-purpose dialect code.

### Racket inspiration

Racket presents contracts as checks at communication boundaries and provides named predicates plus composition through `and/c` and `or/c`.
Its guide also discusses regular expressions as contracts and distinguishes ordinary value checks from higher-order monitoring.
Source links appear in [[SPEC-040-numeric-and-refinement-types#Sources]].

CBCL adopts the naming, composition, boundary checking, and diagnostic ideas.
This proposal restricts contracts to a finite declarative data language over one existing value.
It does not import Racket procedures, function contracts, wrappers, execution semantics, or its regex syntax wholesale.
A contract's failure identifies the violated promise; it does not establish that an authenticated sender is malicious.

## Vocabulary

| Term | Meaning |
|---|---|
| Representation | The existing integer, float, decimal, string, boolean, symbol, keyword, or list atom/value kind |
| Numeric category | `number`, the union of integer, float, and decimal representations |
| Flat contract | A total, pure yes/no check of one bounded existing value without delayed wrappers or callbacks |
| Named type | A dialect-local name for a flat contract; it adds no wire constructor or nominal brand |
| Refinement | A contract accepting only a subset of values accepted by its base contract |
| Base representations | The finite set of value kinds that a contract can accept, derived conservatively at installation |
| Type environment | The immutable installed map from local names to checked contract definitions |
| Full match | A regex accepts exactly the entire decoded string, including its final scalar |
| Semantics profile | A fixed identifier binding numeric meanings, contract syntax, regex rules, and deterministic interpretation |

## User paths

An author declares a postal code once and references it from several shapes.
They move declarations for readability without changing acceptance or resolving names differently.
A host authenticates a message, then applies the installed checks to each required field without running author code.
An implementer verifies that string validation gives the same answer in native Rust, WASM, and NIF consumers.

The example is a dialect fragment; the surrounding `define`, performatives, and protocol remain ordinary CBCL declarations.
The following order also works:

```lisp
(shape address (require :postcode postal-code))
(type postal-code (string (matches "[0-9]{4}")))
```

Composition is explicit and remains flat:

```lisp
(type invoice-id (string (matches "INV-[0-9]+")))
(type reference (or postal-code invoice-id))
(type local-postcode (and postal-code (string (matches "2[0-9]{3}"))))
```

`reference` accepts either complete format. `local-postcode` must satisfy both contracts.
These examples are accepted by the dialect parser and checked at installation.

## Requirements

### REQ-4000

`number` SHALL accept exactly integer, finite binary64, and exact decimal atoms while preserving their representations.
`integer`, `float`, and `decimal` SHALL each accept only their respective representations.

Counters, sums, repetition counts, resource bounds, and existing finite-lattice numeric parameters SHALL retain integer-only requirements.
A broad `number` contract SHALL NOT satisfy an integer-only declaration requirement.
A contract proven to accept only integers can satisfy that representation requirement; runtime positivity and range checks still apply.

`nonnegative` remains an explicitly documented shorthand for a nonnegative integer contract in this revision.
It does not become an unrestricted numeric representation or admit fractional atoms.

Acceptance: `12`, `12.0`, and `12m` satisfy `number`; only `12` satisfies `integer`.
Boolean `#t` satisfies neither. No check converts an accepted decimal into a float or integer.
Trace: [[SPEC-040-numeric-and-refinement-types#CON-4000]], [[SPEC-040-numeric-and-refinement-types#TEST-4000]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

### REQ-4001

A dialect SHALL support names for aliases, enumerations, length bounds, numeric range refinements, bounded string refinements, intersections, and unions under [[SPEC-040-numeric-and-refinement-types#CON-4000]].
A named type SHALL check the underlying value without adding a wire tag or changing its canonical bytes.

Acceptance: a value satisfying `postal-code` remains an ordinary string; an alias and its target accept the same bounded values.
Intersection requires every operand; union requires at least one operand. Branch order does not change successful acceptance or the required worst-case work reservation.
Trace: [[SPEC-040-numeric-and-refinement-types#CON-4000]], [[SPEC-040-numeric-and-refinement-types#TEST-4001]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

### REQ-4002

Installation SHALL resolve type references against the complete dialect declaration set before committing the installed dialect.
It SHALL reject duplicate names, built-in shadowing, unknown names, cycles, and invalid refinement domains atomically.

Acceptance: moving type or shape declarations does not change the resolved environment or validation results.
Failure leaves the registry unchanged. An unknown type SHALL NOT be reinterpreted as an optional default or unchecked value.
This requirement introduces no new ordering requirement for dialect fields or type declarations.
Trace: [[SPEC-040-numeric-and-refinement-types#CON-4002]], [[SPEC-040-numeric-and-refinement-types#TEST-4002]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

### REQ-4003

`matches` SHALL validate a decoded string under RFC 9485 syntax and semantics, as adopted in [[SPEC-040-numeric-and-refinement-types#CON-4001]].
The implementation SHALL compile each distinct installed pattern before accepting the dialect and enforce finite compilation and matching budgets.

Acceptance: `[0-9]{4}` accepts `"2000"`, rejects `"x2000y"`, and rejects `"2000\n"`.
A non-string fails its base type without invoking a string matcher.
Unsupported constructs, invalid ranges, malformed patterns, and resource exhaustion reject without permissive fallback.
Trace: [[SPEC-040-numeric-and-refinement-types#CON-4001]], [[SPEC-040-numeric-and-refinement-types#TEST-4003]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

### REQ-4004

User types SHALL NOT call author procedures, perform I/O, read mutable state, inspect other message fields, or rewrite the checked value.
Contract composition SHALL NOT introduce higher-order wrappers, recursion, implicit type conversions, or dialect expansion callbacks.

Acceptance: checking the same value under the same installed type environment gives the same answer without host capabilities.
Matching a string does not trim, normalize, decode again, or replace it.
Trace: [[SPEC-040-numeric-and-refinement-types#CON-4002]], [[SPEC-040-numeric-and-refinement-types#TEST-4004]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

### REQ-4005

Canonical signed dialect data SHALL bind the numeric and contract semantics profile and the complete declared type environment.
Changing a type name, base contract, numeric bound or comparator, enumeration member or order, length clause, regex, composition, or profile SHALL change the signed commitment.

The changed meaning of `number` SHALL NOT reuse old signatures under the old integer-only interpretation.
Compiled matcher state and caches SHALL NOT replace the source definition in the signed commitment.

Acceptance: an old signed integer-only `number` dialect fails verification under the new semantics unless explicitly reissued.
Type declaration order does not change the canonical type-environment segment; existing ordering rules for other signed clauses remain explicit.
Trace: [[SPEC-040-numeric-and-refinement-types#CON-4002]], [[SPEC-040-numeric-and-refinement-types#TEST-4005]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

### REQ-4006

The installed contract SHALL check message fields at their existing shape boundary and declared defaults before installation succeeds.
Failures SHALL identify the dialect, performative, field path, declared type, and failed rule or invalid-definition reason.

Acceptance: native, WASM, and NIF surfaces share the core result and preserve the same failure category.
Diagnostics omit raw field values by default. Domain validators do not become an independent JavaScript or host regex implementation.
Trace: [[SPEC-040-numeric-and-refinement-types#CON-4002]], [[SPEC-040-numeric-and-refinement-types#TEST-4006]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

### NFR-4000

Installation and checking SHALL have explicit finite limits for declaration count, dependency depth, expression nodes, pattern bytes, compiled states, and input bytes.
Enumeration member count and total literal bytes SHALL also have profile-fixed caps.
The signed semantics profile fixes these caps.
The installer derives a conservative worst-case work bound that includes composition and repeated references.
Equivalent operand permutations have the same reservation requirement. Host availability limits remain separate operational limits.

Compiled checks SHALL use an algorithm without input-dependent exponential backtracking.
The implementation plan SHALL ratify numeric caps and demonstrate worst-case work against the configured pattern and input limits.
Host resource exhaustion returns a distinct `resource-limit` outcome; it is neither successful acceptance nor proof of a contract violation.

Trace: [[SPEC-040-numeric-and-refinement-types#TEST-4003]], [[SPEC-040-numeric-and-refinement-types#TEST-4004]], [[SPEC-040-numeric-and-refinement-types#OBS-4000]].

## Contracts

### CON-4000

Interface: type declarations inside a dialect and type expressions in existing shape type slots.
The structural grammar uses the existing CBCL lexical productions for symbols, keywords, strings, and values.

```ebnf
type-decl   = "(" , "type" , ws , type-name , ws , type-expr , ")" ;
type-expr   = builtin | type-name
            | "(" , "one-of" , ws , scalar-literal , { ws , scalar-literal } , ")"
            | "(" , "string" , ws , string-rule , { ws , string-rule } , ")"
            | "(" , "list" , ws , length , { ws , length } , ")"
            | "(" , numeric-base , ws , bound , { ws , bound } , ")"
            | "(" , "and" , ws , type-expr , ws , type-expr ,
                { ws , type-expr } , ")"
            | "(" , "or" , ws , type-expr , ws , type-expr ,
                { ws , type-expr } , ")" ;
numeric-base = "number" | "integer" | "float" | "decimal" ;
bound       = "(" , comparator , ws , numeric-literal , ")" ;
comparator  = ">=" | ">" | "<=" | "<" ;
string-rule = matches | length ;
length      = "(" , "length" , ws , length-bound , { ws , length-bound } , ")" ;
length-bound = "(" , comparator , ws , nonnegative-integer-literal , ")" ;
matches     = "(" , "matches" , ws , string , ")" ;
builtin     = "number" | "integer" | "float" | "decimal" | "nonnegative"
            | "string" | "hlc" | "bool" | "symbol" | "keyword" | "list" ;
require     = "(" , "require" , ws , keyword , [ ws , type-expr ] ,
                { ws , child-rule } , ")" ;
optional    = "(" , "optional" , ws , keyword , [ ws , type-expr ] ,
                [ ws , default ] , { ws , child-rule } , ")" ;
default     = "(" , "default" , ws , value , ")" ;
```

`value` is the existing `expression` production; `child-rule` is `require`, `optional`, or the existing `max-depth` rule.
A user `type-name` matches `[a-z][a-z0-9-]{0,47}` and excludes built-ins and reserved expression heads.
Names are local to the declaring dialect in this initial design; no implicit registry lookup or imported type namespace is introduced.
Existing `hlc` and `nonnegative` remain named built-ins with their current narrower contracts.
`list` remains the existing structural kind; this proposal adds no recursive list-element type constructor.

Refinements are intersections with their base kind. Multiple `matches` clauses all apply to the same complete string.
Expressions using `and` or `or` have at least two operands and retain their declared diagnostic order.
An `and` whose representation sets are disjoint rejects installation; `number` intersected with `integer` remains integer-only.
No general regex-language inclusion or emptiness decision is required by this representation check.
A syntactically valid regex accepting no strings remains a legal contract that rejects every value.

Enumerations specify one or more literal scalar members:

```lisp
(type currency (one-of :AUD :USD :EUR))
(type response (one-of "yes" "no"))
```

`scalar-literal` is an existing integer, float, decimal, string, boolean, symbol, or keyword atom; lists are excluded.
Bare symbols in `one-of` member positions denote literal symbols, never type references or evaluated expressions.
Membership SHALL use canonical atom identity (the existing canonical signing encoding), including representation, rather than numeric range equality or text conversion.
Thus `(one-of 1)` rejects `1.0` and `1m`; `(one-of :AUD)` rejects string `"AUD"` and symbol `AUD`.
Installation SHALL reject empty enumerations and duplicate canonical members, including differently spelled literals that normalize identically.
The inferred representation set is the union of member representations; mixed scalar kinds are permitted explicitly.
Member order is preserved in signed source definitions; reordered members accept the same values but change the signed commitment.

Length constraints compose with other refinements:

```lisp
(type display-name (string (length (>= 1) (<= 80))))
(type short-postcode (and postal-code (string (length (<= 4)))))
(type batch (list (length (> 0) (<= 100))))
```

Every length bound SHALL use a nonnegative integer literal within the existing signed 64-bit integer range.
String length counts decoded Unicode scalar values, not UTF-8 bytes, grapheme clusters, or displayed characters.
No Unicode normalization occurs: precomposed and decomposed text can have different lengths.
List length counts immediate elements; nested lists each count as one element without recursive checking.
The base representation is checked first; neither strings nor lists are converted to the other representation.
All length clauses apply conjunctively, including when mixed with `matches` inside a string refinement.
Within each string or list refinement, installation combines its length clauses and SHALL reject an interval containing no nonnegative integer.
No general emptiness proof across named contracts, `and`, or `or` is required; their checks still compose conjunctively or disjunctively.
For example, `(length (> 0) (< 1))` and `(length (< 0))` are definition errors.
Explicit byte and input-size resource caps apply independently of semantic length bounds.
Enumeration member count, literal bytes, and length scanning SHALL be covered by profile-fixed caps and whole-check work reservation.
These clauses add neither list-element contracts nor record constructors.

Numeric refinements combine their base representation with every declared bound:

```lisp
(type percentage (number (>= 0) (<= 100)))
(type positive-count (integer (> 0)))
(type price (decimal (>= 0) (< 10000)))
```

`numeric-literal` is an existing integer, finite float, or decimal literal; expressions and references are not bounds.
Each comparator applies to the checked value and its literal bound in that order.
Bounds compare exact mathematical values across representations, without rounding either operand or rewriting the checked atom.
A float contributes its exact represented binary64 value; its printed decimal approximation does not replace that value.
For example, float `0.1` is greater than decimal `0.1m`, while integer `1`, float `1.0`, and decimal `1m` compare equal.
Signed zeros compare equal. The base contract still determines which representations are accepted.
Thus `percentage` admits integer, float, and decimal values; `price` admits only decimals, even with an integer bound.
`>=` and `<=` include their endpoints; `>` and `<` exclude them. A single bound permits an open-ended interval.
Comparisons SHALL NOT convert values to binary64 as a common intermediate representation.
Exact comparison work and temporary storage count toward the signed profile's installation and checking budgets.
The installer derives the tightest lower and upper bounds, treating an exclusive bound as tighter at an equal endpoint.
It SHALL reject reversed endpoints and equal endpoints with either endpoint excluded.
Other empty domains, such as `(integer (> 0) (< 1))`, SHALL remain valid contracts that reject every value.
These checks introduce no arithmetic expressions, step sizes, units, coercion, or cross-field comparisons.

The `default` clause makes optional defaults explicit:

```lisp
(optional :postcode postal-code (default "2000"))
```

The installer validates that default against its declared contract.
Bare symbols in a type slot are always type references, including unresolved references.
Legacy positional defaults require rewriting as explicit clauses; they cannot mask a misspelled type name.

Preconditions: the complete dialect syntax is recognized under the chosen type-system profile.
Postconditions: recognized expressions have unique structural interpretation before name resolution or pattern compilation.
Error model: unknown heads, invalid arities, reserved names, wrong argument kinds, and ambiguous defaults reject the definition.
Implements: [[SPEC-040-numeric-and-refinement-types#REQ-4000]], [[SPEC-040-numeric-and-refinement-types#REQ-4001]], [[SPEC-040-numeric-and-refinement-types#REQ-4002]].
Verified by: [[SPEC-040-numeric-and-refinement-types#TEST-4000]], [[SPEC-040-numeric-and-refinement-types#TEST-4001]], [[SPEC-040-numeric-and-refinement-types#TEST-4002]].

### CON-4001

Interface: the decoded `matches` pattern is an I-Regexp under [[SPEC-040-numeric-and-refinement-types#RFC 9485]].
Section 3 and Figure 1 supply the grammar; section 4 supplies the Boolean semantics through its normative XSD references.
CBCL adopts that documented language by reference and removes its bespoke regex EBNF.

The implementation SHALL be checking in the sense of RFC 9485 section 3.1.
It SHALL recognize the entire I-Regexp before adapting or compiling it, rejecting syntax outside that language.
Host-library acceptance alone is not sufficient evidence of I-Regexp validity.

The following distinctions matter for CBCL authors and adapters:

| Rule | Required interpretation |
|---|---|
| Input | Unicode scalar sequences, including the RFC's required character properties; no ASCII-only fallback |
| Match | The complete string, with no implicit substring search or extracted captures |
| Dot | Any scalar except LF and CR; a decoded newline is not normalized away |
| `^` and `$` | Ordinary literal characters under I-Regexp, not host-engine anchors |
| Repetition | The RFC's exact, bounded, and open-ended counted forms, subject to explicit resource limits |
| Escapes | The RFC's permitted escapes and Unicode categories; no engine-specific shorthand extension |

Backreferences, lookaround, and engine-specific flags are not accepted as additional syntax.
The RFC's grammar, including its character-class restrictions, decides recognition rather than an informal feature checklist.

CBCL string unescaping occurs once before I-Regexp recognition. Pattern source is retained for signing and diagnostics.
An author writing a regex backslash therefore escapes it in CBCL, such as `(matches "\\p{Nd}{4}")`.
The signed semantics profile fixes the Unicode property-data version used by every binding; using host-default tables is not permitted.
That version is a maintainer-owned implementation gate rather than an ambient library choice.

An adapter composes an existing regex implementation with an I-Regexp recognizer and semantic translation where needed.
RFC 9485 section 5 gives informative mapping guidance; the normative grammar and Boolean semantics remain authoritative.
The adapter SHALL preserve literal metacharacters, dot behavior, Unicode categories, and the full-input boundary.
Wrapping raw source in host anchors alone does not establish conformance.

Compiled regexes and translated host patterns are implementation artifacts. They never replace the original pattern in signed dialect data.
Runtime bindings share the core implementation; browser or NIF consumers do not independently interpret the source with host regex defaults.

CBCL retains the explicit compilation, input, and whole-check reservation limits in [[SPEC-040-numeric-and-refinement-types#NFR-4000]].
Those are resource policy, not an alternate regex dialect or permission to approximate the accepted language.
Counted repetition is admitted only within the profile's resource limits; exhaustion is distinct from malformed syntax or value mismatch.
A constrained target unable to support the required Unicode data reports unsupported capability; it does not accept a weaker ASCII contract.

Preconditions: the structural `matches` clause and CBCL string escape syntax are recognized; the signed semantics profile is supported.
Postconditions: within admitted budgets, the compiled check yields the RFC's Boolean result and preserves the original string.
Error model: invalid I-Regexp is a definition error; value mismatch is a contract violation; exhausted resources use the separate operational category.
Implements: [[SPEC-040-numeric-and-refinement-types#REQ-4003]], [[SPEC-040-numeric-and-refinement-types#REQ-4004]].
Verified by: [[SPEC-040-numeric-and-refinement-types#TEST-4003]], [[SPEC-040-numeric-and-refinement-types#TEST-4004]].

### CON-4002

Interface: installation produces an immutable type environment; message validation consumes that environment and the existing value.

Installation first collects all type declarations and shape references from the complete dialect.
It recognizes each expression, rejects duplicate and reserved names, builds the reference graph, and rejects unknown names and cycles.
It then resolves the graph, derives representation sets, validates refinement domains, and compiles patterns under explicit budgets.
Defaults pass the resolved contracts before the registry changes. Any failure discards the entire candidate installation.

Aliases retain their declared names for diagnostics. Canonical type declarations are sorted by name, independently of source declaration order.
Their definitions retain source strings and explicit composition order; compiled automata and cache layouts are excluded from signed data.
The canonical type segment binds each name and expression together, preventing changes through name rebinding.

The signed body also includes a fixed type-semantics identifier, `cbcl-flat-v1-unicode16`.
The compiler inserts this identifier; dialect authors do not supply or order it.
Its definition covers the numeric hierarchy, contract grammar, RFC 9485 semantics, pinned Unicode property data, and resource limits in this document.
The signing-form version changes, and verification binds the profile rather than relying on an informational version constant alone.
Existing development signatures and self-addressed dialect identities require reissue under this explicit format change.
Existing historical records remain available as evidence; no silent migration or permissive legacy alias is introduced.

The semantics profile fixes pattern, input, dependency, expression-size, compiled-state, enumeration-member, and literal-byte limits.
Their numeric values are ratified before implementation and bound through the signed profile identifier.
A host lacking those capabilities can refuse installation with an explicit local resource failure; it cannot silently weaken the installed contract.

The compiled environment supplies a conservative work bound for each contract over every permitted input size.
The bound includes each distinct predicate, composition node, and referenced definition, without exponential alias expansion.
Before evaluating any predicate, the checker reserves that complete bound against the caller's available work allowance.
Operand permutations have equal reservation requirements; successful short-circuiting does not bypass this reservation.
A rejected reservation returns `resource-limit` without a partial contract decision.

A pure check takes `(installed-type, value, available-work)` and returns success, structured contract violation, or `resource-limit`.
Available work is an operational allowance, not part of the predicate's meaning.
If reservation succeeds and input fits profile limits, the bound covers the entire check regardless of operand order.
Sufficiently provisioned native, WASM, and NIF checks therefore agree on success or violation for the same installed contract and value.
Profile input limits and local work exhaustion produce `resource-limit`, never a false value-mismatch or a dropped refinement.
It preserves the complete input value and performs no effectful operation.
Representation checks precede any representation-specific predicate. Composition uses bounded evaluation without recursively expanding aliases into unbounded copied trees.
Unions and intersections have ordinary Boolean semantics; a failure diagnostic chooses the first relevant operand in declared order.

The checker runs at the existing message-shape boundary and is shared by native, WASM, NIF, and other bindings.
The authoring pipeline checks the intended value against the same core contract before producing a message to sign.
Validation does not bypass authentication, role checks, causal admission, state bounds, or host effect policy.
The type schema exposes the declared name, resolved contract, and representation set, including `number` as the numeric union.

Preconditions: the semantics profile is supported and the supplied installation and value-check budgets are finite.
Postconditions: installation is atomic; a successful value check preserves bytes and representation under the signed installed definitions.
Error model: invalid definitions are installation failures; invalid values are shape violations; resource exhaustion is a separate operational result.
Implements: [[SPEC-040-numeric-and-refinement-types#REQ-4002]], [[SPEC-040-numeric-and-refinement-types#REQ-4004]], [[SPEC-040-numeric-and-refinement-types#REQ-4005]], [[SPEC-040-numeric-and-refinement-types#REQ-4006]].
Verified by: [[SPEC-040-numeric-and-refinement-types#TEST-4002]], [[SPEC-040-numeric-and-refinement-types#TEST-4004]], [[SPEC-040-numeric-and-refinement-types#TEST-4005]], [[SPEC-040-numeric-and-refinement-types#TEST-4006]].

## Decisions

### ADR-4000

Decision: use named, composable flat contracts as the user-type model.
A regex-refined string remains a string, and a numeric supertype does not convert its accepted members.

Rationale: authors need reusable constraints on exchanged data, not executable dialect extensions or higher-order function boundaries.
Racket's naming and composition concepts fit that need without importing its procedure-based extensibility.
Recursive containers and cross-field constraints remain future proposals with their own grammars.

Trade-off: initial refinements are scalar enumerations, string matching, literal numeric bounds, and string/list length bounds. Other predicate forms require a separate grammar decision.

### ADR-4001

Decision: use complete-dialect name collection followed by bounded dependency resolution at installation.

Rationale: authors can organize declarations for readability without maintaining a manual dependency order.
Forward references work; cycles and unknown names are definition failures rather than runtime surprises.
Signed type declarations use name order; ordinary unrelated dialect-clause ordering retains its existing semantics.

Trade-off: local type names require an installed environment, so the current closed enum and parser extraction paths need an implementation plan.

### ADR-4002

Decision: bind a fixed type-semantics profile into every signed dialect under the new signing-form version.

Rationale: changing `number` from integer-only to a union changes a promise even when the old source text is unchanged.
An unchanged valid signature cannot authorize both meanings implicitly.
Source pattern strings and profile identity support deterministic interpretation independently of the compiled regex representation.

Trade-off: this is a deliberate development-time compatibility break; signatures and dialect self-addresses require explicit reissue.
The implementation profile fixes the canonical segment; PR review includes updated golden vectors and an explicit identity migration fixture.

### ADR-4003

Decision: adopt RFC 9485 I-Regexp for the regex language, with mandatory checking and the resource policy in this specification.
The implementation composes an existing engine through a verified semantic adapter rather than publishing its native dialect as CBCL syntax.

Rationale: authors need a documented, portable language for Boolean validation. A bespoke regex grammar duplicates established interoperability work.
Engine syntax, Unicode tables, and default matching modes cannot silently define signed contract semantics.

Trade-off: adapters must preserve the documented language even where a host engine differs.
The implementation pins Unicode data, supplies adaptation vectors, and records budget enforcement in the linked verification evidence.

Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4003]], [[SPEC-040-numeric-and-refinement-types#CON-4001]], [[SPEC-040-numeric-and-refinement-types#TEST-4003]].

## Acceptance tests

Core acceptance is executable in `crates/cbcl-parser/tests/flat_contracts.rs` and shared native/WASM/NIF binding vectors.
The verification record links results, mutation evidence, explicit fixture migration, and depth follow-up.
Core tests use the actual parser, installer, shared checker, and binding helpers without network services.
Depth tests add adversarial pattern corpora and cross-target performance measurement.

### TEST-4000

Core: exercise each numeric representation against `integer`, `float`, `decimal`, and `number`. Reject booleans and quoted numeric strings.
Verify that acceptance preserves each atom and its canonical tag.
Reject broad `number` shapes on integer-only counters and sums; reject fractional repetition counts and bounds.
Accept aliases proven to be integer-only and retain their separate runtime range checks.
Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4000]].

### TEST-4001

Core: check named aliases, refined strings, intersections, and unions with positive and negative values.
Check singleton and mixed-kind enumerations; distinguish keywords, symbols, strings, and numeric representations.
Reject empty enumerations, list members, and duplicate members after canonical normalization.
Verify literal symbols are not type references; infer integer-only enumerations for integer-only declaration checks.
Check zero, inclusive, exclusive, and one-sided string/list lengths and combinations with regex constraints.
Count supplementary Unicode scalars once; distinguish composed and decomposed text without normalization.
Combine multiple length clauses directly and through named `and` operands; verify every bound applies.
Count a nested list as one immediate element; reject wrong base kinds and fractional or negative length bounds.
Reject impossible integer length domains; exercise enumeration-size, literal-byte, and scanning work limits.
Verify full-string behavior and unchanged canonical message bytes.
Check inclusive and exclusive numeric endpoints, one-sided bounds, negative bounds, and mixed representations.
Accept `0`, `0.0`, and `0m` as percentages; reject values below zero or above one hundred.
Reject a float under a decimal base, even when it satisfies the bounds.
Compare float `0.1` above decimal `0.1m`; compare a large integer beyond binary64 precision without rounding.
Reject nonnumeric bounds, reversed endpoints, and equal endpoints with an exclusive bound.
Exercise numeric comparison work and storage limits; preserve operational `resource-limit` outcomes.
Reject nested list contracts, executable predicates, and unknown combinator heads.
Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4001]].

### TEST-4002

Core: permute type and shape declarations and compare the installed environment, canonical type segment, and value-check results.
Reject direct and indirect cycles, unknown names, duplicates, and attempts to shadow built-ins.
Test optional-default disambiguation and assert no registry changes after a failing installation.
Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4002]].

### TEST-4003

Core: derive recognition cases from RFC 9485 Figure 1 and its additional character-class restriction.
Verify `"2000"` passes and `"x2000y"`, integer `2000`, and `"2000\n"` fail the postal-code contract.
Check open-ended repetition, escaped literals, character ranges, Unicode properties, and empty patterns.
Assert `.` rejects LF and CR but accepts a supplementary Unicode scalar.
Match pattern `^x$` against literal text `"^x$"`; reject `"x"` to detect accidental host-anchor interpretation.
Verify `\p{Nd}{4}` accepts non-ASCII decimal digits, while `[0-9]{4}` rejects them.
Reject invalid classes, unsupported shorthand, lookaround, backreferences, embedded flags, malformed escapes, and invalid repetition bounds.
Exercise compile and input budgets at their limit and just beyond it.
Run identical vectors through native, WASM, and NIF with the pinned Unicode data.
Depth: test engine adaptations against an independent I-Regexp reference and adversarial counted repetitions under agreed resource limits.
Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4003]], [[SPEC-040-numeric-and-refinement-types#NFR-4000]].

### TEST-4004

Core: repeat checks under identical installed inputs and compare outcomes while recording all effect hooks.
Assert no I/O, callbacks, mutable-state reads, field rewriting, or other-field inspection.
Exercise repeated aliases and composition under a total-work budget without exponential tree expansion.
Compare `(or expensive-string-type string)` with its operand permutation using identical values and available work.
With sufficient work, assert equal reservation requirements and successful results.
With insufficient work, assert `resource-limit` before either predicate runs.
Compare sufficiently provisioned bindings with a host that refuses local work; distinguish resource unavailability from value mismatch.
Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4004]], [[SPEC-040-numeric-and-refinement-types#NFR-4000]].

### TEST-4005

Core: mutate a name, numeric bound, comparator, regex, base, operand, or profile; verify the signed commitment changes.
Mutate enumeration members, their order, and length clauses; verify each changes the signed commitment.
Reorder declarations and verify the canonical type segment remains equal. Reorder composition and retain its specified signed diagnostic order.
Reject a signature produced for the old integer-only `number` interpretation under the new semantics.
Depth: regenerate self-addressed dialect fixtures with an explicit old/new identity map and native cross-binding golden vectors.
Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4005]].

### TEST-4006

Core: reject invalid declared defaults during installation and invalid field values at the existing message-shape boundary.
Compare native, WASM, and NIF failure categories, named types, and field paths.
Assert diagnostics omit raw values by default and validation leaves authentication and causal admission obligations intact.
Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4006]].

## Observability

### OBS-4000

Installation diagnostics record the semantics profile, type name, structural path, and definition-error category.
Message violations record the dialect, performative, field path, declared type, and failed rule without raw values by default.
Resource failures distinguish pattern compilation, input limits, dependency depth, and total check work.
Bindings expose the same core categories; no independent host validator supplies a conflicting answer.

Trace: [[SPEC-040-numeric-and-refinement-types#REQ-4000]], [[SPEC-040-numeric-and-refinement-types#REQ-4001]], [[SPEC-040-numeric-and-refinement-types#REQ-4002]], [[SPEC-040-numeric-and-refinement-types#REQ-4003]], [[SPEC-040-numeric-and-refinement-types#REQ-4004]], [[SPEC-040-numeric-and-refinement-types#REQ-4005]], [[SPEC-040-numeric-and-refinement-types#REQ-4006]].

## Implementation profile

The maintainer's implementation instruction approves the declarative design and authorizes the following concrete development choices.
The compiler inserts `cbcl-flat-v1-unicode16`; signing form 6 binds that profile on every dialect, including dialects without custom types.
Explicit `(default value)` replaces positional defaults; legacy sources require an explicit rewrite, with no ambiguous symbol fallback.
RFC recognition precedes translation into regex-syntax 0.8.11 HIR and regex-automata 0.4.14 Thompson PikeVM execution.
The pinned Unicode property tables are version 16.0.0; upgrades require a new signed profile.

| Limit | Value |
|---|---|
| Named declarations | 128 |
| Compiled expression nodes | 512 |
| Dependency and expression depth | 32 |
| Pattern UTF-8 bytes | 1024 |
| Check input storage budget | 65536 bytes, with fixed per-atom/node overhead |
| Decimal digit storage per value | 4096 bytes |
| Total literal canonical bytes | 65536 |
| Members per enumeration | 256 |
| Portable compiled NFA cost units | 262144 |
| States per compiled NFA | 16384 |
| Default local work allowance | 34359738368 units |

Portable NFA cost sums fixed-width state and transition costs, independent of native pointer sizes.
Sparse states cost 16 plus 8 per transition; dense states cost 16 plus 4 per transition.
Union states cost 16 plus 4 per alternate; fail/match states cost 16; other states cost 32.
A separate 16 MiB compiler allocation guard is operational, not the signed complexity metric.
The type schema exposes source definitions, resolved representation sets, and the complete local name environment as an acyclic contract graph.
Optional field metadata includes requiredness and default source; validators continue to use the shared core.

Whole-check reservation sums worst-case predicate costs over composition before evaluation, including repeated named references without copying their programs.
Numeric bounds reserve a conservative quadratic digit-work allowance; regex checks reserve state-count times maximum-input work.
Local callers can lower their work allowance and receive `resource-limit` without a contract verdict.
Measurements, adapter conformance vectors, signing fixture migration, and independent implementation review are acceptance evidence, not consequences of these choices.
Depth testing against a separate full I-Regexp implementation remains maintainer-owned follow-up; core independent semantic vectors are mandatory here.

## Reading paths

Reviewer: [[SPEC-040-numeric-and-refinement-types#Orientation]] → [[SPEC-040-numeric-and-refinement-types#Decisions]] → [[SPEC-040-numeric-and-refinement-types#Implementation profile]].
Implementer: [[SPEC-040-numeric-and-refinement-types#Contracts]] → [[SPEC-040-numeric-and-refinement-types#Acceptance tests]] → [[SPEC-040-numeric-and-refinement-types#Requirements]].
Stakeholder: [[SPEC-040-numeric-and-refinement-types#User paths]] → [[SPEC-040-numeric-and-refinement-types#Racket inspiration]].

## Amendment Channels

The CBCL maintainer amends this specification through a recorded type-system decision or reviewed specification revision.
Remote data, regex contents, message fields, and host callbacks cannot amend validation rules or resource budgets.
Hard stops are the representation, installation, bounded matching, purity, signed-semantics, and boundary controls in [[SPEC-040-numeric-and-refinement-types#Orientation]].
The maintainer authorized implementation after reviewing the design; the SPL ledger records acceptance dependencies.

## Sources

### RFC 9485

I-Regexp: An Interoperable Regular Expression Format. Sections 3–4 define the adopted grammar and semantics.
Section 5 gives informative engine-mapping guidance; section 8 discusses resource limits and untrusted patterns.
URL: https://www.rfc-editor.org/rfc/rfc9485.html

### Racket contracts

The Racket Guide, Contracts: the source suggested by the user.
URL: https://docs.racket-lang.org/guide/contracts.html

Contracts and Boundaries: value checks at boundaries and attribution of contract violations.
URL: https://docs.racket-lang.org/guide/contract-boundaries.html

Simple Contracts on Functions, especially Rolling Your Own Contracts: named predicates, `and/c`, `or/c`, and regular-expression contracts.
URL: https://docs.racket-lang.org/guide/contract-func.html

Building New Contracts: the distinction between flat contracts and higher-order projections.
URL: https://docs.racket-lang.org/guide/Building_New_Contracts.html

The type-declaration grammar, budgets, signed profile, and mandatory checking are CBCL choices. The regex language is the adopted I-Regexp standard.
Racket supplies contract-system inspiration; this proposal makes no assertion of Racket compatibility.

## Review status

Implementation evidence: [SPEC-040 verification](../proofs/flat-contracts/verification.md).
The initial draft passed independent comprehension and design review before implementation was authorized.
Implementation reviews covered core semantics, resource safety, schemas, grammar, and binding coverage; substantive findings were corrected.
No formal proof or full independent-engine regex equivalence claim is made.

Comprehension reviewer `type_spec_comprehension` read only the Orientation and correctly predicted the numeric, postal-code, ordering, and signature rules.
Independent reviewer `type_spec_review` identified budget-order ambiguity and unclear separation of signed limits from local resource availability.
The revision adds whole-check work reservation, profile-fixed limits, and a separate resource-limit result before a Boolean contract decision.
The reviewer re-read the revision and reported no remaining substantive objection.
That initial design review preceded the concrete implementation profile and runtime acceptance evidence.

The 0.2.0 comprehension review confirmed numeric spellings and ownership of range syntax after Orientation clarification.
Independent review checked RFC 9485 semantics and numeric ranges, resolving stale scope text, endpoint handling, and signed-bound coverage.
Empty numeric-domain installation remains deterministic; range and regex cases subsequently became executable acceptance tests.

The 0.3.0 independent review found no substantive enumeration or length issues and requested explicit multi-clause composition coverage.
Those composition cases are included in core acceptance.
The Orientation-only comprehension review confirmed enumeration identity, endpoint inclusion, length measures, and the owning syntax contract.

## Changelog

<details>
<summary>Revision history</summary>

- 1.0.0 — 2026-11-10: implement the shared contract system, pin its portable profile, migrate signing format, and record executable acceptance evidence.
- 0.3.0 — 2026-11-10: add scalar enumerations and Unicode-scalar/string and immediate-element/list length constraints.
- 0.2.0 — 2026-11-10: adopt RFC 9485 I-Regexp, remove bespoke regex syntax, specify Unicode and adapter conformance obligations, and add exact numeric range refinements.
- 0.1.0 — 2026-11-10: draft the numeric hierarchy and named flat-contract model on the numeric-types branch, inspired by Racket contracts.

</details>
