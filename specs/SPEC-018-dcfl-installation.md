---
id: SPEC-018
title: DCFL Membership Under Dialect Installation
status: implemented
mode: reference
version: 0.2.0
date: 2026-09-10
owner: CBCL maintainer
---

# SPEC-018: DCFL Membership Under Dialect Installation

| Field | Value |
|---|---|
| id | SPEC-018 |
| title | DCFL Membership Under Dialect Installation |
| Status | Implemented; independent proof and claim review passed |
| Owner | CBCL maintainer |
| Scope | Lean recognisers, proofs, proof tests, and claim documentation |

## Orientation

Intent: Establish the promise that installing dialects preserves membership of CBCL's recursive syntactic message language in [[SPEC-018-dcfl-installation#CON-1800|DCFL]]. A certificate must identify the language it recognises and enforce finite machine components.

Structure:

```text
finite installed environment ----> scope/name classification
                                            |
recursive syntax contract ----------> finite DPDA recogniser
                                            |
accepted finite installations ------> preservation theorem
                                            |
raw-text lexer ---------------------> raw-language lifting
```

Decisions: [[SPEC-018-dcfl-installation#ADR-1800]] fixes an environment before constructing its recogniser. [[SPEC-018-dcfl-installation#ADR-1801]] separates syntactic admission from execution and causal verification.

Load-bearing: [[SPEC-018-dcfl-installation#REQ-1800]] standard machine certificate; [[SPEC-018-dcfl-installation#REQ-1801]] recursive recognition equivalence; [[SPEC-018-dcfl-installation#REQ-1802]] finite installation sequences; [[SPEC-018-dcfl-installation#REQ-1803]] raw-language lifting.

Controls:

- [[SPEC-018-dcfl-installation#REQ-1804]] forbids replacing recursive admission with head classification, AST membership, bounded-depth enumeration, or proof assumptions.
- [[SPEC-018-dcfl-installation#REQ-1805]] forbids runtime changes within this work.
- [[SPEC-018-dcfl-installation#REQ-1806]] requires explicit boundaries in published claims; raw-text completion requires the lexer bridge.
- [[SPEC-018-dcfl-installation#Amendment Channels]] names the maintainer as amendment authority and requires independent review before approval.

Concrete behaviour: with `d` declaring `ship`, `(lang d (signed sig (ship parcel)))` is admitted. `(signed sig (ship parcel))` is rejected. Nested `lang e` selects `e`; it cannot borrow `ship` from `d`. A wrapper selects its last list-valued argument; subsequent atoms remain structurally permitted. Argument checks still reject missing keyword values and malformed `:caused-by` values.

Evidence: the finite scalar lexer and universal DPDA composition discharge [[SPEC-018-dcfl-installation#CON-1803]]; see [[dcfl-raw-installation-evidence-2026-09-10]]. The concrete lexer declares the lexical language, including rejection. The maintainer owns runtime conformance gaps in [[SPEC-018-dcfl-installation#Open boundaries]].

Detail: [[SPEC-018-dcfl-installation#CON-1801]] defines recursive admission; [[SPEC-018-dcfl-installation#CON-1803]] fixes the Unicode scalar lexical contract; [[SPEC-018-dcfl-installation#Acceptance tests]] defines evidence; [[SPEC-018-dcfl-installation#Reading paths]] directs readers.

## Context and failure mode

The user identifies preservation of DCFL membership under dialect installation as a foundation for subsequent claims. [[SPEC-001]] promises deterministic pushdown recognition. [[SPEC-005-lean-mechanisation]] also claims DCFL preservation.

The mechanical failure is a certificate whose interface permits unrestricted machine state or stack symbols, combined with shallow language predicates. Such a certificate can check while failing to establish standard DCFL membership for recursive messages. The remedy strengthens the certificate and connects it to the intended syntax; it does not weaken the promise.

The stakeholder happy path is: accept a dialect, nest its invocations within ordinary wrappers, install other dialects, and retain deterministic syntactic recognition. The implementer happy path is: instantiate a finite environment, obtain a recogniser and an equivalence theorem, then apply installation induction. Independent reviewers challenge the equivalence and finiteness arguments before downstream proofs use them.

## Requirements

### REQ-1800

Lean SHALL certify standard deterministic pushdown recognition of the token language for every admissible finite environment.

Acceptance requires finite input, control-state, and stack-symbol carriers; deterministic transitions; explicit initial configuration; and acceptance after complete input consumption. Acceptance cannot depend on an unrestricted host-language predicate over the complete input or stack. Any epsilon transitions require the standard noncompetition condition against consuming transitions.

Trace: [[SPEC-018-dcfl-installation#CON-1800]], [[SPEC-018-dcfl-installation#TEST-1800]], [[SPEC-018-dcfl-installation#OBS-1800]].

### REQ-1801

Lean SHALL prove soundness and completeness of that recogniser against recursive syntactic admission in [[SPEC-018-dcfl-installation#CON-1801]].

Both directions quantify over every token list, including malformed encodings. There is no fixed nesting bound. Scope, declared performative membership, wrapper selection, and argument checks belong to the language predicate.

Trace: [[SPEC-018-dcfl-installation#CON-1801]], [[SPEC-018-dcfl-installation#TEST-1801]], [[SPEC-018-dcfl-installation#OBS-1800]].

### REQ-1802

Lean SHALL prove that every finite sequence of accepted fresh dialect installations produces an environment satisfying the DCFL theorem.

The installation relation records the actual acceptance predicate and fresh name condition. The proof establishes preservation of finite declarations and all recogniser admissibility conditions. No bound on the number of installations is fixed globally. Distinct dialects can declare the same custom performative name. Their scoped interpretations remain separate.

Trace: [[SPEC-018-dcfl-installation#CON-1802]], [[SPEC-018-dcfl-installation#TEST-1802]], [[SPEC-018-dcfl-installation#OBS-1800]].

### REQ-1803

Lean SHALL connect the finite classified token language to a declared raw-text lexical language through a deterministic finite-state lexical construction.

The lifting theorem proves DCFL membership for the resulting raw language. It includes atom boundaries, escaping, comments, complete-input consumption, and malformed lexical rejection. A freely chosen tokenisation function or arbitrary inverse-image assertion does not discharge this requirement.

Trace: [[SPEC-018-dcfl-installation#CON-1803]], [[SPEC-018-dcfl-installation#TEST-1803]], [[SPEC-018-dcfl-installation#OBS-1800]].

### REQ-1804

The proof development SHALL NOT discharge recursive DCFL membership using shallow tags, AST inhabitation, a fixed-depth restriction, `sorry`, or new assumed DCFL facts.

Trace: [[SPEC-018-dcfl-installation#TEST-1804]], [[SPEC-018-dcfl-installation#OBS-1800]].

### REQ-1805

This change SHALL NOT modify Rust runtime recognition, installation, expansion, validation, or deployment behaviour.

Runtime differences become explicit follow-up obligations. The task has no deployment toggle, traffic rejection change, or external notification requirement.

Trace: [[SPEC-018-dcfl-installation#TEST-1805]], [[SPEC-018-dcfl-installation#OBS-1800]].

### REQ-1806

Published claims SHALL identify the proved language and its remaining implementation bridges.

They SHALL NOT describe token-only proofs as completed raw-text verification, or syntactic membership as a resource bound or causal-validity theorem.

Trace: [[SPEC-018-dcfl-installation#TEST-1806]], [[SPEC-018-dcfl-installation#OBS-1800]].

## Contracts

### CON-1800

Interface: a finite-machine recogniser certificate and `IsDCFL` predicate satisfying [[SPEC-018-dcfl-installation#REQ-1800]].

Preconditions: a finite input alphabet and explicit finite control-state and stack-symbol types.

Postcondition: the certificate denotes a standard DPDA language. A real-time machine with finite stack rewrites is sufficient. A finite summary tree recogniser compiled into such a machine is permitted; its compilation correctness is proved.

Error model: absent transitions reject. Premature exhaustion, unmatched delimiters, and residual unconsumed input cannot accept.

Implements: [[SPEC-018-dcfl-installation#REQ-1800]]. Verified by: [[SPEC-018-dcfl-installation#TEST-1800]].

### CON-1801

Interface: `Admitted A scope expression`, independently specified from machine execution, and its serialized token language.

Preconditions: `A` is a finite map from dialect names to finite performative declarations. `scope` is absent or names an installed dialect. Core and reserved heads have fixed dispatch priority. The initial scope is absent.

The token grammar for trees is:

```text
Expr ::= Atom | Open Expr* Close
```

`Atom` is a finite environment-dependent classification. Its classes preserve every predicate used below: symbol versus other atom kinds, exact reserved heads, core names, each installed dialect name, per-dialect declared membership, keyword versus positional atom, reserved parameter names, symbol-or-string values, and address-group membership. An address is `@` followed by at least one symbol character. Bare `@` is an ordinary symbol. Classification preserves that complete address predicate. Classes can be a finite product or an equivalent finite partition; arbitrary strings cannot become control states or stack symbols.

A message is a nonempty list with a symbol head. Its recursive admission follows these rules:

- Core simple heads are admitted in every scope. Custom heads require membership in the selected installed dialect; reserved heads never become custom messages.
- A simple tail first consumes an optional address or nonempty all-address list as recipients. Every remaining keyword consumes exactly one following expression. `:caused-by` requires a symbol, string, or nonempty list of symbols/strings. `:thread` and `:sender` require a symbol or string. Other keyword values are structurally arbitrary expressions. Positional arguments cannot be addresses or nonempty all-address lists. Empty lists and mixed lists remain ordinary positional data.
- `meta` requires an operation expression. Remaining expressions are permitted syntax. This rule recognises message syntax; accepting an operation does not execute it or install its payload.
- `lang` requires a symbol naming an installed dialect and a recursively admitted inner message under that dialect. Remaining expressions are permitted syntax. Nested `lang` replaces scope.
- Each of `envelope`, `signed`, `with-limits`, and `with-roles` selects its last list-valued argument as its inner message. That message is recursively admitted under the current scope. Earlier arguments are arbitrary expressions; following arguments are atoms. A wrapper with no list argument rejects.

Postcondition: complete serialized input is accepted exactly when it encodes one admitted message. Payload trees remain opaque syntactic data unless a rule above selects a recursive message position.

Error model: reject unknown dialects, undeclared scoped heads, bare custom heads, invalid recursive inner messages, invalid argument structure, and malformed serialized trees.

This contract records structural parsing plus installed-name admission. It does not assert that Rust's structural parser alone checks installed-name admission. It does not add causal-store, signature, role-binding, template-execution, or installation-validity checks to message syntax.

Implements: [[SPEC-018-dcfl-installation#REQ-1801]]. Verified by: [[SPEC-018-dcfl-installation#TEST-1801]].

### CON-1802

Interface: successful fresh installation `Install A d A'` and its finite reflexive-transitive closure.

Preconditions: the existing acceptance predicate accepts `d`; its name is fresh; `A` satisfies the finite-environment invariant. The proof explicitly identifies any stronger acceptance conditions it uses.

Postconditions: `A'` retains existing bindings, adds the finite declarations of `d`, and satisfies the recogniser invariant. Both `L(A)` and `L(A')` receive standard DCFL witnesses. The sequential theorem starts at the base environment and quantifies over any finite installation list.

Failure leaves `A` unchanged. Duplicate names are outside the accepted fresh-installation relation. Acceptance conditions irrelevant to syntax can remain stronger than this theorem needs, but cannot be silently assumed to establish finiteness or recognition.

Implements: [[SPEC-018-dcfl-installation#REQ-1802]]. Verified by: [[SPEC-018-dcfl-installation#TEST-1802]].

### CON-1803

Interface: Unicode scalar values to classified tokens, then the machine of [[SPEC-018-dcfl-installation#CON-1800]].

Preconditions: input is a list of Unicode scalar values, a finite alphabet excluding surrogate code points. The lexical contract is the S-expression grammar and deterministic tokenization rules in [[IETF/draft-oconnor-cbcl]]. This is the complete accepted-text language, not only canonical serialized text.

Whitespace is space, tab, line feed, form feed, or carriage return. Semicolon comments consume through line feed or end of input. Symbols use ASCII letters, digits, and `_ - . / ! ? + * < > = @`; keywords prefix a nonempty symbol-character sequence with `:`. Strings admit every scalar except unescaped quotation mark and backslash. Their only escapes are quotation mark, backslash, `n`, `r`, and `t`. Booleans are `#t` and `#f`, followed by whitespace, parentheses, quotation mark, semicolon, or end of input.

First-character dispatch is deterministic. A digit, or minus followed by a digit, begins a maximal run of digits and minus signs. That run must match optional minus followed by nonempty digits and fit a signed 64-bit integer. Other minus-prefixed forms follow symbol dispatch. Lists use balanced parentheses. Complete recognition consumes exactly one expression plus surrounding whitespace/comments.

Postconditions: the lexical transducer has finite states for the fixed environment; composition recognises exactly the declared raw language. Runtime lexer equivalence is a distinct checked bridge if claimed.

Error model: invalid escapes, invalid booleans or boolean delimiters, malformed or overflowing numeric runs, empty keywords, unsupported characters, unmatched delimiters, and trailing expressions reject. Ill-formed UTF-8 rejection belongs to a separate byte-decoding bridge if byte-level conformance is claimed.

Implements: [[SPEC-018-dcfl-installation#REQ-1803]]. Verified by: [[SPEC-018-dcfl-installation#TEST-1803]].

## Architecture decisions

### ADR-1800

Decision: construct a recogniser separately for each finite environment.

Rationale: dialect names and declared memberships form a finite classification for that environment. Installation may enlarge that classification without demanding one machine remember unbounded future installations. Existing finite automata components are reused where their contracts suffice; a new certificate exists only to close missing standard-machine restrictions.

Alternative rejected: unrestricted `String` state with a deterministic host function. Functional determinism alone does not establish finite-state control.

Trace: [[SPEC-018-dcfl-installation#REQ-1800]], [[SPEC-018-dcfl-installation#REQ-1802]].

### ADR-1801

Decision: prove recursive syntactic admission independently of expansion and causal validity.

Rationale: dialect installation changes finite name admission within a fixed recursive grammar. Template evaluation and predecessor resolution introduce separate computations. Their existing guarantees neither replace this proof nor become consequences of it.

Alternative rejected: define admitted syntax as the full verifier's successful outputs. That would change the language under review and import unproved semantic closure assumptions.

Trace: [[SPEC-018-dcfl-installation#REQ-1801]], [[SPEC-018-dcfl-installation#REQ-1806]].

## Acceptance tests

### TEST-1800

Tier: core. Validates: [[SPEC-018-dcfl-installation#REQ-1800]].

Compile the finite-machine interface and exported DCFL witnesses. Inspect finite instances and transition signatures. A deliberately unrestricted string-state candidate cannot obtain a certificate without a finite reachable-state construction. Record the axiom dependencies of the exported results.

### TEST-1801

Tier: core. Validates: [[SPEC-018-dcfl-installation#REQ-1801]].

Compile universal soundness/completeness proofs. Include executable examples for core messages, nested wrappers, scope replacement, same-name coexistence, unknown dialects, undeclared heads, malformed inner messages, missing keyword values, malformed causal lists, positional addresses, and last-list wrapper selection. Verify that bare `@` remains ordinary positional data while `@a` and nonempty all-address lists obey recipient restrictions. Verify that `:thread` and `:sender` accept symbols and strings but reject lists, numbers, booleans, and keywords as values. Include arbitrary-depth theorem coverage, not merely a deepest example. Deliberately bypass a scope or argument check and require its attributed negative example to fail.

### TEST-1802

Tier: core. Validates: [[SPEC-018-dcfl-installation#REQ-1802]].

Compile base, single-installation, and arbitrary finite-sequence theorems. Exercise a fresh dialect, distinct dialects sharing a custom name, and duplicate-name rejection. Check that the exported theorem uses the actual acceptance predicate and preserves prior bindings.

### TEST-1803

Tier: core for full completion. Validates: [[SPEC-018-dcfl-installation#REQ-1803]].

Compile the finite lexical construction and composition theorem. Exercise lexical boundaries, strings containing delimiters, escapes, comments, malformed tokens, and complete consumption. Accept signed integer endpoints `-9223372036854775808` and `9223372036854775807`; reject adjacent overflows `-9223372036854775809` and `9223372036854775808`. Reject boolean adjacency such as `#tx` and `#true`; accept a boolean followed by a legal delimiter. Reject unsupported escapes such as `\q`. Accept `--3` as a symbol under first-character dispatch, while rejecting malformed numeric runs `1-2` and `1-`. A token-only development records this test as incomplete.

### TEST-1804

Tier: core. Validates: [[SPEC-018-dcfl-installation#REQ-1804]].

Audit exported theorem statements and `#print axioms` output. Confirm no `sorryAx` or new project assumptions discharge machine finiteness or recognition. Check universal input quantification and unrestricted nesting. Inspect the independently defined grammar relation rather than trusting theorem names.

### TEST-1805

Tier: core. Validates: [[SPEC-018-dcfl-installation#REQ-1805]].

Inspect the final diff against the starting worktree state. Rust runtime files and deployment configuration remain unchanged by this task. Existing unrelated user edits are recorded separately.

### TEST-1806

Tier: core. Validates: [[SPEC-018-dcfl-installation#REQ-1806]].

An independent reviewer compares each changed headline claim with its theorem statement, input alphabet, scope predicate, installation hypotheses, and lexer/runtime bridge evidence. Claims that exceed those results fail review.

### OBS-1800

Signal: durable proof acceptance report containing commands, exit statuses, theorem names, axiom output, mutation outcomes, review identity, and open bridges. The proof implementer produces this report before claiming completion. The maintainer consumes it when approving downstream reliance.

## Open boundaries

- Owner: maintainer. Runtime lexer/parser equivalence and UTF-8 byte decoding remain separate bridges. The proved raw language is defined by the concrete finite lexer implementing [[SPEC-018-dcfl-installation#CON-1803]], not by successful runtime parsing. There is no separate formal equivalence to IETF prose or raw value-preserving AST parser.
- Owner: maintainer. The intended grammar restricts `:thread` and `:sender` to symbols/strings, while current structural parsing stringifies arbitrary expression values. This is a runtime conformance gap; the theorem retains the intended restriction.
- Owner: maintainer. Rust's address recognition uses `starts_with('@')`, admitting bare `@` as an address. The intended address grammar requires a following symbol character. The theorem treats bare `@` as an ordinary symbol and records runtime parity as incomplete on this case.
- Owner: maintainer. The IETF numeric examples call `--3` invalid, although its normative first-character dispatch makes it a symbol. The lexical contract follows the explicit dispatch rule; reconcile that example without changing runtime behaviour in this task.
- Owner: proof implementer. The Rust structural parser tracks whether scope exists, while installed dialect membership is checked elsewhere. Locate that path before claiming implementation equivalence.
- Independent review completed: the foundation/specification comprehension review, recursive installation review, and final raw-language review are recorded in the evidence reports. The author did not self-approve these gates.
- Owner: maintainer. The source-code wikilink to `crates/cbcl-core/src/message.rs` is unresolved by the Markdown vault. Keep this source reference as explicit vault debt; the file exists and supplies the cited evidence.

Source evidence: [[IETF/draft-oconnor-cbcl]] core grammar and scoped invocation sections; [[crates/cbcl-core/src/message.rs]] `parse_message_scoped`, `parse_dialect_msg`, `parse_wrapped`, `parse_simple`, and `parse_caused_by`. These sources inform mismatch reporting. The user-approved preservation promise supplies the governing intent.

## Amendment Channels

The CBCL maintainer can amend the contract through explicit conversation instructions or reviewed specification edits. An agent can propose changes and record evidence. Independent review is required before this draft is marked approved. No amendment channel can label an incomplete proof complete without corresponding evidence. The controls in [[SPEC-018-dcfl-installation#REQ-1804]], [[SPEC-018-dcfl-installation#REQ-1805]], and [[SPEC-018-dcfl-installation#REQ-1806]] remain binding within the accepted task scope.

## Reading paths

Reviewer: [[SPEC-018-dcfl-installation#ADR-1800]] → [[SPEC-018-dcfl-installation#ADR-1801]] → [[SPEC-018-dcfl-installation#Open boundaries]] → [[SPEC-018-dcfl-installation#TEST-1806]].

Implementer: [[SPEC-018-dcfl-installation#CON-1801]] → [[SPEC-018-dcfl-installation#TEST-1801]] → [[SPEC-018-dcfl-installation#REQ-1801]].

Stakeholder: [[SPEC-018-dcfl-installation#Context and failure mode]] → [[SPEC-018-dcfl-installation#REQ-1802]] → [[SPEC-018-dcfl-installation#TEST-1802]].

## Gate evidence

The generic finite-machine and forest-compilation foundation is implemented and independently reviewed. Its build, arbitrary-word correctness, axiom audit, and malformed-input mutation evidence are recorded in [[dcfl-foundation-evidence-2026-09-10]]. The Orientation comprehension review identified the raw bridge contract and predicted scope replacement correctly after clarification.

The concrete CBCL algebra, classification fidelity, scope-indexed recursive admission bridge, and finite installation theorems are implemented and independently reviewed. [[dcfl-installation-evidence-2026-09-10]] records validation and the exact Lean acceptance-gate link. The unconditional theorem also covers arbitrary finite append sequences without assuming acceptance-gate correctness.

Raw lexical lifting is implemented. [[dcfl-raw-installation-evidence-2026-09-10]] records the finite scalar encoding, universal exact-name theorem, lexer/parser composition, installation capstones, kernel tests, mutation checks, axiom audit, and independent review. REQ-1800 through REQ-1806 are discharged within the stated scope. Rust parser/admission equivalence and UTF-8 byte decoding are not established.

## Changelog

- 2026-09-10: Draft the user-approved DCFL installation promise with recursive scope and explicit finite-machine and raw-language obligations.
- 2026-09-10: Complete finite scalar lexical lifting and full installation witnesses; independent review passes the stated scope.
