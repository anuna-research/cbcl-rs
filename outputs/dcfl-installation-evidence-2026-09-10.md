# Recursive token-language installation evidence

This extends [[dcfl-foundation-evidence-2026-09-10]] and discharges the token
recognition and Lean installation portions of [[SPEC-018-dcfl-installation]].
This report records the token milestone. The subsequent
[[dcfl-raw-installation-evidence-2026-09-10]] discharges
[[SPEC-018-dcfl-installation#REQ-1803]].

## Results

`InstalledSyntax.environmentDCFL` constructs a standard finite real-time DPDA
for the recursive classified-token language of every finite declaration list.
Its theorem quantifies over every word, including malformed encodings, and has
no input-length, nesting-depth, or global installation-count bound.

The alphabet consists of ordinary atom categories and a finite table containing
every exact symbol name inspected by the grammar. `decode_encode_atom` proves
that concrete atom classification survives this encoding. `admittedAt` evaluates
concrete syntax directly under a named finite scope; `encoded_direct_tree` and
`recognizes_expression` connect it to recognition. The recursive evaluator
implements core/custom membership, scope replacement, last-list wrappers,
optional recipients, and keyword-value checks.

`dcfl_preserved` and `dcfl_preserved_many` cover arbitrary finite append
installations. Their unconditional form is stronger than preservation under
any particular verification policy. `VerifiedFresh` additionally names the
existing Lean R1/R2/R3 conjunction and fresh-name condition.
`pipeline_verified_fresh` proves the link from successful `verifyDialectString`.
`verified_fresh_installations_dcfl` covers finite sequences of that relation;
`verified_sequence_unique` preserves unique dialect names. Separate theorems
preserve prior declarations and first-match lookup.

Rust's registry also checks protocol-expansion budgets, R5 and R6, derives
routes, and adds hashes. No Lean/Rust equivalence for those operations is
claimed. The universal finite-environment result needs no assumption that
those checks are correct to cover the finite declarations they select.

## Verification

- `lake env lean LeanCbcl/InstalledSyntax.lean`: exit 0.
- `lake env lean LeanCbcl/InstalledDCFL.lean`: exit 0.
- `lake env lean LeanCbcl/InstalledSyntaxTests.lean`: exit 0.
- `lake build`: exit 0; new modules are imported by the library root.
- `lake env lean DCFLInstallationAudit.lean`: exit 0. Exported recognition and
  preservation results use only standard `propext`, `Classical.choice`, and
  `Quot.sound`; no project assumptions, `sorryAx`, or native-decide trust.
- Concrete grammar tests cover valid nested invocation, bare custom rejection,
  absent dialects, undeclared scoped names, scope replacement, shared custom
  names, all wrapper types' shared grammar, malformed inner forms, keyword
  values, causal lists, recipients, and bare `@`. An induction theorem proves
  wrapper scope preservation under arbitrary nesting.
- The scope mutant bypassed declared membership. The original negative case
  `(lang d (stop))`, with `d` declaring only `ship`, failed by kernel evaluation.
- The argument mutant bypassed the symbol/string requirement for reserved
  keyword values. The original negative `:thread` numeric-value case failed by
  kernel evaluation. Both mutant files elaborated; their failures were false
  test propositions. Logs are retained alongside this report.

Independent reviewer `/root/installation_review` reviewed the specification
and code, independently checked Lean, identified missing classification and
acceptance bridges, and confirmed their resolution after the corresponding
theorems landed. No blocking token-language or concrete Lean gate defects
remained in its final review. It explicitly excluded raw lexical lifting and
Rust equivalence from approval.

## Subsequent completion

The finite Unicode-scalar lexer, composition theorem, and final review are now
complete; see [[dcfl-raw-installation-evidence-2026-09-10]]. The token-only
review above remains a record of that earlier milestone. No runtime or
deployment files were changed.
