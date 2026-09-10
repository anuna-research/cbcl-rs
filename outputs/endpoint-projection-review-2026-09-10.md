Endpoint projection Lean review — 2026-09-10

Reviewed current sources at HEAD `2c82056183118978edd57dee2885cffa8548b3bc`: EPP, EPPCompletion, Projectability, ProtocolProjection, Bridge, and Splice, with the EPP manuscript used to check intended scope. No proof implementation changes were made. Existing broader audit reports were treated as background, not verification evidence.

The core abstract safety and completion arguments are sound under their stated hypotheses. I found no invalid proof step or admitted theorem in these modules. The actionable findings concern claims exceeding the formal statements.

1. **Medium — the named projectability equivalence is not an equivalence.** `LeanCbcl/Projectability.lean:329` conjoins universal sufficiency with an existential counterexample. This does not establish that each locally verifiable protocol is causally local. The preceding comment correctly observes that unused or unrealizable legal edges invalidate that converse. Rename the theorem and its “both directions” description to sufficiency plus counterexample; alternatively state and prove a converse with explicit edge-realizability hypotheses. The current result remains useful and correctly proved.

2. **Medium — the temporal bridge does not prove eventual finite-time resolution.** `LeanCbcl/Bridge.lean:52` allows arbitrary predicate stores and infinitely many predecessors. Exhaustion says each predecessor arrives at some time; it does not give one time at which all predecessors have arrived. For example, take one role, a message citing all natural-number-indexed predecessors, and deliver predecessor k at time k+1 while holding the dependent message from time zero. With conformant fields, universally legal edges, and a true clause, the global run is closed and safe and exhaustion holds, yet the message remains Unknown at every finite time. This is a mathematical countermodel description, not a separately executed Lean example. The checked theorem at line 172 correctly proves limit equality and persistence of already-resolved verdicts. Add finite predecessor support and a maximum-arrival-time argument if finite-time resolution is intended; remove unsupported “finite store” descriptions otherwise. The manuscript's finite-configuration restriction is not encoded in Schedule.

3. **Medium — splicing commentary overstates the cryptographic and minimality results.** `LeanCbcl/Splice.lean:220` proves indistinguishability for an abstract observation while changing `perf` between worlds. There is no hash function, byte encoding, binding condition, or computational adversary. This cannot by itself establish a content-hash cryptographic impossibility. At line 454, the equivalence characterizes resolution in a model that defines it as predecessor presence; it does not compare all possible evidence or communication schemes. At line 370, `openStore` is a predicate over the same abstract messages, not an authenticated opening representation. Narrow the prose to observation indistinguishability and semantic factoring; concrete authentication and representation require separate refinement proofs.

The following are material, already disclosed assumptions rather than newly discovered proof errors:

- **Concrete projection:** `ProtocolProjection.lean:52` assumes `AgreesOnRole`, including clause equivalence on every relevant type. The transfer theorem is valid, but no concrete erasure/splice function is proved to satisfy that interface. Causal locality constrains `legalPred`; the abstract `clause` is independent, so the interface cannot simply be inferred from locality without a concrete syntax interpretation and its supporting invariant.
- **Completion and compatibility:** `EPPCompletion.lean:37` shares a single obligation system. `EPP.lean:236` assumes endpoint coverage and predecessor closure. Common cast/seals and agreement of concrete hash-addressed records are not checked by these structures. A common message universe already supplies identity in the abstract model. Completion proves witness transfer once obligations and compatibility are supplied; it does not derive branch-dependent obligations or implement seal agreement.
- **Verdict scope:** `EPP.lean:109` uses resolved-first semantics. The violation-stability theorem must not be cited as a theorem about the deployed eager verifier without a semantics bridge. On safe closed stores, every present message is Valid (`valid_of_safe_closed`), so the reconciliation's Unknown/Violation equivalences are false-on-both-sides cases. Likewise the temporal bridge's violation premise is impossible on its safe global domain. The transfer of resolution and goodness is substantive; general detection of unsafe executions is outside these statements.

Proof coverage checked:

| Module | Assessment |
| --- | --- |
| EPP | Local predecessor availability follows from conformance of both messages, legal predecessor typing, and causal locality. Projection preserves goodness/resolution; compatible gluing preserves safety; both set-level round trips hold. |
| EPPCompletion | Role-relevant witnesses survive projection, local witnesses survive union, and validity transfers. Shared obligations are a precondition. |
| Projectability | Partial-store missing predecessors are eventually observable in the ideal projection; full projections resolve. The explicit nonlocal safe-run example is valid. |
| ProtocolProjection | Message/store equalities and relevant protocol-field agreement correctly transfer all verdict predicates. Concrete projection remains outside the theorem. |
| Bridge | Monotone store inclusion correctly transfers terminal verdicts, exhaustion identifies limits, and those limits yield the projection family. No finite-time resolution theorem. |
| Splice | The explicit observation counterexample, predecessor-resolution facts, type factoring, and model-relative resolution equivalence check. Stronger cryptographic interpretations are unproved. |

Validation performed on current sources:

- `lake build` succeeded (77 jobs).
- Separate `lake env lean LeanCbcl/<module>.lean` elaboration succeeded for all six reviewed files.
- A fresh 15-theorem dependency audit covered local resolution, reconciliation, safety and completion correspondence, projectability, protocol transfer, temporal correspondence, and splice/opening results. Dependencies were subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom appeared. The audit driver is `/private/tmp/EndpointProjectionAudit.lean`.
- Source inspection found no proof admissions, unsafe implementations, or native-decision proofs in these six modules.

Review completed. Suggested repairs are recommendations, not changes performed. Validation establishes the checked abstract statements; it does not certify the Rust projection or runtime verifier.
