# DCFL foundation evidence

Scope: the finite machine and generic forest compiler required by
[[SPEC-018-dcfl-installation#CON-1800]] and the compilation portion of
[[SPEC-018-dcfl-installation#CON-1801]]. This report does not establish the full
recursive CBCL installation promise.

## Implemented result

`ForestAlgebra.isRealtimeDCFL` constructs a real-time finite DPDA for the
independent predicate `ForestAlgebra.language`. The alphabet has `k + 2`
symbols, control has `n + n` states, and the stack alphabet has `n + n + 1`
symbols for an algebra with `k` atom classes and `n` summaries. These are
construction parameters, not bounds on input length or nesting depth.

`ForestAlgebra.accepts_iff` quantifies over every token word. Soundness follows
from simulation of the syntax decoder and its consumed-prefix reconstruction
invariant. Completeness follows from structural induction over finite forests.
The language predicate contains no reference to machine execution.

The generic algebra decides whether empty or multiple-root forests are admitted.
The CBCL instance must enforce exactly one recursively admitted message.

## Verification

- `lake env lean LeanCbcl/FiniteDPDA.lean`: exit 0.
- `lake env lean LeanCbcl/FiniteForest.lean`: exit 0.
- `lake env lean LeanCbcl/FiniteForestTests.lean`: exit 0.
- `lake build`: exit 0, including the new modules through the library root.
- A temporary mutant allowed inside-list states to use the root acceptance
  predicate. The unterminated token stream `[0, 0, 1]` then accepted. Its
  negative example failed with Lean reporting that the asserted proposition
  was false. The final mutant elaborated successfully; this was a behavioural
  failure, not an import or type error. The mutant is not in the library.
- `#print axioms` for `ForestAlgebra.accepts_iff`,
  `ForestAlgebra.isRealtimeDCFL`, and `ForestDecoder.run_encodedPrefix` reports
  only `propext` and `Quot.sound`.
- `ForestTests.arbitrary_list` additionally uses standard `Classical.choice`.
  No audited result uses `sorryAx`, a new project axiom, or native-decide trust.

Independent reviewer: `/root/dcfl_review`, given the specification and
deliverables. It independently compiled the foundation and audited the capstone
axioms. It found no blocking defects and confirmed the arbitrary-word proof,
finite-machine restrictions, malformed-delimiter treatment, and stated scope.

## Outstanding acceptance

The full acceptance tests of [[SPEC-018-dcfl-installation]] remain incomplete.
The next executable plan task is `recursive`, followed by `installation` and
`lexical`, then final independent review. No concrete CBCL DCFL witness, accepted
installation sequence theorem, or raw-text lexical lifting theorem has been
added by this foundation change. The earlier shallow certificate remains
unchanged and cannot substitute for those results.

Runtime Rust files, deployment configuration, and pre-existing untracked work
were not changed by this task. The new specification remains draft.
