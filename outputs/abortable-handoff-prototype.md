# Abortable checkpoint handoff experiment

[[SPEC-023-abortable-budget-handoff]] adds a separate symbolic profile for switching
from concurrent checkpoints to an abstract recovery agreement service. The original
unsafe renewal and sealed-checkpoint models remain unchanged.

```text
operation signatures --> sealed checkpoint --> prepare QC --> activation QC
                                                   |              |
                                                 stall         install
                                                   |
                                              abort quorum
                                                   |
                                      frozen operation journals
                                      + known prepare certificates
                                                   |
                                      abstract unique recovery decision
                                                   |
                                       install the same or a safe successor
```

A prepare quorum alone no longer authorizes installation. An honest activation
signer first records a full prepare certificate. Any activation quorum intersects
any abort quorum at an honest validator, so the manifest preserves that evidence.
Recovery must honor it. With no such evidence, recovery can supersede split prepare
votes and select a complete conservative cut. This recovery choice is an explicit
trusted one-shot consensus oracle; the prototype does not implement BFT consensus.

Old operation certificates remain valid and reserved. Handoff never erases effects
or releases a reservation. A late fast certificate and a recovery decision install
the same semantic successor, and replay preserves already-spent capacity. A later
epoch cannot be rolled back. Overloaded candidate unions still stall; cancellation
and reclamation remain open.

Run from the repository root:

```sh
python3 proofs/validator-budget/check_handoff.py --lean-mutation
python3 outputs/handoff-independent-quorum-audit.py
python3 -m unittest discover -s proofs/validator-budget -p 'test*.py'
```

The runner records passing cases and catches behavioral mutants that omit prepare
evidence, allow post-abort activation, ignore the pinned successor, reset a replayed
journal, or install on preparation alone. Its Lean mutant weakens the activation
freeze guard and fails the snapshot proof. Recorded evidence is in
`outputs/abortable-handoff-checks.json`, `outputs/abortable-handoff-lean-mutation.json`
and `outputs/abortable-handoff-quorum-audit.json`.

Independent cross-model review by `/root/handoff_adversarial_review` (gpt-6-astra,
fresh context, specification and deliverable only) found no blocking defect within
this symbolic scope. The reviewer supplied the reproducible schedule audit and
checked late delivery to an already-aborted validator. Its report remains immutable
even when later delivery increases locally known prepare evidence. The fresh
Orientation reader predicted hidden-certificate preservation and conditional recovery;
its late-installation ambiguity was clarified in the specification.

Lean proves local signed identity and activation freeze, reachable snapshot validity,
selected-quorum evidence preservation, and recovery preservation under the evidence
honoring interface premise. It does not prove production consensus, persistence,
payload retention, Python correspondence or full asynchronous resource accounting.
The minimal Lean activation field tracks issued votes, not all subsequently learned
prepare evidence. Prepare vote-once remains an explicit premise of prepare uniqueness.
The prior [[SPEC-022-sealed-budget-checkpoints#Evidence and remaining proof obligations]]
remain outstanding. No certification runtime has been enabled.
