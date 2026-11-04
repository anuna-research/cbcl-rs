# Fresh cross-model adversarial review record

Reviewer: general_checkpoint_review, fresh context, gpt-6-astra. Read-only brief
and source review, followed by scoped deltas. The producer did not validate its
own artifact. This is experimental evidence; human cryptographic review is open.

Findings and dispositions:

- Pin admission API and distinguish global state computation from endpoint host
  policy: explicitly uses cbcl_parser::state_exports::admit and native
  escrow::fold_instance; not AdmissionMonitor or Agent policy execution.
- Bind all source/ancestor definitions, thread and nested dialect context: source
  closure hash covers exact complete supplied registry text; every message is
  checked against the selected thread and leaf context. No ambient registry.
- Native consumer admission is shape/causal acceptance, not escrow authorization
  for external effects. Brief, journal authentication label and result scope make
  that boundary explicit. Ed25519 authentication is not claimed.
- Set bounded prover parallelism, record aggregate process-tree resource use:
  initial setting1/exponent16 partial was interrupted; tuned setting4/exponent18
  remains one prover process under unchanged memory/time caps. RSS is sampled;
  installation peak was not captured. Internal backend CPU/GPU behavior was not
  independently characterized.
- Compare native output bytes, rather than only parsed JSON. Drawing expectations
  come from the actual SDK fold; native status expectations are literal values.
  Native/SDK generation differences and exact canonicalization changes are saved.
- Signer-commitment test must not silently skip on rejection: mutated role-free
  input is now required to succeed before its different commitment is asserted.
- Independent expected commitments: native reference captured before proof under
  a separate directory; standalone receiver uses it, not prover expected.json.
- Direct guest negatives previously accepted every executor error. They now run
  a valid control and require the specific guest panic/reason. Infrastructure or
  resource failures are inconclusive failures, not successful rejection evidence.
- Resource manager could leave a child after group leader exit. It now kills the
  whole process group in finally. Regression checks cover normal-leader descendant
  cleanup and monitor SIGINT interruption; SIGTERM handling is also installed.
  Uncatchable SIGKILL remains outside this supervisor's guarantee.
- Preserve first image/verifier while changing build tracking. Copies were kept
  in ignored artifacts; SHA-256 confirms identical guest image across rebuilds.
  methods/build.rs tracks wrapper/core/parser path dependencies to avoid stale ELFs.

Reviewer after these changes reported no new material checkpoint soundness defect,
while leaving pending proof and receipt acceptance open. Final proof/result delta
review is recorded below after the remaining runs complete.

Additional producer verification correction: an initial mutation run included a
failing ancestor fixture and cannot be acceptance evidence. Native semantics ignore
unresolved unused parents, and a template reference alone does not create protocol
checking dependency. The revised ancestor fixture has a post-opener protocol edge
to its parent's performative. Full native baseline passes, and final mutation runs
start with that passing baseline and select each mutant's specific test. Earlier
records are retained under pre-ancestor-fixture-fix and explicitly non-authoritative.

Final reviewer response: “No material blockers found in the final reviewed delta.”
It explicitly accepts the signer/metadata boundary, native ancestor semantics,
bandwidth exclusions and in-place deletion guard, while distinguishing measured
proof feasibility from un demonstrated bandwidth benefit and production readiness.
This is code/evidence review, not human cryptographic or production signoff.

Final measured artifacts: both dialects' real composite and succinct receipts
verify under the same image; standalone succinct verification measured12ms and
18ms. Final guest negative run includes sender/cast and genuinely required ancestor
cases. All retained receipt kinds pass honest checks and reject wrong expectations,
changed snapshot, corruption and a fake receipt with dev mode enabled. Native
acceptance-corrected is the final passing baseline. Failed earlier assumptions
remain in staged logs and do not constitute passing acceptance evidence.
