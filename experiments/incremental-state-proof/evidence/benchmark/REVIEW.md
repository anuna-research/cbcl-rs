# Fresh-context benchmark review

Reviewer: independent `benchmark_brief_review` agent, read-only review of the
brief, harness, native SDK implementation and result claims. This does not replace
human cryptographic review or validate a drawing proof.

Initial numeric brief: no material fairness/scope defect; require actual snapshot
reconstruction timing if claiming client speed advantage. Superseded after user
identified drawing workload; no snapshot continuation speedup is now claimed.

Drawing review findings and disposition:

- Timed decoding included correctness assertions and parse measured two parses.
  Retained the actual measurement but renamed fields to validation-inclusive
  timings and explicitly excluded pure client decode claims.
- Source provenance omitted executed WASM/compiler/index. New captures include
  hashes. Early rows' later-added metadata is explicitly retrospective; report
  does not claim it was captured during those measurements.
- Failed reruns could publish stale successful result JSON. Runner now removes
  old result and ledger before starting, and summary excludes rows with a failed
  run ledger. A deliberately failed ledger excluded an existing successful row;
  original evidence was restored (stale-result-check.json).
- Summarizer hardcoded the sibling repository. It now respects CBCL_BUS_REPO.

Final reviewer response after corrections: “No remaining material findings.”
Reviewer checked cumulative proof-call versus uninterrupted wall-time distinction,
and that numeric proof timing is not claimed to measure drawing proving.
At that review, the 4096-by-30 row was pending and not approved as completed.
The final-row disposition is recorded separately once its bounded run ends.

Final-row delta review: sizes and native time match saved drawing-4096-30.json;
1.0% is correctly rounded, SDK overhead caveat is accurate. Reviewer requested a
saved process ledger for the manually observed successful 295.683-second run.
Captured supervisor stdout (tool session 56966) was transcribed into
 drawing-4096-30-run.json with explicit provenance; source log is retained. This
is a session observation, not independently remeasured timing. No other material
findings were reported. All drawing measurements completed; no drawing proof claim.
