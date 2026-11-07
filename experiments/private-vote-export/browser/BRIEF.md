---
mode: explanation
status: experimental-runtime-gate-passed
---
# Browser runtime gate for Jolt/Dory

Continue the authenticated private-vote experiment with the exact pinned guest
ELF and the same synthetic signed witness. Run Dory/BlindFold inside a browser
Web Worker, rather than treating a WASM Cargo check as runtime evidence.
First verify an existing native proof, then execute/count the guest, generate a
browser proof, export only proof/public IO/preprocessing and measurements, and
verify the exported proof in a fresh independent native process. The browser
module must require the ZK protocol and exact expected experimental statement,
reject populated advice, and pin preprocessing and guest identity. The fixture
is synthetic and known; real private histories are not sent to a server.

This is a prototype of the existing fixed experimental voting profile. It is
not a production general-purpose export API or native R4 attestation profile.
The future interface distinguishes trusted expected context from the outcome
being proved; this gate uses the existing complete expected fixture as an oracle.
The public roster remains signing keys with labels, not human identity proof.
The closed input/output schemas and native computation remain [[../BRIEF]].

Acceptance: honest native proof verifies in browser; wrong context/setup/mode,
coherently changed public output and populated advice reject for the correct
reason. A native count control precedes browser tracing. A browser-produced
proof must verify under pinned native tooling without a history file. Report
browser trace/setup/prove/verification timing, serialized artifact and JS/WASM
sizes, and process memory separately. A failure to link, trace, prove or stay
within caps is an informative failure, never a successful proof.

Use locally installed Chromium via CDP, synthetic local files and an HTTP server
bound to loopback. Every request path is selected from a fixed asset map; private
witness bytes are passed only to the worker. No service worker, remote network
request or server-side prover. Worker cancellation terminates work without
publishing a partial proof. Local process cap: sampled 4 GiB aggregate RSS,
1 GiB disk reserve, 30 minutes per managed process. Separate compile and runtime
ledgers; browser process memory is not WASM linear memory. Do not modify upstream
cryptographic constraints or relax authentication/closure checks to fit browsers.

The maintainer owns the decision whether browser proving is practical on target
devices. A single desktop run cannot establish mobile feasibility. Native proving
can remain an optional local path while browser packaging/performance evolves.
