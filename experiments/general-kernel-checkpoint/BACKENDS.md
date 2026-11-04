---
mode: explanation
status: research-not-measured-comparison
---
# General-kernel proof backend candidates

The user proposed SP1, Nexus and Jolt during this experiment. All are relevant
candidates for proving interpreter execution, rather than compiling each dialect
into its own circuit. This experiment's shared computation crate contains no
RISC Zero I/O or prover calls; those live in the thin guest and host. Other VMs
still require SDK/runtime integration and compatibility tests, especially their
standard-library/allocation support. No CBCL performance ranking is established.

| Backend | Primary-source finding | Consequence for this experiment |
|---|---|---|
| RISC Zero 3.0.6 | Rust guest, receipt verifies against a program image; local proving documentation recommends 16 GiB RAM. | Initial measured baseline on this 8 GiB Mac uses small segments and capped aggregate memory. A composite receipt can grow with execution; do not call it a constant-size checkpoint. |
| SP1 | Current docs support Rust zkVM execution, core/compressed and wrapped proof kinds. Local core/compressed requirements list 16+ cores, 16+ GiB RAM and 10+ GiB disk; recommend network proving for nontrivial workloads. | Same CBCL input/journal statement can be ported. Execution profiling is useful locally, but this workstation is below published proving minimums. No remote spending or unmeasured speed claim. |
| Nexus | Current main README describes Stwo-based proving and explicitly experimental status; SDK exposes older Nova/HyperNova/Jolt backends as legacy features. | Pin a concrete current commit/runtime before a test. Old Nexus Nova descriptions do not characterize current main. Not yet built or measured for CBCL. |
| Jolt | Current README describes RV64IMAC and alpha status. Current quickstart has Dory and Akita commitment backends; Dory supports optional ZK, Akita currently non-ZK only. | The guest input model explicitly provides UntrustedAdvice<T>: prover input absent from the verifier call, with no privacy guarantee unless ZK is enabled. That directly matches history-as-witness; the guest must validate all advice and the application must reject panic=true. Must measure total verifier inputs/preprocessing as well as proof bytes. Not yet built or measured for CBCL. |

Sources checked during this session:

- https://dev.risczero.com/zkvm/quickstart
- https://dev.risczero.com/api/zkvm
- https://docs.succinct.xyz/docs/sp1/introduction
- https://docs.succinct.xyz/docs/sp1/getting-started/hardware-requirements
- https://docs.succinct.xyz/docs/sp1/getting-started/recommended-workflow
- https://github.com/nexus-xyz/nexus-zkvm
- https://github.com/nexus-xyz/nexus-zkvm/blob/main/sdk/Cargo.toml
- https://github.com/a16z/jolt
- https://jolt.a16zcrypto.com/usage/quickstart.html
- https://jolt.a16zcrypto.com/usage/guests_hosts/guests.html

Comparison contract: identical pinned CBCL computation, dialect source closure,
canonical message set, asserted-signer boundary and resulting state. Record exact
backend/version, real proof versus execution/mock mode, all verifier inputs,
program/verifier preprocessing download, raw/gzip/Brotli bundle bytes, proving and
verification timings, and aggregate peak memory. Ordinary compression applies to
both replay and checkpoint bundle. A fast Fibonacci or SHA demo does not answer
the CBCL question. Private witness and zero-knowledge are different requirements:
a non-ZK proof must still avoid requiring history as a verifier input to save
history-download bandwidth. Privacy leakage is a separate analysis.
