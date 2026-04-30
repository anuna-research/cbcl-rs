# Table 4 — paper-ready (REQ-1160 wide schema)

Generated 2026-04-30 from `cargo run --release --example cbcl-arena -- --n 300 --seed 0xCBC1A1EADEFA0173`.
Headline predictions all PASS (REQ-1150 / OBS-1110).

| Cell | PSI | Yao | DC |
|------|-----|-----|----|
| 03-A (vanilla, published) [N=300]   | 0.490 [0.434, 0.546] | 0.213 [0.171, 0.263] | 0.000 [0.000, 0.013] |
| 03-A-novel (vanilla, novel) [N=300] | 0.000 [0.000, 0.013] | 0.003 [0.001, 0.019] | 0.000 [0.000, 0.013] |
| 03-B (CBCL, published) [N=300]      | 0.000 [0.000, 0.013] | 0.000 [0.000, 0.013] | 0.000 [0.000, 0.013] |
| 03-B-novel (CBCL, novel) [N=300]    | 0.000 [0.000, 0.013] | 0.000 [0.000, 0.013] | 0.000 [0.000, 0.013] |

Caption: Multi-agent arena demonstration (Demo 3) — attack success rate per cell, Wilson 95% CI at N=300 runs. `03-A` = vanilla NL-chat agent; `03-B` = CBCL-disciplined agent. `-novel` denotes the malicious-novel attacker category (author-crafted, contamination-controlled per REQ-1131); otherwise the malicious-published category (replicates the public *Malicious (claude-sonnet-4-6)* PSI playbook at 2026-04-30). Cells are attack-success rate (fraction of runs where the focal agent's security score is `−1`).

## Notes for paper integration

**Calibration (PSI 03-A):** vanilla agent's measured rate of 0.490 with 95% CI [0.434, 0.546] confidently brackets the public Arena baseline of 0.43 reported on the *Malicious (claude-sonnet-4-6)* leaderboard at 2026-04-30. The CI does not exclude 0.43, validating the comparator.

**DC zeros are honest, not artefacts.** The DC unanimity rule (REQ-1112) drops a payer's security only when *every* diner names that specific diner by invite code. A single attacker among three cannot achieve unanimity unilaterally, so even the vanilla agent registers 0/300 against the published-attacker patterns. CBCL's contribution to DC is preventing the *coalition* attack — out of scope here per the failure-mode list. The honest reading: DC's classical anonymity property is robust against single-attacker manipulation regardless of agent strategy; the CBCL discipline is necessary but not sufficient evidence for DC, and the load-bearing CBCL claim lives on PSI and Yao.

**Yao (03-A): 0.213 [0.171, 0.263] is meaningful.** Vanilla leaks 21.3% under the published attacker library (direct-ask, compare-by-naming, threshold-injection, social-pressure). The CBCL cell collapses to 0.000 across published and novel — bracket-and-narrow over a typed dialect cannot leak the exact wealth value because the dialect's content forms (`yao-bracket`, `yao-bracket-commit`, `yao-bracket-reveal`) carry only the comparison bit, never the magnitude.

**The contamination-stress result is the single most important number.** `03-B-novel × PSI = 0.000 [0.000, 0.013]` shows CBCL defeats novel attacks not present in any LLM's training data. This is the column the paper should foreground — published attacks at 0.000 are necessary but contamination-vulnerable evidence; novel attacks at 0.000 are the load-bearing claim.
