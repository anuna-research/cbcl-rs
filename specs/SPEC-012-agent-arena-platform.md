---
id: SPEC-012
title: Agent Arena — Composable Referee on cbcl-lfe-router with Spindle Game Theories
status: draft
version: 0.3.0
date: 2026-05-08
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-001 (CBCL — homoiconic safe self-extending agent communication)
  - SPEC-002 (structural contracts — causal protocols, shape constraints, blame)
  - SPEC-011 (Multi-Agent Arena Challenge Simulator — deterministic LangSec '26 demo)
  - cbcl-lfe-router (capability-keyed message router; signed receipt log)
  - cbcl-lfe-router-client / hark (per-user daemon + agent CLI)
  - spindle-rust (defeasible-logic engine for game theories)
prior-art:
  - SPEC-011 (cbcl-arena crate; this spec composes its operators as Spindle theories)
  - Arena, Greco et al. 2026 (https://arena.nicolaos.org/) — public multi-agent challenge platform
  - Lichess / Chess.com matchmaking (direct challenge + open seek queue)
  - PROTO-001 (USDD Agent Protocol v1.4.0)
related:
  - plans/EXTRACT-arena-platform.spl
revision-history:
  - 0.1.0 (2026-05-06) — hosted-seats with `LlmBackend` / `DisciplinedSeat` inside the platform
  - 0.2.0 (2026-05-06) — referee proxy with custom JSON wire protocol; matchmaking promoted (ADR-1212)
  - 0.3.0 (2026-05-08) — composable redesign. The arena is an *agent on cbcl-lfe-router*, not a service. Games are `(CBCL dialect, Spindle theory)` data pairs — no Rust per game. Referee mode collapses to one (CBCL-disciplined by construction). Transcripts publish through a signed `arena:result` stream as the scientific artefact. Player profile + agent declaration added (ADR-1218 through ADR-1222).
repository: standalone — TBD on codeberg.org/anuna
target: standalone repo `agent-arena` (Rust; arena agent + library) plus an optional `agent-arena-cbcl` in-process harness for SPEC-011 byte-parity.
---

# SPEC-012: Agent Arena — Composable Referee on cbcl-lfe-router with Spindle Game Theories

## Information Table

| Field          | Value                                                                |
|----------------|----------------------------------------------------------------------|
| Document ID    | SPEC-012                                                             |
| Title          | Agent Arena — Composable Referee on cbcl-lfe-router with Spindle Game Theories |
| Status         | draft                                                                |
| Version        | 0.3.0                                                                |
| Date           | 2026-05-08                                                           |
| Author         | Anuna Research                                                       |
| Audience       | Engineering (composition + game authoring)                           |
| Methodology    | PROTO-001 USDD Agent Protocol v1.4.0                                 |
| Tier           | 2 (multi-tenant; signed messages and signed result stream)           |

---

## Overview

`cbcl-arena` (SPEC-011) is a deterministic local simulator: one process, one seed, one Wilson CI per cell. That shape is correct for the LangSec '26 paper and stays as-is for that use case (`agent-arena-cbcl` in-process harness, REQ-1290).

This specification covers the second use case — **two players, sitting at different machines, each running their own agent (any provider, any scaffolding, even non-LLM), wanting to play PSI / Yao / Auction / DC / Ultimatum against each other and have the result count.** v0.2.0 attempted this with a custom JSON-over-WebSocket referee proxy, custom matchmaker, custom signing, custom match-log format. v0.3.0 observes that **every one of those concerns already has a sibling project that solves it cleanly**, and recomposes the arena as a thin agent over them:

| Concern                | v0.2.0                                | v0.3.0                                                                 |
|------------------------|---------------------------------------|------------------------------------------------------------------------|
| Wire protocol          | Custom JSON frames                    | CBCL through `cbcl-lfe-router`; arena registers `arena:*` capabilities |
| Player identity / sigs | Custom Ed25519 + per-frame signing    | Router's existing Ed25519 agent auth (SPEC-007 in router repo)         |
| Player CLI             | New `arena` binary                    | `hark` (router-client) extended with arena verbs                       |
| Game definition        | `Operator + GameMetadata` Rust trait  | Two data files: `<game>.cbcl` (dialect grammar) + `<game>.spl` (Spindle theory) |
| Referee mode           | Passthrough vs CBCL-disciplined       | Single mode — CBCL-disciplined by construction (only mode the stack allows) |
| Match log              | Custom JSON file under `<data>/matches/` | Router receipts + arena's signed `arena:result` frame                |
| Public artefact        | Implicit (read the JSON files)        | Explicit signed `arena:result` *stream*; leaderboard is a projection over it |

The thesis is **architectural compression**: the arena's load-bearing surface reduces to (a) a matchmaker, (b) a Spindle-driven referee that advances per-match state on each parsed message, (c) a per-result publication stream. Everything else is reused.

The thesis is **not** a security claim about CBCL; that argument is owned by SPEC-011 and survives because the deterministic measurement matrix is *not* routed through the router. The matrix stays in-process in `agent-arena-cbcl`, byte-identical to today.

### Design Provenance

**SPEC-011 operators → Spindle theories.** Each existing operator's scoring logic is rewritten as an SPL theory: facts for the recorded transcript, defeasible rules for legal moves and termination, conclusions for `(winner ?seat)` / `(utility ?seat ?u)` / `(security ?seat ?s)`. `reason()` over the theory is deterministic forward-chaining; the referee never needs an LLM-as-judge for the v0.3 catalogue. (Future games requiring subjective scoring may register a separate `judge:assess` agent; out of scope here.)

**cbcl-lfe-router as transport.** The router already provides capability-keyed routing (`<dialect>:<verb>`), Ed25519 agent authentication, content-addressed signed receipts (= the audit log), and per-WebSocket isolation. The arena registers as one more agent and plugs in.

**Hark as player CLI.** `hark recv` / `hark reply` is already the player-side idiom for talking to any router agent. v0.3 adds arena-aware sugar (`hark seek`, `hark challenge`, `hark play`, `hark leaderboard`) but the underlying frames go through the same daemon and the same router connection.

**`arena.nicolaos.org`.** The closed-source public Arena platform's observable surface — submit agents, allocate matches, publish transcripts and scores — fits our model exactly, with the added property that *publication is the signed stream*, citable as a scientific artefact.

### Scope

This specification covers:

- A standalone Rust crate `agent-arena` exposing the arena agent (matchmaker + Spindle referee + result-stream publisher) and a small library reused by `agent-arena-cbcl`.
- The arena's CBCL verb vocabulary (`arena:profile`, `arena:seek`, `arena:challenge`, `arena:accept`, `arena:cancel`, `arena:resign`, `arena:match-start`, `arena:setup`, `arena:result`, `arena:report`, `arena:leaderboard`).
- Three matchmaking primitives: **direct challenge**, **open seek queue**, **self-play**.
- A built-in catalogue of five reference games as `(dialect, theory)` pairs: PSI, Yao, DC, Auction, Ultimatum.
- Open game registration: drop a `(<game>.cbcl, <game>.spl)` pair into the games directory; restart; the arena registers the dialect's verbs as capabilities and `arena games list` shows it.
- Player profile (durable, per `PlayerId`) and agent declaration (per match) frames.
- Eligibility predicates over both rating and declarations.
- A signed, append-only `arena:result` publication stream as the scientific artefact.
- A query-time leaderboard projection over the stream, with Wilson 95% CIs from `statistics::wilson_ci`.
- Hark CLI extensions (`hark seek`, `hark challenge`, `hark play`, `hark leaderboard`, `hark profile`).
- Preservation of SPEC-011's in-process deterministic harness.

This specification does **not** cover:

- Hosting players' LLMs, scaffolding, or provider keys — the platform never sees these (NFR-1213).
- A skill-rating system (Elo, Glicko-2). Streams are rating-ready (REQ-1260) but rating math is future work (ADR-1216).
- A web UI — `hark` is the interface; a UI may consume the result stream later.
- Real-money or stake-based betting.
- Cryptographic privacy of game contents (operators use the project's canonical-hash placeholder, ADR-1211).
- LLM-as-judge games. The v0.3 catalogue is deterministic-scorable; subjective games would register a separate judge agent (out of scope).
- Modifications to `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client`, or `spindle-rust`. The arena consumes them as fixed inputs (NFR-1212).

---

## User Profiles

### User: Researcher

**Role:** Reproduce or extend a published claim about live-LLM agent behaviour in strategic-communication games.
**Goals:** Run their own agent against a baseline; benchmark across providers; replay a published match from the result stream.
**Constraints:** Reproducibility from receipts + result frame is non-negotiable; declarations must travel with results.
**Workflow:** `hark play --game psi --self-play --left ./my-agent.sh --right ./baseline.sh --n 100 --declare anthropic/claude-opus-4-7+vanilla`.

### User: Player

**Role:** Builder pitting their own agent against another player's.
**Goals:** Issue a direct challenge, or post an open seek and wait; play; see their score on the leaderboard.
**Constraints:** Will not give the platform an API key. Wants their agent to keep running on their own machine. May want pseudonymity.
**Workflow:** `hark seek --game yao` (open seek) or `hark challenge <player-id> --game yao` (direct).

### User: Tournament Organiser

**Role:** Run a scheduled tournament across N submitted agents.
**Goals:** Pair every entrant against every other entrant on a fixed game; aggregate; publish a signed `arena:report` bundle.
**Constraints:** Must complete in bounded wall-clock time; cancellations of stalled matches must not deadlock the bracket.
**Workflow:** `hark tournament --game psi --entrants entrants.json --pair round-robin`.

### User: Game Author

**Role:** Implement a new game and have it hosted.
**Goals:** Write `<game>.cbcl` (dialect grammar) and `<game>.spl` (Spindle theory); drop into the games directory; matches available immediately.
**Constraints:** No platform-crate modification, no Rust required.
**Workflow:** Author the two files; restart the arena; `hark games list` shows it.

### User: Stream Consumer (NEW)

**Role:** Third-party researcher, journalist, or auditor reading the public `arena:result` stream without participating.
**Goals:** Filter by game / provider / scaffolding / date; recompute leaderboards locally; verify per-match Spindle scoring against the cited receipts.
**Constraints:** Does not require an account on any specific arena; only needs the stream URL and the players' / arena's public keys.
**Workflow:** `hark stream subscribe --arena <arena-id> --game psi | jq …` or a downstream tool that consumes the stream.

### User: SPEC-011 Maintainer

**Role:** Operate the LangSec '26 deterministic measurement matrix.
**Goals:** Continue producing Demo 3's Table 4 from a single reproducible run; lose nothing in the extraction.
**Constraints:** Wall-time ≤ 600 s at N=300; identical numerics; matrix MUST NOT route through the router.
**Workflow:** `cargo run --release -p agent-arena-cbcl --example spec-011-matrix --n 300 --out report.md` — the in-process harness, no router, no arena agent in the loop.

---

## Threat Model

### TM-1201: Adversary capabilities

The adversary may be: (a) a player whose agent tries to cheat, exfiltrate, or DoS; (b) a network attacker between a player and the router; (c) a co-resident match on the same arena agent; (d) a malicious matchmaker submission (replay, forged challenge); (e) a stream consumer trying to forge results.

The adversary may:

- Send any *CBCL-valid* sequence in the relevant dialect (the router rejects non-conforming bytes before they reach the arena).
- Drop or stall their connection at any point.
- Submit forged or replayed seek/challenge envelopes via WSS or HTTP ingress.
- Run any agent locally (any provider, any scaffolding, any tool-shimming).
- Lie about their declared provider / model / scaffolding (self-reported).

The adversary may NOT:

- Forge another player's signature on a frame (Ed25519 enforced at the router; REQ-1240 inherits).
- Submit non-CBCL bytes through the stack (rejected at hark client-side validation; rejected again at router ingress; never reaches the arena).
- Read another concurrent match's transcript (router scopes receipts; REQ-1241).
- Modify the arena's Spindle scoring (it's a pure function of the recorded transcript; any replay reproduces it).
- Touch another player's API keys (the platform never sees provider keys at all; NFR-1213).
- Forge a result-stream frame (each is signed by the arena's key; consumers verify).

### TM-1202: Threat instances

| Threat | Defence | REQ |
|--------|---------|-----|
| Player connection drops mid-match | Per-match wall-time budget; on timeout, finalise with the recorded transcript and a `seat-timeout` event; arena posts result frame regardless | REQ-1233 |
| Forged challenge or seek | Router-level Ed25519 signature + monotone per-player counter | REQ-1240 |
| Player sends non-conforming bytes | Rejected at hark; rejected again at router; never reaches arena | (by construction) |
| One player's panic affects another concurrent match | Per-match isolation: own task, own theory instance, own buffers | REQ-1241 |
| Replay of a finalised match to manipulate the leaderboard | Result stream is append-only; leaderboard recomputes from the stream at query time, so a duplicate is a no-op | REQ-1260 |
| Player lies about declared provider/model | Honest-scope statement; reproducibility audits expose drift over time | REQ-1270, REQ-1296 |
| Forged result-stream frame from a non-arena key | Each result frame signed by the arena's published key; consumers verify | REQ-1260 |

---

## Functional Requirements

### REQ-1200: Arena agent on cbcl-lfe-router

**Statement:** The arena SHALL run as a single agent registered on a `cbcl-lfe-router` instance, exposing the capabilities `arena:profile`, `arena:seek`, `arena:challenge`, `arena:accept`, `arena:cancel`, `arena:resign`, `arena:leaderboard`, and the per-game move/setup/result verbs derived from each loaded dialect (e.g., `psi:commit`, `psi:open`, `yao:bid`, `yao:reveal`). The arena SHALL NOT modify the router; it is one more agent on a stock router instance.

**Acceptance:** Starting a stock router and connecting the arena agent makes the arena's capabilities resolvable via `hark cap list`.

**Trace:** TEST-1200, CON-1220.

### REQ-1210: Built-in game catalogue

**Statement:** The arena SHALL ship five reference games as `(dialect, theory)` pairs — PSI, Yao's Millionaire, Dining Cryptographers, Sealed-Bid Auction, Ultimatum — each consisting of a `<game>.cbcl` dialect file and a `<game>.spl` Spindle theory file, registered at startup.

**Acceptance:** `hark games list` enumerates the five with their dialect versions and theory digests.

**Trace:** TEST-1210, CON-1230.

### REQ-1211: Open game registration

**Statement:** Adding a new game SHALL require dropping `<game>.cbcl` and `<game>.spl` into the arena's games directory and restarting the arena. No platform-crate modification, no `cargo add`, no Rust required.

**Acceptance:** A toy `tic-tac-toe` `(dialect, theory)` pair appears in `hark games list` after restart; `git diff -- src/` is empty.

**Trace:** TEST-1211, CON-1230.

### REQ-1220: Wire protocol — defer to router

**Statement:** All player↔arena and player↔player communication SHALL travel as CBCL frames through the router using its existing protocol (HTTP ingress for asks; WSS for the arena's agent connection; CBCL parsing and Ed25519 signature verification at the router). The arena's contribution to the wire is the *vocabulary* (the `arena:*` verbs and the loaded games' dialect verbs), not a new transport.

**Acceptance:** A standard router instance with the arena agent attached carries a complete PSI match end-to-end without any custom transport code in the arena.

**Trace:** TEST-1220, CON-1220.

### REQ-1230: Matchmaking — direct challenge

**Statement:** A player MAY post an `arena:challenge` ask naming the opponent's `PlayerId`, the game, and an optional `agent_declaration`. The arena holds the pending challenge until the named opponent posts `arena:accept` (with matching challenge id) or until TTL expires. On accept, the arena issues `arena:match-start` to both seats.

**Acceptance:** Alice issues `hark challenge bob --game yao`; Bob, connected, receives the offer and accepts; the match runs to completion.

**Trace:** TEST-1230.

### REQ-1231: Matchmaking — open seek queue

**Statement:** A player MAY post an `arena:seek` ask declaring the game, eligibility predicates (rating bounds, required/excluded provider, required/excluded scaffolding, required/excluded tag, excluded player), and an optional `agent_declaration`. The arena SHALL pair two compatible seeks (eligibility predicates satisfied symmetrically) using FIFO order on the older seek; on pairing, both players receive `arena:match-start`.

**Acceptance:** Two open `yao` seeks from different players are paired in arrival order; a third seek with `excluded_player: alice` is not paired with Alice's seek; a seek with `required_provider: openai` against an `anthropic`-declared seek does not pair.

**Trace:** TEST-1231.

### REQ-1232: Matchmaking — self-play

**Statement:** A single player MAY post both seats of a match (`arena:seek --self-play` with two distinct seat declarations under the same `PlayerId`). The arena treats the two seats as independent counterparties for the duration of the match and runs the same code path as an inter-player match.

**Acceptance:** A researcher script connecting twice with the same Ed25519 key and posting a self-play envelope yields a complete match transcript and result frame.

**Trace:** TEST-1232.

### REQ-1233: Match timeout, cancellation, resignation

**Statement:** Every match SHALL have a per-match wall-time budget (default 5 min, configurable per game and per match). On timeout, the arena finalises the match with the recorded transcript and a `seat-timeout` event recording which seat(s) were unresponsive, then posts an `arena:result` frame. Either player MAY cancel a *pending* (unstarted) seek or challenge they originated; once the match is started, no unilateral cancellation — only `arena:resign`, which finalises with that seat's utility = 0 and security per the Spindle theory's scoring on the recorded transcript.

**Acceptance:** Killing one player mid-match yields a finalised result with `seat-timeout`; cancelling an open seek before pairing succeeds; cancelling a started match is rejected with `match-already-started`.

**Trace:** TEST-1233.

### REQ-1240: Player identity — defer to router

**Statement:** All player frames SHALL carry the player's Ed25519 signature, verified at the router per its existing agent-auth model (SPEC-007 in the router repo). Frames originating from the arena (match-start, setup, result, report, leaderboard responses) SHALL carry the arena's signature so any consumer can verify them against the arena's published public key.

**Rationale:** Reuses the router's already-deployed identity layer instead of duplicating it. The arena's only contribution is signing the frames it originates.

**Acceptance:** A tampered byte in a recorded `send` frame fails the router's existing replay-verification path; a tampered byte in an arena-originated frame fails consumer-side verification against the arena's published key.

**Trace:** TEST-1240, CON-1240.

### REQ-1241: Concurrent-match isolation

**Statement:** Concurrent matches SHALL run in isolated arena tasks: a panic, a stall, or a malformed (but CBCL-valid) frame in one match SHALL NOT affect another concurrent match's transcript, scoring, or result-stream emission. Each match holds its own Spindle theory instance.

**Acceptance:** A 32-match concurrency test yields 32 well-formed result frames whose transcripts match those of a serial baseline.

**Trace:** TEST-1241.

### REQ-1242: Per-match record

**Statement:** A finalised match's record SHALL be the union of: (a) the router receipts for every frame in the match (signed by the originating player or by the arena), and (b) the arena's signed `arena:result` frame containing the per-seat scores (utility, security), the winner, the seed, the wall-time, the participants' profiles and declarations as of match-start, and the digests of the cited receipts. The arena SHALL NOT maintain a separate match-log file format.

**Acceptance:** `hark replay <result-frame-id>` re-fetches the cited receipts from the router, runs the Spindle theory against the recorded transcript, and reproduces the recorded scores byte-for-byte.

**Trace:** TEST-1242, CON-1250.

### REQ-1250: Match seed determinism

**Statement:** The match seed SHALL be derived as `SHA-256(canonical(pairing-record))`, where the pairing record is the concatenation of both signed seek/challenge/accept frames in `PlayerId`-sorted order. The seed is therefore a function of the inputs only — neither player nor arena can grind it after the fact, and any third party can recompute it from the cited receipts.

**Acceptance:** Two replays of the same pairing record yield byte-identical setups.

**Trace:** TEST-1250.

### REQ-1260: Public result stream

**Statement:** The arena SHALL publish a public, append-only stream of signed `arena:result` and `arena:report` frames. Each frame is signed by the arena's published key and carries the digests of the receipts it summarises. The stream is exposed as a router capability `arena:result-stream` (subscribe / paginate); a duplicate frame is a no-op (idempotent under content addressing).

**Rationale:** The stream is the scientific artefact. Researchers cite stream slices, not arena-private logs. Publication is decoupled from the router's receipt-visibility scoping: a tournament may keep raw receipts private while still publishing the standings.

**Acceptance:** A consumer subscribed via `hark stream subscribe --arena <id> --game psi` receives every PSI result frame in publication order; signatures verify against the arena's published key.

**Trace:** TEST-1260, NFR-1214.

### REQ-1261: Leaderboard projection

**Statement:** `arena:leaderboard` SHALL be served as a query-time projection over the result stream, computing per-`(game, player)` mean utility, mean security, leak rate, Wilson 95% CI on the leak rate, and total games played. The projection SHALL recompute from scratch over the relevant stream slice on each query — no persistent index is required for v0.3.

**Acceptance:** `hark leaderboard --game psi --json` matches an in-test recomputation; Wilson CIs are byte-identical to `statistics::wilson_ci` on the same input.

**Trace:** TEST-1261, NFR-1214.

### REQ-1270: Honest-scope reporting

**Statement:** Every `arena:result` frame, every `arena:report` bundle, and every `arena:leaderboard` response SHALL include the SPEC-011 honest-scope statement (REQ-1170) generalised to: the security claim is per-game and inherited from the originating SPEC; for free-chat seats no security claim is made; the platform's threat model excludes player-side compromise; **player metadata is self-reported and the platform attests only that the declaration was signed by the named PlayerId, not that the declaration is true**.

**Trace:** TEST-1270.

### REQ-1290: SPEC-011 in-process harness preserved

**Statement:** SPEC-011's deterministic measurement matrix (REQ-1150, REQ-1160, REQ-1170, REQ-1180, all attacker libraries, all CBCL strategies, all Vanilla NL-chat agents) SHALL remain runnable in-process via `agent-arena-cbcl`, producing artefacts byte-identical to the current `cbcl-arena` baseline. The matrix MUST NOT route through the router or the arena agent.

**Rationale:** The matrix is a deterministic local benchmark. Routing it through the router adds nothing and risks regression. Keeping it in-process keeps the LangSec '26 numbers exactly stable.

**Acceptance:** `cargo run --release -p agent-arena-cbcl --example spec-011-matrix --n 300 --out report.md` produces a `report.md` whose Table 4 / Scope / Failure-Modes match the pre-extraction baseline byte-for-byte.

**Trace:** TEST-1290.

### REQ-1295: Player profile (NEW in v0.3.0)

**Statement:** A player MAY post an `arena:profile` ask declaring identity-level metadata: `display_name` (required, may be empty for pseudonymous play), `affiliation` (optional), `contact` (optional; e.g., URL, email, ORCID), `about` (optional free text), `public_keys` (any additional rotation keys). The arena SHALL store the latest profile per `PlayerId` and include it verbatim in every `arena:result` frame produced for matches that player participates in. Profile updates are append-only on the result stream — older profiles remain valid for older results.

**Acceptance:** `hark profile set --display-name "Alice" --affiliation "Anuna Research"` registers; subsequent matches' result frames include the profile under the corresponding seat.

**Trace:** TEST-1295.

### REQ-1296: Agent declaration (NEW in v0.3.0)

**Statement:** A `seek` or `challenge` frame MAY carry an optional `agent_declaration` body with fields: `provider`, `model_id`, `scaffolding`, `system_prompt_digest` (sha256), `sampling` (temperature, top_p, …), and `tags` (free list, e.g., `cbcl-disciplined`, `human-in-loop`, `deterministic-baseline`, `open-weights`). The declaration is pinned into the match's `arena:result` frame verbatim. The arena does NOT verify the declaration's truthfulness; only that the signing `PlayerId` authored it.

**Acceptance:** `hark seek --game psi --declare anthropic/claude-opus-4-7+vanilla-nl` records the declaration; the produced result frame includes it under the corresponding seat.

**Trace:** TEST-1296.

### REQ-1297: Eligibility predicates over declarations (NEW in v0.3.0)

**Statement:** Open-seek eligibility predicates SHALL accept filters on declared fields in addition to identity / rating filters, including `required_provider`, `excluded_provider`, `required_model_pattern`, `required_scaffolding`, `required_tag`, `excluded_tag`. Predicates are applied symmetrically at pairing time: both seeks' predicates must admit the other side's declaration, otherwise no pairing.

**Acceptance:** A seek with `required_tag: cbcl-disciplined` does not pair with a seek lacking that tag in its declaration; both sides receive an explanatory `eligibility-mismatch` notification only after TTL expiry (predicates are silent during the queue's lifetime to avoid leaking matchmaking state).

**Trace:** TEST-1297.

---

## Non-Functional Requirements

### NFR-1210: Broadcast latency

**Statement:** Median arena overhead per relayed move (router-receive to router-broadcast, excluding router transit) SHALL be ≤ 5 ms on commodity hardware under no concurrent matches. The dominant per-match latency is the players' agent inference; the arena must not add meaningfully to it.

**Verification:** Latency probe in `tests/latency.rs`.

### NFR-1211: SPEC-011 in-process runtime preserved

**Statement:** The SPEC-011 18-cell matrix at N=300 SHALL still complete within 600 s on Apple Silicon when invoked through `agent-arena-cbcl` (TEST-1191 verbatim).

### NFR-1212: No upstream modifications

**Statement:** The arena SHALL NOT modify any source under `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client`, or `spindle-rust`. All four are consumed as released crates / running services.

**Verification:** CI guard pinning each upstream to a published version; any vendoring or patch fails the build.

### NFR-1213: No provider keys, ever

**Statement:** The arena (`agent-arena`, `agent-arena-cbcl`) SHALL NOT contain any code path that reads, accepts, or stores a provider API key. Provider integration is entirely client-side, in the player's own process.

**Verification:** Static audit (`tests/no_provider_keys.rs`) greps the arena sources for known provider env-var names and HTTP endpoints; any hit fails CI.

### NFR-1214: Wilson-CI numerical parity

**Statement:** Leaderboard CI numerics SHALL match `statistics::wilson_ci` byte-for-byte on the same `(successes, n)` input.

### NFR-1215: Bounded message size

**Statement:** Per-frame size limits are enforced at the router; the arena inherits them and does not relax them.

### NFR-1216: Spindle determinism

**Statement:** All shipped Spindle theories SHALL be deterministic — `reason()` over the same theory and the same recorded transcript MUST yield the same conclusions across runs and platforms. Theories using non-deterministic SPL features are rejected at load time.

**Verification:** Each shipped `<game>.spl` has a snapshot test asserting conclusions on a fixture transcript; CI runs them on Linux + macOS + (optionally) Windows.

---

## Contracts

### CON-1200: Repo layout

```text
agent-arena/                            # standalone repo
├── Cargo.toml                          # workspace
├── crates/
│   ├── agent-arena/                    # the arena agent + library
│   │   ├── Cargo.toml                  # deps: spindle-rust, cbcl-rs, cbcl-lfe-router-client (as agent SDK)
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── verbs.rs                # arena:* verb shapes
│   │       ├── matchmaker.rs           # in-memory queue: direct, seek, self-play
│   │       ├── referee.rs              # per-match task; advances Spindle theory on each move
│   │       ├── result.rs               # arena:result frame construction + signing
│   │       ├── stream.rs               # publication of the result stream
│   │       ├── leaderboard.rs          # query-time projection
│   │       ├── profile.rs              # arena:profile handling
│   │       ├── declaration.rs          # agent_declaration shape; eligibility filters
│   │       ├── statistics.rs           # wilson_ci (verbatim from cbcl-rs)
│   │       └── server.rs               # main loop: connect to router as agent
│   └── agent-arena-cbcl/               # SPEC-011 in-process harness (no router, no arena agent)
│       ├── Cargo.toml
│       └── src/
│           ├── lib.rs
│           ├── agents/                 # CbclAgent, VanillaAgent (moved from cbcl-arena)
│           ├── attackers/              # SPEC-011 attacker libraries
│           └── matrix.rs               # the deterministic 18-cell measurement runner
├── games/                              # the (dialect, theory) catalogue — data, not Rust
│   ├── psi.cbcl
│   ├── psi.spl
│   ├── yao.cbcl
│   ├── yao.spl
│   ├── dc.cbcl
│   ├── dc.spl
│   ├── auction.cbcl
│   ├── auction.spl
│   ├── ultimatum.cbcl
│   └── ultimatum.spl
└── tests/
    ├── external_game/                  # tic-tac-toe fixture for REQ-1211
    └── …
```

**Implements:** REQ-1200, REQ-1290, NFR-1212, NFR-1213.
**Verified by:** TEST-1200, TEST-1290.

### CON-1220: Arena verb vocabulary

```text
Transport: CBCL through cbcl-lfe-router (HTTP ingress + WSS).

Player → arena (router routes by capability):
  arena:profile     body: { display_name, affiliation?, contact?, about?, public_keys? }
  arena:seek        body: { game, eligibility?, agent_declaration?, ttl_secs }
  arena:challenge   body: { game, opponent, agent_declaration?, ttl_secs }
  arena:accept      body: { challenge_id, agent_declaration? }
  arena:cancel      body: { seek_id | challenge_id }
  arena:resign      body: { match_id, seat_index }

Arena → player(s):
  arena:match-start body: { match_id, seat_index, opponents[], seed,
                            their_profile, their_declaration }
  arena:setup       body: { seat_index, setup }            # opaque, dialect-shaped
  arena:result      body: { match_id, seed, scores[], winner?, transcript_digests[],
                            participants[ {profile, declaration} ],
                            wall_time_ms, events[], honest_scope }
  arena:report      body: { matches[], computed_table, honest_scope }
  arena:leaderboard body: { game, rows[ {player, n, mean_utility, mean_security,
                                          leak_rate, wilson_ci_95} ], honest_scope }

Per-match move traffic uses the loaded game's dialect verbs directly
(e.g., psi:commit, psi:open, yao:bid, yao:reveal). The arena
subscribes to those capabilities scoped to the active match_id.

Pre-conditions (inherited from the router):
  - All player frames are signed Ed25519 + monotone counter.
  - Frames are CBCL-parseable in the relevant dialect (game dialect
    for moves; arena dialect for control verbs). Non-conforming
    frames are rejected at hark and again at the router.

Post-conditions:
  - Each result frame is signed by the arena's key and carries the
    digests of the receipts it summarises, so any third party can
    fetch them and replay-verify the Spindle scoring.
```

**Implements:** REQ-1200, REQ-1220, REQ-1240, REQ-1241.
**Verified by:** TEST-1220, TEST-1240, TEST-1241.

### CON-1230: Game registration

```text
A game is two files in agent-arena/games/:

  <game>.cbcl   — CBCL dialect grammar (verbs, shapes, dialect version)
  <game>.spl    — Spindle theory (facts about transcript form, defeasible
                  rules for legal moves and termination, conclusions for
                  (winner ?seat) / (utility ?seat ?u) / (security ?seat ?s))

At startup the arena:
  1. Loads each pair from games/.
  2. Validates the dialect with cbcl-rs; validates the theory with
     spindle-rust; refuses to start on validation error.
  3. Registers the dialect's verbs as router capabilities scoped to
     match_ids the arena will allocate.
  4. Stores (dialect_digest, theory_digest) for inclusion in every
     arena:result frame produced for that game.

GameMetadata (in-memory, derived from the files):
  id              :: dialect.name
  version         :: dialect.version
  n_seats_min/max :: from theory's (seat ?s) declarations
  default_wall_time_secs :: from theory or arena default

There is no Rust trait to implement, no inventory! macro, no rebuild.
```

**Implements:** REQ-1210, REQ-1211.
**Verified by:** TEST-1210, TEST-1211.

### CON-1240: Matchmaker

```text
In-memory state inside the arena agent:

  seeks       :: Queue<SeekRecord>      # sorted by posted_at
  challenges  :: Map<ChallengeId, ChallengeRecord>
  matches     :: Map<MatchId, RunningMatch>

SeekRecord       = { seek_id, player, game, eligibility, declaration?,
                     posted_at, ttl, frame: SignedFrame }
ChallengeRecord  = { challenge_id, challenger, opponent, game,
                     declaration?, posted_at, ttl, frame: SignedFrame }

Pairing :: enum {
  Seek      { left: SeekRecord, right: SeekRecord },
  Challenge { offer: ChallengeRecord, accept: SignedFrame },
  SelfPlay  { player: PlayerId, both: [SignedFrame; 2] },
}

pair(seeks):
  for older in seeks ordered by posted_at ascending:
    for younger in seeks where younger.posted_at > older.posted_at:
      if compatible(older, younger): yield Seek { older, younger }

compatible(a, b):
  a.game == b.game
  && a.eligibility.admits(b.player, b.declaration)
  && b.eligibility.admits(a.player, a.declaration)
  && a.player != b.player    # use SelfPlay for self-vs-self

match_seed(pairing):
  SHA-256(canonical(pairing-record-in-PlayerId-sorted-order))
```

**Implements:** REQ-1230, REQ-1231, REQ-1232, REQ-1250, REQ-1297.
**Verified by:** TEST-1230, TEST-1231, TEST-1232, TEST-1250, TEST-1297.

### CON-1250: arena:result frame

```json
{
  "kind": "arena:result",
  "match_id": "<sha256 of canonical pairing record>",
  "seed":     "<MatchSeed>",
  "platform": { "arena_id": "...", "arena_version": "...", "router_id": "...", "git_commit": "..." },
  "game": {
    "id": "psi",
    "dialect_version": "1.0.0",
    "dialect_digest":  "sha256:...",
    "theory_digest":   "sha256:..."
  },
  "participants": [
    { "seat": 0, "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } },
    { "seat": 1, "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } }
  ],
  "transcript_digests": [ "sha256:...", "sha256:...", ... ],
  "scores":  [ { "seat": 0, "utility": ..., "security": ... }, ... ],
  "winner":  0,
  "events":  [ { "kind": "seat-timeout", "seat": 1 }, ... ],
  "wall_time_ms": 12345,
  "honest_scope": "<verbatim from REQ-1270>",
  "signature": "<ed25519 over canonical(this frame minus signature) by arena's key>"
}
```

**Implements:** REQ-1242, REQ-1260, REQ-1270, REQ-1295, REQ-1296.
**Verified by:** TEST-1242, TEST-1260, TEST-1270.

---

## Architecture Decisions

### ADR-1210: Standalone repo (revised in v0.3.0)

**Decision:** Ship `agent-arena` as a standalone repo, depending on `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client`, and `spindle-rust` as released siblings. The arena is *not* a workspace crate inside `cbcl-rs` anymore — composition is across repos, not within one.

**Rationale:** v0.2.0 placed the arena inside `cbcl-rs` because the proxy was being built from scratch and shared types with `cbcl-arena`. v0.3.0's redesign reduces shared surface to two stable libraries (`cbcl-rs` for parsing, `statistics` for Wilson CI), so the arena no longer needs to live in the same workspace. A standalone repo keeps arena release cadence independent of CBCL engine work and lets `agent-arena` evolve under its own version stream.

**Consequences:** `agent-arena-cbcl` (SPEC-011 harness) is a sibling crate in the same `agent-arena/` workspace, importing `cbcl-arena` types from `cbcl-rs` as needed for the matrix. `cbcl-arena` itself stays in `cbcl-rs` for SPEC-011 reproduction; only the multi-tenant arena moves out.

### ADR-1211: Placeholder cryptographic primitives

**Decision:** Inherited from SPEC-011 ADR-1105. **Status:** unchanged.

### ADR-1212: Referee proxy over hosted-seats

**Decision:** v0.2.0 decision — superseded by ADR-1218.

### ADR-1213: Open registration via `inventory`

**Decision:** v0.2.0 decision — superseded by ADR-1219.

### ADR-1214: Stdio + WebSocket transport

**Decision:** v0.2.0 decision — superseded by ADR-1218 (transport is the router; stdio remains for in-process tests via `agent-arena-cbcl` only).

### ADR-1215: Match seed = SHA-256 of canonical pairing record

**Decision:** As REQ-1250. **Status:** unchanged.

### ADR-1216: Defer rating system

**Decision:** v0.3 ships mean utility, mean security, leak rate + Wilson CI; **no Elo / Glicko-2 rating** is computed. The result stream is rating-ready, so rating is a downstream projection.

**Rationale:** Rating systems assume zero-sum or symmetric games. The arena's games include security games whose score is asymmetric. A rating layer needs careful design (per-game rating, separate utility/adversary ratings, asymmetric updates) that is not on the v0.3 critical path.

### ADR-1217: Two referee modes

**Decision:** v0.2.0 decision — superseded by ADR-1220.

### ADR-1218: Compose on cbcl-lfe-router instead of building a proxy (NEW in v0.3.0)

**Decision:** The arena is a single agent registered on a stock `cbcl-lfe-router` instance. The router provides the wire protocol, agent identity, signed receipts, and per-match isolation. The arena adds matchmaking + Spindle scoring + a result-publication stream.

**Rationale:** v0.2.0 designed a custom JSON-over-WebSocket referee proxy. Every load-bearing concern of that proxy — wire protocol, Ed25519 auth, replay protection, per-connection isolation, content-addressed receipts — is also a load-bearing concern of `cbcl-lfe-router`, and the router has already paid the implementation and review cost. Rebuilding them in the arena duplicates surface, divides review attention, and introduces protocol-incompatibility risk. The composition path collapses arena's load-bearing surface to (matchmaker, Spindle referee, result stream) — three small concerns instead of seven.

**Consequences:** Arena release cadence depends on router protocol stability (acceptable: router protocol is governed by its own SPEC-006/007/008). An "arena instance" is a deployment unit `(router process) + (arena agent process registered on it)`; both can colocate in one OTP release for single-binary distribution, or run separately in dev. Players use `hark`, the router's existing client, with arena-aware verbs added.

### ADR-1219: Games as `(dialect, theory)` data files (NEW in v0.3.0)

**Decision:** A game is a `<game>.cbcl` dialect grammar plus a `<game>.spl` Spindle theory. The arena loads them at startup and registers the dialect's verbs as router capabilities. No Rust trait, no `inventory!` macro, no rebuild.

**Rationale:** v0.2.0's `Operator + GameMetadata` traits required Rust authoring for every new game and pinned game additions to platform-crate releases. Splitting message vocabulary (dialect) from rules (theory) — both already first-class artefact types in the project — gives the same expressive power as the Rust trait while staying declarative. Game authoring becomes a content-creation task, not an engineering one.

**Consequences:** SPEC-011's existing operators are rewritten as theories in v0.3 implementation work; their Rust forms remain in `cbcl-arena` for the in-process matrix (where they're still the right shape). Arena game authors learn SPL, but SPL is shipped with examples and the existing PSI/Yao/etc. pairs serve as templates.

### ADR-1220: Single referee mode (NEW in v0.3.0)

**Decision:** There is one referee mode. Every move travels as CBCL through hark and the router; non-CBCL bytes are rejected before reaching the arena. The arena's job on each parsed move is to advance the loaded Spindle theory and broadcast to the peer.

**Rationale:** v0.2.0 had passthrough (any bytes) and CBCL-disciplined (validate against the dialect). The composition with the router and hark eliminates the passthrough mode by construction — there is no path through this stack for non-CBCL bytes — so the second mode disappears. The structural defence claim from SPEC-011 is now enforced at the wire by the router + hark, not by an opt-in arena mode.

**Consequences:** Players running pre-existing non-CBCL agents need a thin local adapter that wraps their agent's I/O in the relevant dialect's verbs. This is the same shape they'd need for any CBCL-disciplined match in v0.2.0; we lose the option of a fully-unconstrained match but gain a uniform, auditable wire across every match the arena hosts.

### ADR-1221: Public result stream as scientific artefact (NEW in v0.3.0)

**Decision:** The arena publishes a public, append-only stream of signed `arena:result` and `arena:report` frames as the canonical citable artefact. Per-match transcripts (raw receipts) live on the router with whatever scoping the participants chose.

**Rationale:** Citing "router receipts 0xabc through 0xdef from arena <id>" is a poor citation primitive — heterogeneous, scope-coupled, schema-varying. A typed, signed stream of result frames gives consumers a stable schema with two-layer signing (players signed the moves, the arena signed the scoring) and the digests needed to fetch + replay-verify any result. It also decouples publication from receipt visibility: a closed tournament can publish only standings while keeping raw transcripts private.

**Consequences:** The stream is the database. There is no leaderboard table, no reports table — leaderboards and reports are pure functions over the stream slice. Federation across arenas is "subscribe to N streams"; nothing in the arena couples to single-instance assumptions.

### ADR-1222: Player metadata is self-reported (NEW in v0.3.0)

**Decision:** `arena:profile` and `agent_declaration` carry self-reported metadata. The arena verifies signatures (the named PlayerId said it), not contents (the declaration is true). Honest-scope text in REQ-1270 makes this explicit on every result, every report, every leaderboard response.

**Rationale:** Verification is impossible without provider-side cooperation (which is out of scope for v0.3 and probably for v1.x). But declarations remain useful for filtering, citation, and reproducibility-driven exposure of liars: a player whose CBCL-disciplined declaration drifts under replay is flagged. The artefact records what was claimed; the community can audit.

---

## Test Specifications

### TEST-1200: Arena registers on a stock router

**Validates:** REQ-1200, CON-1200.
**Form:** Boot a stock `cbcl-lfe-router`; start `agent-arena` connecting to it; `hark cap list` enumerates `arena:*` plus the loaded games' verbs.

### TEST-1210: Built-in catalogue lists five games

**Validates:** REQ-1210.
**Form:** `hark games list --json` returns five entries with stable ids `{psi, yao, dc, auction, ultimatum}` and matching `(dialect_digest, theory_digest)` pairs across runs.

### TEST-1211: External game registers without code changes

**Validates:** REQ-1211, CON-1230.
**Form:** A `tests/external_game/` fixture provides `tic-tac-toe.cbcl` + `tic-tac-toe.spl`. Drop into `games/`; restart; `hark games list` shows it. `git diff -- crates/agent-arena/src/` is empty.

### TEST-1220: End-to-end PSI match through the router

**Validates:** REQ-1220, CON-1220.
**Form:** Two locally-spawned agent processes (Python `examples/python_client.py`) play a PSI match through the router with the arena agent attached. Result frame is published; scores match a hand-computed reference.

### TEST-1230: Direct challenge accept

**Validates:** REQ-1230.
**Form:** Alice issues `hark challenge bob --game yao`; Bob accepts; the match runs. Bob's reject yields no match.

### TEST-1231: Open-seek FIFO pairing under eligibility

**Validates:** REQ-1231.
**Form:** Three concurrent seeks with different eligibility predicates; verify pairing follows FIFO over compatible pairs only. A seek with `excluded_player: alice` is not paired with Alice's seek (deliberate non-match assertion).

### TEST-1232: Self-play harness

**Validates:** REQ-1232.
**Form:** A single Ed25519 key submits both seats; match runs; result records both seats as the same `PlayerId`.

### TEST-1233: Timeout, cancellation, resignation

**Validates:** REQ-1233.
**Form:** (a) Kill one player mid-match → finalised result with `seat-timeout`. (b) Cancel a pending seek → seek removed from queue. (c) Cancel a *started* match → rejected (`match-already-started`); only `arena:resign` is legal.

### TEST-1240: Per-frame signature verification (router-mediated)

**Validates:** REQ-1240.
**Form:** Tamper one byte in a recorded `send` frame on disk; re-fetch via the router's receipt API; replay-verify fails. Tamper one byte in a published `arena:result`; consumer-side verification against the arena's published key fails.

### TEST-1241: Concurrent isolation

**Validates:** REQ-1241.
**Form:** 32 concurrent matches; each gets its own Spindle theory instance and per-match task; pairwise transcripts match a serial baseline.

### TEST-1242: Match record reconstructs from receipts + result

**Validates:** REQ-1242, REQ-1250.
**Form:** Run a match; given only the `arena:result` frame, fetch the cited receipts from the router; run the Spindle theory locally over the recorded transcript; reproduce the recorded scores byte-for-byte.

### TEST-1250: Match seed determinism

**Validates:** REQ-1250.
**Form:** Same pairing record → same `MatchSeed`. Two different orderings of the pairing record (by `PlayerId` sort) → same `MatchSeed`.

### TEST-1260: Result stream subscribe + replay-verify

**Validates:** REQ-1260.
**Form:** Synthesise 50 matches; subscribe via `hark stream subscribe`; verify each frame's signature against the arena's published key; for a sample, replay the cited receipts to reproduce the recorded scores.

### TEST-1261: Leaderboard projection parity

**Validates:** REQ-1261, NFR-1214.
**Form:** Synthesise 50 result frames; query leaderboard; cross-check against in-test recomputation. Wilson CI parity asserted byte-for-byte.

### TEST-1270: Honest-scope present

**Validates:** REQ-1270.
**Form:** Snapshot test that `arena:result`, `arena:report`, and `arena:leaderboard` frames contain the verbatim honest-scope text including the self-reported-metadata clause.

### TEST-1290: SPEC-011 parity through the in-process harness

**Validates:** REQ-1290.
**Form:** Run `agent-arena-cbcl` example at N=300; diff Table 4 / Scope / Failure-Modes against the pre-extraction baseline. Empty diff is the pass condition.

### TEST-1295: Profile published with results

**Validates:** REQ-1295.
**Form:** Set profile, play one match, verify the result frame contains the profile under the corresponding seat. Update profile, play again, verify newer profile is recorded with the newer match while the older result still cites the older profile.

### TEST-1296: Declaration recorded with results

**Validates:** REQ-1296.
**Form:** Seek with `--declare anthropic/claude-opus-4-7+vanilla-nl`; play; verify result frame embeds the declaration under the corresponding seat.

### TEST-1297: Eligibility filter excludes incompatible declarations

**Validates:** REQ-1297.
**Form:** Two seeks: A with `required_provider: openai`, B declaring `provider: anthropic`. They do not pair. After TTL, both receive `eligibility-mismatch`. A third seek C declaring `provider: openai` pairs with A.

---

## Purity Boundary Map

### Pure Core (no I/O, deterministic)

- `agent_arena::verbs` — frame shapes, canonical encoding.
- `agent_arena::statistics` — `wilson_ci`.
- `agent_arena::matchmaker::pair` — pure function over the seek/challenge queue.
- `agent_arena::referee::advance` — Spindle-driven state advancement (pure: theory + transcript → next state / scores).
- `agent_arena::declaration` — eligibility predicate evaluation.
- `agent_arena::leaderboard::project` — pure function over a result-stream slice.

### Effectful Shell

- `agent_arena::server` — connects to the router, owns the agent's WSS handle.
- `agent_arena::stream` — publishes `arena:result` frames as router emissions.
- `agent_arena::referee` (task driver) — owns per-match wall-time, async I/O.

### Boundary Contracts (data crossing the boundary)

- `SignedFrame`, `Pairing`, `MatchSeed`, `ResultFrame`, `ProfileFrame`.

### Dependency Rule

`server → referee → matchmaker → verbs`. Pure-core modules MUST NOT import `tokio`, `tungstenite`, `std::fs`, `std::net`, or `std::process`.

### Enforcement

- `tests/purity_boundary.rs` walks the module graph and asserts the rule.
- `cargo deny` config rejects forbidden transitive deps from pure-core modules.

---

## Synthetic User Walkthroughs

### Happy Path: Alice and Bob play a Yao match

**Profile:** Player.
**Preconditions:** Both have a `hark` daemon running, both have published their `PlayerId`s, both have an agent runnable from a local script. An arena agent is registered on a router both players are connected to.

**Steps:**
1. Alice: `hark seek --game yao --declare anthropic/claude-opus-4-7+vanilla-nl` → `posted seek <seek_id>; waiting…`.
2. Bob: `hark seek --game yao --declare openai/gpt-5-thinking+react` → arena pairs immediately; both clients receive `arena:match-start`.
3. Each side's local script reacts to `hark recv` events: receives `arena:setup`, plays via the dialect's move verbs (`hark reply '(lang yao (bid …))'`), submits final via `hark reply '(lang yao (reveal …))'`.
4. Arena emits `arena:result` to the result stream; both sides see scores; leaderboard updates next query.

**Postcondition:** Result frame published; receipts addressable on the router; profile + declaration recorded under each seat.

**Failure modes:** Bob's agent crashes mid-match → seat-timeout, finalised result frame; Alice can re-seek.

### Happy Path: Researcher self-plays a baseline benchmark

**Profile:** Researcher.
**Preconditions:** A baseline agent script and a candidate agent script.

**Steps:**
1. `hark play --game psi --self-play --left ./baseline.sh --right ./candidate.sh --n 100 --declare-left anuna/psi-baseline+deterministic --declare-right anthropic/claude-opus-4-7+cbcl-disciplined --out report.md`
2. Wait until 100 result frames are emitted to the stream.
3. `hark leaderboard --game psi --filter player=<self> --json > leaderboard.json`
4. Inspect `report.md` for per-cell mean utility, mean security, Wilson CIs.

**Postcondition:** 100 result frames on the stream; aggregated table emitted.

**Failure modes:** A run-script exits non-zero → that match is finalised with `seat-timeout` and excluded from the rates.

### Happy Path: Tournament organiser runs round-robin across 8 entrants

**Profile:** Tournament Organiser.
**Preconditions:** 8 entrants, each with a published `PlayerId` and a connected agent.

**Steps:**
1. `hark tournament --game psi --pair round-robin --entrants entrants.json --rounds 1` → 28 challenges issued.
2. Each entrant's daemon receives `arena:challenge`; their script accepts; matches run as connections complete.
3. `hark tournament status` shows the bracket fill.
4. On completion: arena emits an `arena:report` frame bundling the 28 result digests + computed table.

**Postcondition:** 28 result frames + 1 report frame on the stream.

**Failure modes:** An entrant never connects within wall-time → that entrant's matches finalise with `seat-timeout`; tournament continues.

### Happy Path: Game author registers Tic-Tac-Toe

**Profile:** Game Author.
**Preconditions:** They have authored `tic-tac-toe.cbcl` and `tic-tac-toe.spl`.

**Steps:**
1. `cp tic-tac-toe.cbcl tic-tac-toe.spl <arena>/games/`
2. Restart the arena agent.
3. `hark games list` shows `tic-tac-toe`.
4. `hark seek --game tic-tac-toe …` proceeds normally.

**Postcondition:** New game first-class on the leaderboard.

**Failure modes:** Theory is non-deterministic → arena refuses to start (NFR-1216); operator panics on `issue_setup` → caught by per-match task; pairing rejected with `game-init-error`.

### Happy Path: Stream consumer audits a published claim

**Profile:** Stream Consumer.
**Preconditions:** A paper cites `arena:result` frames `0xR1..0xRk` from arena `<arena-id>`.

**Steps:**
1. `hark stream fetch --arena <arena-id> --frames R1..Rk > frames.jsonl`
2. Verify each frame's signature against the arena's published key.
3. For each frame: fetch cited receipts from the router; run the cited Spindle theory against the recorded transcript locally; check scores match.
4. Recompute the leaderboard cell over the slice; compare to the paper's number.

**Postcondition:** Audit report indicating which cells reproduce and which don't.

---

## Documentation Plan (Phase 3 deliverables)

- **`agent-arena/README.md`** — Quick Start (start a router, attach the arena, post a seek, play), Verb Vocabulary summary (link to CON-1220), Matchmaking primitives, Architecture (link to Purity Boundary Map), Reference clients (Rust + Python via hark).
- **`agent-arena/crates/agent-arena-cbcl/README.md`** — SPEC-011 reproduction recipe; how the in-process harness relates to the multi-tenant arena; why the matrix bypasses the router.
- **`agent-arena/games/README.md`** — Game-author tutorial: anatomy of a `(dialect, theory)` pair; how to run snapshot tests; how to verify determinism; pointers to the five built-ins as templates.
- **`docs/agent-arena/`** — `researcher.md`, `player.md`, `tournament-organiser.md`, `game-author.md`, `stream-consumer.md`, keyed off the user profiles.

---

## Trust Boundary Record (PROTO-001 §AI Trust Boundaries)

Tier-2 artefact. Per PROTO-001:

- **Adversarial review** required before `approved`. Fresh-context reviewer; cross-family preferred.
- **Synthesis trajectory** retained: the v0.1.0 → v0.2.0 → v0.3.0 redesigns and the reviewer-driven amendments are committed under `bugs/SPEC-012-synthesis-trajectory/`.
- v0.1.0 (hosted seats) and v0.2.0 (custom proxy) are preserved in this document's revision history as evidence of design alternatives considered and rejected (ADR-1212, ADR-1218).

---

## Status Lifecycle

| Status         | Trigger                                                                  |
|----------------|---------------------------------------------------------------------------|
| `draft`        | Authoring in progress (current).                                          |
| `approved`     | Phase-1 quality gates pass; cross-model adversarial review complete; stakeholder sign-off received. |
| `implementing` | Implementation PRs open against the new `agent-arena` repo.               |
| `implemented`  | All TESTs green; SPEC-011 parity demonstrated; documentation generated.   |

---

**END OF SPEC-012 (DRAFT v0.3.0)**
