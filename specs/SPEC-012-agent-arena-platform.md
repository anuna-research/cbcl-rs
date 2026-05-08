---
id: SPEC-012
title: Agent Arena — Composable Referee on cbcl-lfe-router with Spindle Game Theories
status: draft
version: 0.3.1
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
  - 0.3.0 (2026-05-08) — composable redesign: arena is an *agent on cbcl-lfe-router*, not a service. Games are `(CBCL dialect, Spindle theory)` data pairs. Single referee mode (CBCL-disciplined by construction). Public signed `arena:result` stream as scientific artefact. Player profile + agent declaration added (ADR-1218 through ADR-1222).
  - 0.3.1 (2026-05-08) — multiplayer + live game teaching. Lobbies replace 2-player challenges as the matchmaking primitive (challenge becomes degenerate 2P sugar). Seat roles declared by the theory. Game registration is live via `arena:register-game` — no restart, no file watching required for new games. Dialect propagates to participants at match-start by content digest. Catalogue is now a stream projection just like the leaderboard. Federation across arenas falls out (ADR-1223, ADR-1224, ADR-1225).
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
| Version        | 0.3.1                                                                |
| Date           | 2026-05-08                                                           |
| Author         | Anuna Research                                                       |
| Audience       | Engineering (composition + game authoring)                           |
| Methodology    | PROTO-001 USDD Agent Protocol v1.4.0                                 |
| Tier           | 2 (multi-tenant; signed messages and signed result/catalogue streams)|

---

## Overview

`cbcl-arena` (SPEC-011) is a deterministic local simulator: one process, one seed, one Wilson CI per cell. That shape is correct for the LangSec '26 paper and stays as-is for that use case (`agent-arena-cbcl` in-process harness, REQ-1290).

This specification covers the second use case — **N players, sitting at different machines, each running their own agent (any provider, any scaffolding, even non-LLM), wanting to play PSI / Yao / DC / Auction / Ultimatum (or a game they've just authored) and have the result count.** v0.2.0 attempted this with a custom JSON-over-WebSocket referee proxy. v0.3.x observes that **every load-bearing concern of that proxy already has a sibling project that solves it cleanly**, and recomposes the arena as a thin agent over them:

| Concern                | v0.2.0                                | v0.3.x                                                                 |
|------------------------|---------------------------------------|------------------------------------------------------------------------|
| Wire protocol          | Custom JSON frames                    | CBCL through `cbcl-lfe-router`; arena registers `arena:*` capabilities |
| Player identity / sigs | Custom Ed25519 + per-frame signing    | Router's existing Ed25519 agent auth                                   |
| Player CLI             | New `arena` binary                    | `hark` (router-client) extended with arena verbs                       |
| Game definition        | `Operator + GameMetadata` Rust trait  | Two data files / two stream frames: `(dialect grammar, Spindle theory)` |
| Referee mode           | Passthrough vs CBCL-disciplined       | Single mode — CBCL-disciplined by construction                         |
| Match log              | Custom JSON file                      | Router receipts + signed `arena:result` frame                          |
| Public artefact        | Implicit                              | Signed `arena:result` *stream*; leaderboard is a projection over it    |
| Game catalogue         | Compile-time `inventory!` registration| Signed `arena:game-registered` stream; live, p2p-teachable; no restart |
| Match shape            | 2-player only                         | N-player lobbies; theory declares seat roles; 2P is the degenerate case|

The thesis is **architectural compression**: the arena's load-bearing surface reduces to (a) a multi-seat lobby + queue matchmaker, (b) a Spindle-driven referee that advances per-match state on each parsed message, (c) two append-only signed streams (results, catalogue). Everything else is reused.

**Federation falls out.** Both streams are signed, content-addressed, and carry their own provenance. A second arena subscribed to a first arena's catalogue stream sees new game registrations and adopts them locally; subscribed to its result stream, it can include those matches in its own leaderboard projection without any pairwise coordination. A "union arena" is just a downstream subscriber doing more folds.

The thesis is **not** a security claim about CBCL; that argument is owned by SPEC-011 and survives because the deterministic measurement matrix is *not* routed through the router. The matrix stays in-process in `agent-arena-cbcl`, byte-identical to today.

### Design Provenance

**SPEC-011 operators → Spindle theories.** Each existing operator's scoring logic is rewritten as an SPL theory: facts for the recorded transcript, defeasible rules for legal moves and termination, conclusions for `(winner ?seat)` / `(utility ?seat ?u)` / `(security ?seat ?s)`. `reason()` is deterministic forward-chaining; the referee never needs an LLM-as-judge for the v0.3 catalogue.

**cbcl-lfe-router as transport.** Capability-keyed routing, Ed25519 agent authentication, content-addressed signed receipts, per-WebSocket isolation. The arena registers as one more agent and plugs in.

**Hark as player CLI — generic, no arena coupling.** `hark recv` / `hark reply` is already the player-side idiom for talking to any router agent, and stays exactly that. The arena's verbs are CBCL bodies (`(lang arena (seek :game psi …))`) that flow through hark as opaque payloads — hark does not need to learn a single new verb to support the arena. An optional `arena` companion binary may ship in this repo for ergonomics (composing common frames, watching for `arena:match-start`, etc.), but it talks to the same hark daemon and is not load-bearing for the spec — every workflow below is also expressible as raw `hark reply` calls.

**CBCL homoiconicity.** A CBCL dialect grammar is itself a CBCL term in the meta-dialect-of-dialects. So a player can *say* a new dialect to the arena rather than ship a file — the same property that lets agents teach each other vocabulary lets players teach the platform new games. Live registration is the natural fit for a homoiconic substrate, not a bolt-on.

### Scope

This specification covers:

- A standalone Rust crate `agent-arena` exposing the arena agent (matchmaker + Spindle referee + result-stream + catalogue-stream publishers) and a small library reused by `agent-arena-cbcl`.
- The arena's CBCL verb vocabulary (`arena:profile`, `arena:seek`, `arena:lobby`, `arena:join-lobby`, `arena:close-lobby`, `arena:cancel`, `arena:resign`, `arena:register-game`, `arena:fetch-dialect`, `arena:fetch-theory`, `arena:match-start`, `arena:setup`, `arena:result`, `arena:report`, `arena:leaderboard`, `arena:games`, `arena:game-registered`).
- Three matchmaking primitives generalised to N seats: **lobby** (multi-seat, named or open invitations), **open seek queue** (FIFO over the oldest compatible group of N), **self-play** (one PlayerId submitting all N seats).
- Theory-declared seat roles (e.g., Auction = `{auctioneer: 1, bidder: 3..M}`; DC = `{participant: 3..12}`).
- A built-in catalogue of five reference games as `(dialect, theory)` pairs: PSI, Yao, DC, Auction, Ultimatum. The catalogue is bootstrapped from `games/` files at startup AND is extensible at runtime via `arena:register-game`.
- Live game registration with content-addressed `(dialect_digest, theory_digest)` identity; deterministic-validation gate; per-PlayerId rate limiting.
- Dialect propagation: at `arena:match-start` the arena names the dialect+theory by digest; participants whose hark daemons don't yet know the dialect fetch it from the arena (or any peer) by digest.
- Player profile (durable, per `PlayerId`) and agent declaration (per match) frames.
- Eligibility predicates over both rating and declarations.
- A signed, append-only `arena:result` publication stream as the scientific artefact.
- A signed, append-only `arena:game-registered` publication stream as the catalogue artefact.
- Query-time leaderboard and catalogue projections over the streams, with Wilson 95% CIs from `statistics::wilson_ci`.
- An *optional* thin `arena` companion CLI (in the agent-arena repo) that wraps common player flows by composing CBCL frames and calling the same `hark` daemon — `hark` itself remains generic and gains no arena-specific verbs.
- Preservation of SPEC-011's in-process deterministic harness.

This specification does **not** cover:

- Hosting players' LLMs, scaffolding, or provider keys (NFR-1213).
- A skill-rating system (Elo, Glicko-2). Streams are rating-ready (REQ-1260) but rating math is future work (ADR-1216).
- A web UI — `hark` is the interface; a UI may consume the streams later.
- Real-money or stake-based betting.
- Cryptographic privacy of game contents (operators use the project's canonical-hash placeholder, ADR-1211).
- LLM-as-judge games (out of scope for v0.3.x catalogue; future games would register a separate `judge:assess` agent).
- Modifications to `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client`, or `spindle-rust` (NFR-1212).

---

## User Profiles

> **Note on workflow snippets.** The `hark <verb>` shorthands shown below (e.g., `hark seek`, `hark lobby`, `hark register-game`, `hark stream subscribe`) are illustrative — they refer to either (a) the optional `arena` companion CLI shipped in this repo, or (b) a one-line shell wrapper around `hark reply '(lang arena (…))'`. `hark` itself is the generic router-client and gains no arena-specific verbs; the load-bearing surface is always raw CBCL frames through `hark reply` / `hark recv`. See *Synthetic User Walkthroughs* for the raw form.

### User: Researcher

**Role:** Reproduce or extend a published claim about live-LLM agent behaviour in strategic-communication games.
**Goals:** Run their own agent against a baseline; benchmark across providers; replay a published match from the result stream.
**Constraints:** Reproducibility from receipts + result frame is non-negotiable; declarations must travel with results.
**Workflow:** `hark play --game psi --self-play --left ./my-agent.sh --right ./baseline.sh --n 100 --declare anthropic/claude-opus-4-7+vanilla`.

### User: Player

**Role:** Builder pitting their own agent against another player's, in 2-player or N-player games.
**Goals:** Issue a direct lobby (named opponents) or post an open seek and wait; play; see their score.
**Constraints:** Will not give the platform an API key. Wants their agent to keep running on their own machine. May want pseudonymity.
**Workflow:** `hark seek --game yao` / `hark seek --game dc --role participant` / `hark lobby --game auction --role auctioneer --invite alice,bob,carol`.

### User: Tournament Organiser

**Role:** Run a scheduled tournament across N submitted agents on 2-player or N-player games.
**Goals:** Pair every entrant against every other entrant on a fixed game (round-robin / group-stage / ladder); aggregate; publish a signed `arena:report` bundle.
**Constraints:** Must complete in bounded wall-clock time; cancellations of stalled matches must not deadlock the bracket.
**Workflow:** `hark tournament --game psi --shape round-robin --entrants entrants.json` (2P) or `hark tournament --game dc --shape group-stage --group-size 5 --rounds 4` (N≥3).

### User: Game Author

**Role:** Implement a new game and have it hosted.
**Goals:** Author `<game>.cbcl` (dialect grammar) and `<game>.spl` (Spindle theory); submit live; matches available immediately on every subscribed arena.
**Constraints:** No platform-crate modification, no Rust required, no admin handshake.
**Workflow:** `hark register-game --dialect tic-tac-toe.cbcl --theory tic-tac-toe.spl` → arena validates determinism, signs `arena:game-registered`, the catalogue projection picks it up next query.

### User: Stream Consumer

**Role:** Third-party researcher, journalist, or auditor reading the public `arena:result` and `arena:game-registered` streams without participating.
**Goals:** Filter results by game / provider / scaffolding / date; recompute leaderboards locally; verify per-match Spindle scoring against the cited receipts; audit which games are registered, by whom, with which signing key.
**Constraints:** Only needs the stream URLs and the players' / arena's public keys.
**Workflow:** `hark stream subscribe --arena <id> --kind result --game psi | jq …`; `hark stream subscribe --arena <id> --kind catalogue | …`.

### User: SPEC-011 Maintainer

**Role:** Operate the LangSec '26 deterministic measurement matrix.
**Goals:** Continue producing Demo 3's Table 4 from a single reproducible run; lose nothing in the extraction.
**Constraints:** Wall-time ≤ 600 s at N=300; identical numerics; matrix MUST NOT route through the router.
**Workflow:** `cargo run --release -p agent-arena-cbcl --example spec-011-matrix --n 300 --out report.md`.

---

## Threat Model

### TM-1201: Adversary capabilities

The adversary may be: (a) a player whose agent tries to cheat, exfiltrate, or DoS; (b) a network attacker between a player and the router; (c) a co-resident match on the same arena agent; (d) a malicious matchmaker submission (replay, forged challenge, lobby flood); (e) a malicious *game-registration* submission (dialect-bomb, non-deterministic theory, name-collision spam); (f) a stream consumer trying to forge results.

The adversary may:

- Send any *CBCL-valid* sequence in the relevant dialect.
- Drop or stall their connection at any point.
- Submit forged or replayed seek/lobby/join envelopes via WSS or HTTP ingress.
- Run any agent locally (any provider, any scaffolding, any tool-shimming).
- Lie about their declared provider / model / scaffolding.
- Submit dialect/theory pairs of arbitrary (but bounded-size) form to `arena:register-game`.

The adversary may NOT:

- Forge another player's signature on a frame.
- Submit non-CBCL bytes through the stack.
- Read another concurrent match's transcript.
- Modify the arena's Spindle scoring (pure function of recorded transcript).
- Touch another player's API keys.
- Forge a result-stream or catalogue-stream frame from a non-arena key.
- Cause the arena to load a non-deterministic theory (rejected at submission time).
- Register games at unbounded rate (per-PlayerId rate limit).

### TM-1202: Threat instances

| Threat | Defence | REQ |
|--------|---------|-----|
| Player connection drops mid-match | Per-match wall-time budget; on timeout, finalise with `seat-timeout` event | REQ-1233 |
| Forged challenge / lobby / seek | Router-level Ed25519 signature + monotone per-player counter | REQ-1240 |
| Player sends non-conforming bytes | Rejected at hark; rejected again at router; never reaches arena | (by construction) |
| One player's panic affects another concurrent match | Per-match isolation: own task, own theory instance, own buffers | REQ-1241 |
| Replay of a finalised match to drift the leaderboard | Stream is append-only; leaderboard recomputes from stream slice; duplicates are no-ops | REQ-1260 |
| Player lies about declared provider/model | Honest-scope statement; reproducibility audits expose drift | REQ-1270, REQ-1296 |
| Forged result-stream frame | Each frame signed by the arena's published key | REQ-1260 |
| Non-deterministic theory submitted | Rejected at submission via spindle-rust's determinism check | NFR-1216 |
| Dialect-registration flood (DoS) | Per-PlayerId rate limit on `arena:register-game`; rejected over quota | NFR-1217 |
| Two dialects with the same name but different bodies | Identity is `(name, digest)`; `hark seek --dialect-digest <hash>` disambiguates | REQ-1212 |
| Adversarial dialect that's pathologically slow to parse | Submission-time parse + parse-time fuel limit; reject on overrun | NFR-1217 |

---

## Functional Requirements

### REQ-1200: Arena agent on cbcl-lfe-router

**Statement:** The arena SHALL run as a single agent registered on a `cbcl-lfe-router` instance, exposing the capabilities `arena:profile`, `arena:seek`, `arena:lobby`, `arena:join-lobby`, `arena:close-lobby`, `arena:cancel`, `arena:resign`, `arena:register-game`, `arena:fetch-dialect`, `arena:fetch-theory`, `arena:games`, `arena:leaderboard`, and the per-game move/setup/result verbs derived from each loaded dialect (e.g., `psi:commit`, `psi:open`, `yao:bid`, `yao:reveal`, `dc:announce`). The arena SHALL NOT modify the router; it is one more agent on a stock router instance.

**Acceptance:** Starting a stock router and connecting the arena agent makes the arena's capabilities resolvable via `hark cap list`.

**Trace:** TEST-1200, CON-1220.

### REQ-1210: Built-in game catalogue

**Statement:** The arena SHALL bootstrap with five reference games as `(dialect, theory)` pairs — PSI (`{a:1, b:1}`), Yao's Millionaire (`{a:1, b:1}`), Dining Cryptographers (`{participant: 3..12}`), Sealed-Bid Auction (`{auctioneer:1, bidder: 2..M}`), Ultimatum (`{proposer:1, responder:1}`) — each consisting of a `<game>.cbcl` dialect file and a `<game>.spl` Spindle theory file under `games/`, registered at startup via the same code path as `arena:register-game` (so the bootstrap registrations also produce `arena:game-registered` stream frames).

**Acceptance:** `hark games list` enumerates the five with their dialect versions, theory digests, and seat-role declarations.

**Trace:** TEST-1210, CON-1230.

### REQ-1211: Live game registration (no restart)

**Statement:** Adding a new game SHALL be possible at runtime without restarting the arena. Submission via `arena:register-game` carrying the dialect grammar (a CBCL term in the meta-dialect-of-dialects) and the SPL theory triggers the arena to: (1) parse the dialect against the meta-dialect, (2) load the theory in spindle-rust and run its determinism check (NFR-1216), (3) verify that the theory's `(seat ?role ?n)` declarations are consistent with the dialect's role vocabulary, (4) emit a signed `arena:game-registered` frame to the catalogue stream, (5) register the dialect's verbs as router capabilities. A submission whose `(name, dialect_digest, theory_digest)` triple is already registered is a no-op (idempotent).

**Acceptance:** A `tic-tac-toe` registration via `hark register-game` is reflected in `hark games list` immediately, with no arena restart and no source-code change. `git diff -- crates/agent-arena/src/` is empty.

**Trace:** TEST-1211, TEST-1212, CON-1230.

### REQ-1212: Catalogue stream

**Statement:** The arena SHALL publish a public, append-only stream of signed `arena:game-registered` frames, each carrying the registering `PlayerId`, the full dialect grammar, the full SPL theory, the `(name, dialect_digest, theory_digest)` triple, and the registering arena's signature. The catalogue (queryable via `arena:games`) SHALL be a projection over this stream, recomputed at query time. A duplicated frame is a no-op (idempotent under content addressing).

**Rationale:** Symmetric with the result stream (REQ-1260). Federation falls out: a second arena subscribed to the catalogue stream sees new registrations and adopts them locally without coordination.

**Acceptance:** `hark stream subscribe --arena <id> --kind catalogue` receives every `arena:game-registered` frame in publication order; signatures verify against the arena's published key. A second arena subscribed to the stream auto-adopts registrations.

**Trace:** TEST-1212, CON-1220.

### REQ-1213: Dialect propagation at match-start

**Statement:** Every `arena:match-start` frame SHALL include the `(name, dialect_digest, theory_digest)` triple identifying the game. A participant whose hark daemon does not yet have the cited dialect SHALL be able to fetch its grammar and the theory body from the arena (or any peer) via `arena:fetch-dialect <digest>` / `arena:fetch-theory <digest>`. Hark caches fetched content by digest; subsequent matches in the same dialect skip the fetch. Content addressing makes the fetch verifiable independent of the source.

**Acceptance:** A first-time match in a freshly-registered dialect causes participating hark daemons to fetch the dialect once; replay shows the dialect served correctly; cache prevents the second match in that dialect from re-fetching.

**Trace:** TEST-1213, CON-1220.

### REQ-1220: Wire protocol — defer to router

**Statement:** All player↔arena and player↔player communication SHALL travel as CBCL frames through the router using its existing protocol. The arena's contribution to the wire is the *vocabulary* (the `arena:*` verbs and the loaded games' dialect verbs), not a new transport.

**Acceptance:** A standard router instance with the arena agent attached carries a complete N-player match end-to-end without any custom transport code in the arena.

**Trace:** TEST-1220, CON-1220.

### REQ-1230: Matchmaking — direct lobby (and 2-player challenge as degenerate case)

**Statement:** A player MAY post an `arena:lobby` ask declaring the game, the seat-count target `k` (within the theory's declared `n_seats_min..n_seats_max`), an optional list of named invitees per role, an optional `agent_declaration`, and a TTL. The arena holds the lobby until either (a) all seats are filled (auto-start), or (b) the initiator posts `arena:close-lobby` with current participants ≥ `n_seats_min` (manual start), or (c) TTL expires (cancel + notify). Other players join via `arena:join-lobby` naming the lobby id and the role they want; the arena fills role slots in submission order subject to per-role caps. On start, every seat receives `arena:match-start`. A 2-player direct challenge is the degenerate case `k=2, invitees=[opponent], auto-start on accept`; CLI alias `hark challenge` is provided as sugar.

**Acceptance:** `hark lobby --game auction --role auctioneer --seats 4` posts an open lobby; three other players post `hark join --lobby <id> --role bidder`; auto-start fires; match runs to completion. `hark challenge bob --game yao` runs the 2-player path identically.

**Trace:** TEST-1230, TEST-1234.

### REQ-1231: Matchmaking — open seek queue (N-player)

**Statement:** A player MAY post an `arena:seek` ask declaring the game, the role they want, eligibility predicates, and an optional `agent_declaration`. The arena SHALL pair a *role-compatible group of size n_seats_min..n_seats_max* (the theory's declaration) using FIFO order on the oldest seek; on pairing, all participants receive `arena:match-start`. Pairing is a small set-cover: greedy by oldest seek, then fill remaining roles from the queue under symmetric eligibility. Predicates evaluated pairwise across the full group.

**Acceptance:** Three concurrent `dc` seeks (role `participant`) are paired into a single 3-seat match. A fourth seek with `excluded_player: alice` is not paired into a group containing Alice. A `required_provider: openai` seek does not pair with `provider: anthropic` seeks.

**Trace:** TEST-1231.

### REQ-1232: Matchmaking — self-play (N-player)

**Statement:** A single player MAY post all N seats of a match (`arena:seek --self-play --seats k` with k distinct seat declarations under the same `PlayerId`, or N independent connections by the same key labelled with distinct seat indices). The arena treats the seats as independent counterparties for the duration of the match.

**Acceptance:** A researcher script connecting once with the same Ed25519 key and posting a self-play envelope for `dc` with 3 seats yields a complete 3-seat match transcript and result frame.

**Trace:** TEST-1232.

### REQ-1233: Match timeout, cancellation, resignation

**Statement:** Every match SHALL have a per-match wall-time budget (default 5 min, configurable per game and per match). On timeout, the arena finalises the match with the recorded transcript and a `seat-timeout` event for each unresponsive seat, then posts `arena:result`. Either a lobby's initiator MAY cancel a *pending* lobby; any seek-poster MAY cancel their *unpaired* seek; once the match is started, no unilateral cancellation — only `arena:resign`, which finalises with that seat's utility = 0 and security per the Spindle theory.

**Acceptance:** Killing one player mid-match yields a finalised result with `seat-timeout` for that seat; the others' scores reflect the truncated transcript per the theory. Cancelling a pending lobby succeeds; cancelling a started match is rejected.

**Trace:** TEST-1233.

### REQ-1234: Multi-seat lobbies and seat roles

**Statement:** Theories SHALL declare seat roles as `(seat ?role ?min ?max)` triples. The arena SHALL respect role demand at lobby formation: a lobby for `auction` requires exactly `(auctioneer 1 1)` and `(bidder 2 M)`; a join request for an over-capped role is rejected with `role-full`. `arena:match-start` carries each seat's role assignment; the dialect verbs may be role-scoped (e.g., only `auctioneer` may post `auction:open`; only `bidder` may post `auction:bid`). Symmetric games (DC, PSI, Yao) declare a single role with min=max=N.

**Acceptance:** An auction lobby with 1 auctioneer + 3 bidders auto-starts; a join request as a fifth bidder when max=3 is rejected; the resulting match-start frames each carry a role assignment.

**Trace:** TEST-1234, CON-1230.

### REQ-1240: Player identity — defer to router

**Statement:** All player frames SHALL carry the player's Ed25519 signature, verified at the router per its existing agent-auth model. Frames originating from the arena (match-start, setup, result, report, leaderboard responses, `arena:game-registered`) SHALL carry the arena's signature so any consumer can verify them against the arena's published public key.

**Acceptance:** A tampered byte in a recorded `send` frame fails the router's existing replay-verification path; a tampered byte in an arena-originated stream frame fails consumer-side verification.

**Trace:** TEST-1240, CON-1240.

### REQ-1241: Concurrent-match isolation

**Statement:** Concurrent matches SHALL run in isolated arena tasks: a panic, a stall, or a malformed (but CBCL-valid) frame in one match SHALL NOT affect another concurrent match's transcript, scoring, or stream emissions. Each match holds its own Spindle theory instance. Lobby + queue state is shared but read-mostly under per-operation locking.

**Acceptance:** A 32-match concurrency test (mix of 2P and N≥3 matches) yields 32 well-formed result frames whose transcripts match those of a serial baseline.

**Trace:** TEST-1241.

### REQ-1242: Per-match record

**Statement:** A finalised match's record SHALL be the union of: (a) the router receipts for every frame in the match (signed by the originating player or the arena), and (b) the arena's signed `arena:result` frame containing the per-seat scores, role assignments, the winner (or null for non-winner-takes-all games), the seed, the wall-time, the participants' profiles and declarations as of match-start, the `(dialect_digest, theory_digest)` of the game version played, and the digests of the cited receipts. The arena SHALL NOT maintain a separate match-log file format.

**Acceptance:** `hark replay <result-frame-id>` re-fetches the cited receipts, runs the cited theory locally over the recorded transcript, and reproduces the recorded scores byte-for-byte.

**Trace:** TEST-1242, CON-1250.

### REQ-1250: Match seed determinism

**Statement:** The match seed SHALL be derived as `SHA-256(canonical(pairing-record))`, where the pairing record is the concatenation of all signed seek/lobby/join frames in `PlayerId`-then-seat-index sorted order. The seed is therefore a function of the inputs only.

**Acceptance:** Two replays of the same pairing record yield byte-identical setups.

**Trace:** TEST-1250.

### REQ-1260: Public result stream

**Statement:** The arena SHALL publish a public, append-only stream of signed `arena:result` and `arena:report` frames. Each is signed by the arena's published key and carries the digests of the receipts it summarises. Exposed as router capability `arena:result-stream` (subscribe / paginate); duplicates are no-ops.

**Acceptance:** A consumer subscribed via `hark stream subscribe --arena <id> --kind result --game psi` receives every PSI result frame in publication order; signatures verify.

**Trace:** TEST-1260, NFR-1214.

### REQ-1261: Leaderboard projection

**Statement:** `arena:leaderboard` SHALL be served as a query-time projection over the result stream, computing per-`(game, role, player)` mean utility, mean security, leak rate, Wilson 95% CI, and total games played. The projection recomputes from scratch over the relevant stream slice on each query.

**Acceptance:** `hark leaderboard --game psi --json` matches an in-test recomputation; Wilson CIs are byte-identical to `statistics::wilson_ci` on the same input.

**Trace:** TEST-1261, NFR-1214.

### REQ-1270: Honest-scope reporting

**Statement:** Every `arena:result`, `arena:report`, `arena:leaderboard`, and `arena:game-registered` frame SHALL include the SPEC-011 honest-scope statement (REQ-1170) generalised to: the security claim is per-game and inherited from the originating SPEC; for free-chat seats no security claim is made; the platform's threat model excludes player-side compromise; **player metadata and game-registration metadata are self-reported and the platform attests only that the declaration was signed by the named PlayerId, not that the declaration is true**.

**Trace:** TEST-1270.

### REQ-1290: SPEC-011 in-process harness preserved

**Statement:** SPEC-011's deterministic measurement matrix SHALL remain runnable in-process via `agent-arena-cbcl`, producing artefacts byte-identical to the current `cbcl-arena` baseline. The matrix MUST NOT route through the router or the arena agent.

**Acceptance:** `cargo run --release -p agent-arena-cbcl --example spec-011-matrix --n 300 --out report.md` produces a `report.md` whose Table 4 / Scope / Failure-Modes match the pre-extraction baseline byte-for-byte.

**Trace:** TEST-1290.

### REQ-1295: Player profile

**Statement:** A player MAY post an `arena:profile` ask declaring identity-level metadata: `display_name` (required, may be empty for pseudonymous play), `affiliation` (optional), `contact` (optional), `about` (optional free text), `public_keys` (any additional rotation keys). The arena SHALL store the latest profile per `PlayerId` and include it verbatim in every `arena:result` frame produced for matches that player participates in. Profile updates are append-only on the result stream.

**Acceptance:** `hark profile set --display-name "Alice" --affiliation "Anuna Research"` registers; subsequent matches' result frames include the profile under the corresponding seat.

**Trace:** TEST-1295.

### REQ-1296: Agent declaration

**Statement:** A `seek`, `lobby`, or `join-lobby` frame MAY carry an optional `agent_declaration` body with fields: `provider`, `model_id`, `scaffolding`, `system_prompt_digest` (sha256), `sampling`, `tags` (free list). Pinned to the match's `arena:result` frame verbatim. The arena does NOT verify truthfulness; only that the signing `PlayerId` authored it.

**Acceptance:** `hark seek --game psi --declare anthropic/claude-opus-4-7+vanilla-nl` records the declaration; the result frame includes it under the corresponding seat.

**Trace:** TEST-1296.

### REQ-1297: Eligibility predicates over declarations

**Statement:** Open-seek and join-lobby eligibility predicates SHALL accept filters on declared fields: `required_provider`, `excluded_provider`, `required_model_pattern`, `required_scaffolding`, `required_tag`, `excluded_tag`. Predicates applied symmetrically across all participants of a multi-seat group; both sides' predicates must admit the other side's declaration.

**Acceptance:** A seek with `required_tag: cbcl-disciplined` does not pair into a group containing seeks lacking that tag. After TTL, the unpaired seeker receives `eligibility-mismatch`.

**Trace:** TEST-1297.

---

## Non-Functional Requirements

### NFR-1210: Broadcast latency

**Statement:** Median arena overhead per relayed move (router-receive to router-broadcast, excluding router transit) SHALL be ≤ 5 ms on commodity hardware under no concurrent matches.

**Verification:** `tests/latency.rs`.

### NFR-1211: SPEC-011 in-process runtime preserved

**Statement:** The SPEC-011 18-cell matrix at N=300 SHALL still complete within 600 s on Apple Silicon when invoked through `agent-arena-cbcl`.

### NFR-1212: No upstream modifications

**Statement:** The arena SHALL NOT modify any source under `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client`, or `spindle-rust`.

**Verification:** CI guard pins each upstream to a published version; vendoring or patching fails the build.

### NFR-1213: No provider keys, ever

**Statement:** The arena SHALL NOT contain any code path that reads, accepts, or stores a provider API key.

**Verification:** Static audit (`tests/no_provider_keys.rs`).

### NFR-1214: Wilson-CI numerical parity

**Statement:** Leaderboard CI numerics SHALL match `statistics::wilson_ci` byte-for-byte.

### NFR-1215: Bounded message size

**Statement:** Per-frame size limits enforced at the router; the arena inherits and does not relax them.

### NFR-1216: Spindle determinism (load + submission gate)

**Statement:** All theories — bootstrapped from `games/` AND submitted via `arena:register-game` — SHALL pass spindle-rust's determinism check before being registered. Theories using non-deterministic SPL features are rejected. The same check is run at theory load (startup bootstrap) and at submission (live `arena:register-game`); the arena MUST NOT serve matches in a non-deterministic theory.

**Verification:** Each shipped `<game>.spl` has a snapshot test asserting conclusions on a fixture transcript; CI runs them on Linux + macOS. Submission-path tests assert that crafted non-deterministic theories are rejected.

### NFR-1217: Registration rate limiting

**Statement:** `arena:register-game` SHALL be rate-limited per `PlayerId`: default 5 successful registrations per hour, 20 per day; failed-validation submissions count toward a separate quota of 20/hour to prevent compute-DoS via bad submissions. Limits are configurable per arena instance. Excess submissions are rejected with `rate-limited` and a retry-after timestamp. Dialect parsing and theory loading run under a per-submission fuel limit; submissions exceeding it are rejected with `submission-overran`.

**Verification:** `tests/registration_rate_limit.rs` asserts both quotas; a fuzz test with adversarial dialects asserts the fuel limit terminates parsing.

---

## Contracts

### CON-1200: Repo layout

```text
agent-arena/                            # standalone repo
├── Cargo.toml                          # workspace
├── crates/
│   ├── agent-arena/                    # the arena agent + library
│   │   ├── Cargo.toml                  # deps: spindle-rust, cbcl-rs, cbcl-lfe-router-client
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── verbs.rs                # arena:* verb shapes
│   │       ├── matchmaker.rs           # in-memory queue + lobbies; N-player pairing
│   │       ├── lobby.rs                # multi-seat lobby state machine
│   │       ├── referee.rs              # per-match task; advances Spindle theory on each move
│   │       ├── result.rs               # arena:result frame construction + signing
│   │       ├── catalogue.rs            # arena:game-registered + projection
│   │       ├── registration.rs         # validate + load (dialect, theory); rate limit
│   │       ├── stream.rs               # publication of result + catalogue streams
│   │       ├── leaderboard.rs          # query-time projection
│   │       ├── profile.rs              # arena:profile handling
│   │       ├── declaration.rs          # agent_declaration + eligibility filters
│   │       ├── statistics.rs           # wilson_ci (verbatim from cbcl-rs)
│   │       └── server.rs               # main loop: connect to router as agent
│   └── agent-arena-cbcl/               # SPEC-011 in-process harness
│       ├── Cargo.toml
│       └── src/
│           ├── lib.rs
│           ├── agents/
│           ├── attackers/
│           └── matrix.rs
├── games/                              # bootstrap (dialect, theory) catalogue
│   ├── psi.cbcl       psi.spl
│   ├── yao.cbcl       yao.spl
│   ├── dc.cbcl        dc.spl           # 3..12 participants
│   ├── auction.cbcl   auction.spl      # 1 auctioneer + 2..M bidders
│   └── ultimatum.cbcl ultimatum.spl
└── tests/
    ├── external_game/                  # tic-tac-toe fixture for live registration test
    └── …
```

**Implements:** REQ-1200, REQ-1290, NFR-1212, NFR-1213.
**Verified by:** TEST-1200, TEST-1290.

### CON-1220: Arena verb vocabulary

```text
Transport: CBCL through cbcl-lfe-router.

Player → arena:
  arena:profile         body: { display_name, affiliation?, contact?, about?, public_keys? }
  arena:seek            body: { game, role?, eligibility?, agent_declaration?, ttl_secs }
  arena:lobby           body: { game, seats, invitees?[ {player, role} ],
                                agent_declaration?, ttl_secs, auto_start? }
  arena:join-lobby      body: { lobby_id, role, agent_declaration? }
  arena:close-lobby     body: { lobby_id }                       # initiator only; manual start
  arena:cancel          body: { seek_id | lobby_id }
  arena:resign          body: { match_id, seat_index }
  arena:register-game   body: { name, dialect: <CBCL term>, theory: <SPL term> }
  arena:fetch-dialect   body: { digest }                         # → arena:dialect (full grammar)
  arena:fetch-theory    body: { digest }                         # → arena:theory  (full SPL)

Arena → player(s):
  arena:lobby-update    body: { lobby_id, participants, missing_roles, ttl_remaining }
  arena:match-start     body: { match_id, seat_index, role, opponents[ {player, seat, role} ],
                                seed, game: { name, dialect_digest, theory_digest },
                                their_profile, their_declaration }
  arena:setup           body: { seat_index, setup }              # opaque, dialect-shaped
  arena:result          body: { match_id, seed, scores[], winner?, role_assignments[],
                                participants[ {profile, declaration} ],
                                game: { dialect_digest, theory_digest },
                                transcript_digests[], wall_time_ms, events[], honest_scope }
  arena:report          body: { matches[], computed_table, honest_scope }
  arena:leaderboard     body: { game, role?, rows[ {player, n, mean_utility, mean_security,
                                                     leak_rate, wilson_ci_95} ], honest_scope }

Arena → catalogue stream:
  arena:game-registered body: { name, dialect_digest, theory_digest, dialect, theory,
                                registrar_player_id, registrar_signature, arena_signature,
                                seat_roles[ {role, min, max} ], honest_scope }

Per-match move traffic uses the loaded game's dialect verbs directly
(e.g., psi:commit, dc:announce, auction:bid). The arena subscribes to
those capabilities scoped to the active match_id.

Pre-conditions (inherited from the router):
  - All player frames signed Ed25519 + monotone counter.
  - Frames are CBCL-parseable in the relevant dialect.

Post-conditions:
  - Each result frame and each game-registered frame is signed by the
    arena's key and carries the digests of the content it summarises.
```

**Implements:** REQ-1200, REQ-1212, REQ-1213, REQ-1220, REQ-1230, REQ-1240.
**Verified by:** TEST-1212, TEST-1213, TEST-1220, TEST-1230, TEST-1240.

### CON-1230: Game registration (bootstrap and live)

```text
A game is two artefacts:

  <game>.cbcl   — CBCL dialect grammar with verbs, shapes, version,
                  and a (seat-roles ((role min max) ...)) clause.
  <game>.spl    — Spindle theory: facts about transcript form,
                  defeasible rules for legal moves and termination,
                  conclusions for (winner ?seat) / (utility ?seat ?u) /
                  (security ?seat ?s).

Two registration paths (same code path internally):

  (1) Bootstrap from files: at startup, for each (dialect, theory) pair
      under games/, the arena calls registration::submit() with the
      arena's own PlayerId as the registrar. Successful registrations
      emit arena:game-registered to the catalogue stream, just like
      live registrations.

  (2) Live via arena:register-game: any signed submission, validated
      under NFR-1216 + NFR-1217, then registered identically.

registration::submit(name, dialect, theory, registrar):
  1. parse dialect against meta-dialect (cbcl-rs); reject on parse err.
  2. compute (dialect_digest, theory_digest).
  3. if (name, dialect_digest, theory_digest) already in catalogue: idempotent return.
  4. spindle-rust load theory; run determinism check; reject on non-determinism.
  5. extract seat_roles from theory's (seat ?role ?min ?max) clauses.
  6. cross-check seat_roles against dialect's (seat-roles ...) clause; reject mismatch.
  7. emit signed arena:game-registered to catalogue stream.
  8. register dialect verbs as router capabilities scoped to match_ids.

GameMetadata (in-memory, projected from the catalogue stream):
  id              :: dialect.name
  version         :: dialect.version
  dialect_digest  :: sha256
  theory_digest   :: sha256
  seat_roles      :: [(role, min, max)]
  default_wall_time_secs :: from theory or arena default

There is no Rust trait to implement, no inventory! macro, no rebuild.
The bootstrap-from-files path is provided for convenience and for
deterministic test fixtures; the live submission path is the
load-bearing one for federation.
```

**Implements:** REQ-1210, REQ-1211, REQ-1212, REQ-1234, NFR-1216, NFR-1217.
**Verified by:** TEST-1210, TEST-1211, TEST-1212, TEST-1234.

### CON-1240: Matchmaker

```text
In-memory state inside the arena agent:

  seeks       :: Queue<SeekRecord>            # sorted by posted_at
  lobbies     :: Map<LobbyId, LobbyRecord>
  matches     :: Map<MatchId, RunningMatch>
  catalogue   :: Map<(name, dialect_digest, theory_digest), GameMetadata>

SeekRecord   = { seek_id, player, game, role, eligibility, declaration?, posted_at, ttl, frame }
LobbyRecord  = { lobby_id, initiator, game, seat_demand: Map<role, (filled, max)>,
                 invitees?, declarations: Map<seat, declaration>, posted_at, ttl,
                 auto_start: bool, frames: Vec<SignedFrame> }

Pairing :: enum {
  Group     { participants: Vec<SeekRecord> },     # N seats from seeks
  Lobby     { record: LobbyRecord },               # named-or-open lobby fully filled
  SelfPlay  { player: PlayerId, frames: Vec<SignedFrame> },
}

pair_from_seeks(seeks, catalogue):
  // Greedy by oldest seek; fill remaining roles from queue under symmetric
  // eligibility. Cheap at queue sizes <100; brute force is fine.
  for older in seeks ordered by posted_at ascending:
    g = catalogue.get(older.game)
    if can_form_group(older, seeks, g.seat_roles):
      yield Group { participants }

can_form_group(seed, queue, seat_roles):
  for each (role, min, max) in seat_roles:
    fill from queue by role, in posted_at order, only if all-pairs eligibility holds;
    if filled count is not in [min, max]: cannot form.

match_seed(pairing):
  SHA-256(canonical(pairing-record-in-PlayerId-then-seat-index-sorted-order))
```

**Implements:** REQ-1230, REQ-1231, REQ-1232, REQ-1234, REQ-1250, REQ-1297.
**Verified by:** TEST-1230, TEST-1231, TEST-1232, TEST-1234, TEST-1250, TEST-1297.

### CON-1250: arena:result frame

```json
{
  "kind": "arena:result",
  "match_id": "<sha256 of canonical pairing record>",
  "seed":     "<MatchSeed>",
  "platform": { "arena_id": "...", "arena_version": "...", "router_id": "...", "git_commit": "..." },
  "game": {
    "name": "auction",
    "dialect_version": "1.0.0",
    "dialect_digest":  "sha256:...",
    "theory_digest":   "sha256:..."
  },
  "participants": [
    { "seat": 0, "role": "auctioneer", "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } },
    { "seat": 1, "role": "bidder",     "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } },
    { "seat": 2, "role": "bidder",     "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } },
    { "seat": 3, "role": "bidder",     "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } }
  ],
  "transcript_digests": [ "sha256:...", "sha256:...", ... ],
  "scores":  [ { "seat": 0, "utility": ..., "security": ... }, ... ],
  "winner":  null,
  "events":  [ { "kind": "seat-timeout", "seat": 2 }, ... ],
  "wall_time_ms": 12345,
  "honest_scope": "<verbatim from REQ-1270>",
  "signature": "<ed25519 over canonical(this frame minus signature) by arena's key>"
}
```

**Implements:** REQ-1234, REQ-1242, REQ-1260, REQ-1270, REQ-1295, REQ-1296.
**Verified by:** TEST-1242, TEST-1260, TEST-1270.

---

## Architecture Decisions

### ADR-1210: Standalone repo

**Decision:** Ship `agent-arena` as a standalone repo, depending on `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client`, and `spindle-rust` as released siblings. Status: unchanged from v0.3.0.

### ADR-1211: Placeholder cryptographic primitives

**Decision:** Inherited from SPEC-011 ADR-1105. Status: unchanged.

### ADR-1212: Referee proxy over hosted-seats

**Decision:** v0.2.0 — superseded by ADR-1218.

### ADR-1213: Open registration via `inventory`

**Decision:** v0.2.0 — superseded by ADR-1219, then by ADR-1223.

### ADR-1214: Stdio + WebSocket transport

**Decision:** v0.2.0 — superseded by ADR-1218.

### ADR-1215: Match seed = SHA-256 of canonical pairing record

**Decision:** As REQ-1250. Status: unchanged.

### ADR-1216: Defer rating system

**Decision:** v0.3.x ships mean utility, mean security, leak rate + Wilson CI. No Elo / Glicko-2.

### ADR-1217: Two referee modes

**Decision:** v0.2.0 — superseded by ADR-1220.

### ADR-1218: Compose on cbcl-lfe-router instead of building a proxy

**Decision:** As v0.3.0. Status: unchanged.

### ADR-1219: Games as `(dialect, theory)` data

**Decision:** As v0.3.0. Status: unchanged in spirit; ADR-1223 adds the live-registration path.

### ADR-1220: Single referee mode

**Decision:** As v0.3.0. Status: unchanged.

### ADR-1221: Public result stream as scientific artefact

**Decision:** As v0.3.0. Status: unchanged.

### ADR-1222: Player metadata is self-reported

**Decision:** As v0.3.0. Status: unchanged.

### ADR-1223: Catalogue is a stream projection (NEW in v0.3.1)

**Decision:** Game registrations are signed `arena:game-registered` frames on a public, append-only catalogue stream. The in-memory catalogue is a projection over the stream. The bootstrap-from-files path runs through the same submission code path; bootstrap and live registrations are indistinguishable downstream.

**Rationale:** Symmetric with the result-stream model (ADR-1221). It gives federation for free — a second arena subscribed to a first arena's catalogue stream adopts new registrations locally without a coordination protocol. It removes the "restart to add a game" friction. And it puts game authoring on the same artefact-citation footing as match results: "this paper uses theory `<digest>` registered by `<PlayerId>` on `<arena>` at `<timestamp>`" is a one-line citation.

**Consequences:** The bootstrap files in `games/` are convenience, not load-bearing. A from-scratch arena could be empty and have its catalogue grow purely from live submissions and federated subscriptions. Determinism + quota gating (NFR-1216, NFR-1217) become load-bearing because they're now the only thing standing between a malicious submitter and arena state.

### ADR-1224: Lobbies as the matchmaking primitive (NEW in v0.3.1)

**Decision:** The matchmaking primitives are *lobby* (multi-seat with optional named invitees), *open seek* (FIFO queue of role-tagged seeks paired into N-element groups), and *self-play* (one PlayerId fills all N seats). 2-player direct challenge is the degenerate `lobby with one named invitee, auto-start on accept`; `hark challenge` remains as a CLI alias.

**Rationale:** v0.3.0's challenge/accept primitive only fit 2-player matches. Promoting lobbies to the primitive handles N-seat games (DC, Auction, future) without a special case, and the 2P case stays ergonomic at the CLI. Roles are declared by the theory, evaluated by the matchmaker, and propagated to participants in `arena:match-start` — players know what role they're playing before they receive setup.

**Consequences:** Wire vocabulary gains `arena:lobby` / `arena:join-lobby` / `arena:close-lobby` / `arena:lobby-update` and drops `arena:challenge` / `arena:accept` from the protocol (CLI alias preserved). The pairing function becomes a small set-cover problem; greedy by oldest seek is sufficient at expected queue sizes.

### ADR-1225: Dialect propagation by content digest (NEW in v0.3.1)

**Decision:** `arena:match-start` carries the `(name, dialect_digest, theory_digest)` triple. Participants whose hark daemons don't know the dialect fetch by digest via `arena:fetch-dialect` / `arena:fetch-theory`; hark caches by digest. Verifiability is content-addressed and source-independent.

**Rationale:** Live registration (ADR-1223) means a player may participate in a game registered five minutes ago that their daemon has never seen. Pushing the dialect at match-start is wasteful for known dialects (the common case); naming by digest with on-demand fetch is the cache-friendly default. Content addressing makes the fetch verifiable: any peer can serve the dialect, the player verifies the digest, no chain-of-trust on the source.

**Consequences:** Hark gains a content-addressed dialect cache. The arena exposes `arena:fetch-dialect` and `arena:fetch-theory` as router capabilities so any participant (and any third-party stream consumer) can re-materialise a dialect from its digest. This is also what makes the catalogue stream a complete artefact: the stream frames themselves carry the dialect+theory bodies, so a stream consumer never needs to ask the original arena for them either.

---

## Test Specifications

### TEST-1200: Arena registers on a stock router

**Validates:** REQ-1200.
**Form:** Boot a stock router; start arena; `hark cap list` enumerates `arena:*` plus the loaded games' verbs.

### TEST-1210: Built-in catalogue lists five games with seat roles

**Validates:** REQ-1210.
**Form:** `hark games list --json` returns five entries with stable ids `{psi, yao, dc, auction, ultimatum}`, matching `(dialect_digest, theory_digest)` pairs across runs, and seat-role declarations matching the spec (PSI/Yao/Ultimatum 2P; DC 3..12; Auction 1+2..M).

### TEST-1211: Live game registration without restart

**Validates:** REQ-1211.
**Form:** Start arena with the five built-ins. `hark register-game --dialect tic-tac-toe.cbcl --theory tic-tac-toe.spl` while running. `hark games list` shows `tic-tac-toe` immediately. Subsequent `hark seek --game tic-tac-toe` proceeds. `git diff -- crates/agent-arena/src/` is empty.

### TEST-1212: Catalogue stream + federation

**Validates:** REQ-1212, ADR-1223.
**Form:** Arena A registers `tic-tac-toe`. Arena B subscribes to A's catalogue stream via `hark stream subscribe --kind catalogue`. Arena B's local catalogue updates; `hark seek --arena B --game tic-tac-toe` proceeds without re-registration on B. Each catalogue frame's signature verifies against A's published key; tampered frames fail.

### TEST-1213: Dialect propagation at match-start

**Validates:** REQ-1213, ADR-1225.
**Form:** Player C has never seen dialect `tic-tac-toe`. C's hark cache is empty. C joins a `tic-tac-toe` lobby; on `arena:match-start`, hark fetches the dialect by digest from the arena, verifies the digest, caches, and proceeds. A second tic-tac-toe match for C does not re-fetch. A tampered fetch response is rejected by digest mismatch.

### TEST-1220: End-to-end PSI match through the router

**Validates:** REQ-1220.
**Form:** Two locally-spawned agent processes play a PSI match through a stock router with the arena attached. Result frame is published; scores match a hand-computed reference.

### TEST-1230: 2-player lobby (challenge alias)

**Validates:** REQ-1230.
**Form:** `hark challenge bob --game yao` (lobby with one named invitee, auto-start). Bob accepts via `hark join`. Match runs to completion. Same result frame structure as a queue-paired match.

### TEST-1231: N-player open-seek FIFO pairing under eligibility

**Validates:** REQ-1231.
**Form:** Three concurrent `dc` seeks (role `participant`) → 3-seat match. Four concurrent `auction` seeks (1 auctioneer, 3 bidders) → 4-seat match. Eligibility predicates correctly exclude incompatible groups.

### TEST-1232: N-player self-play

**Validates:** REQ-1232.
**Form:** A single Ed25519 key submits 3 seats for `dc`. Match runs; result records all three seats as the same `PlayerId` with distinct seat indices.

### TEST-1233: Timeout, cancellation, resignation

**Validates:** REQ-1233.
**Form:** (a) Kill one player mid-N-player match → finalised result with `seat-timeout` for that seat; theory's scoring on the truncated transcript determines others' scores. (b) Cancel a pending lobby → lobby removed. (c) Cancel a *started* match → rejected.

### TEST-1234: Multi-seat lobby with seat roles

**Validates:** REQ-1234.
**Form:** `hark lobby --game auction --role auctioneer --seats 4`; three `hark join --role bidder` calls succeed; a fourth join as `bidder` is rejected with `role-full`. Auto-start fires when seat-demand met. Match-start frames carry role assignments. The dialect rejects an `auction:bid` from the auctioneer seat (role-scoped verb).

### TEST-1240: Per-frame signature verification

**Validates:** REQ-1240.
**Form:** Tamper one byte in a recorded `send` frame; replay-verify fails. Tamper one byte in a published `arena:result`; consumer-side verification fails. Tamper one byte in a published `arena:game-registered`; consumer-side verification fails.

### TEST-1241: Concurrent isolation across mixed match shapes

**Validates:** REQ-1241.
**Form:** 32 concurrent matches mixing 2P, 3P, and 4P games; pairwise transcripts match a serial baseline; no cross-talk.

### TEST-1242: Match record reconstructs from receipts + result

**Validates:** REQ-1242, REQ-1250.
**Form:** Run a match; given only the `arena:result` frame, fetch the cited receipts; run the cited theory locally over the recorded transcript; reproduce scores byte-for-byte.

### TEST-1250: Match seed determinism

**Validates:** REQ-1250.
**Form:** Same pairing record → same `MatchSeed`. Different orderings of the pairing record → same `MatchSeed`.

### TEST-1260: Result stream subscribe + replay-verify

**Validates:** REQ-1260.
**Form:** Synthesise 50 matches; subscribe via `hark stream subscribe --kind result`; verify each frame's signature; for a sample, replay cited receipts to reproduce scores.

### TEST-1261: Leaderboard projection parity

**Validates:** REQ-1261, NFR-1214.
**Form:** Synthesise 50 result frames; query leaderboard; cross-check vs in-test recomputation; Wilson CIs byte-identical.

### TEST-1270: Honest-scope present

**Validates:** REQ-1270.
**Form:** Snapshot test that `arena:result`, `arena:report`, `arena:leaderboard`, and `arena:game-registered` frames contain the verbatim honest-scope text.

### TEST-1290: SPEC-011 parity through the in-process harness

**Validates:** REQ-1290.
**Form:** Run `agent-arena-cbcl` example at N=300; diff Table 4 / Scope / Failure-Modes against the pre-extraction baseline; empty diff is the pass condition.

### TEST-1295: Profile published with results

**Validates:** REQ-1295.
**Form:** Set profile, play one match, verify the result frame contains the profile under the corresponding seat. Update profile, play again, verify newer profile is recorded with the newer match while older results still cite the older profile.

### TEST-1296: Declaration recorded with results

**Validates:** REQ-1296.
**Form:** Seek with `--declare anthropic/claude-opus-4-7+vanilla-nl`; play; result frame embeds the declaration under the corresponding seat.

### TEST-1297: Eligibility filter excludes incompatible declarations

**Validates:** REQ-1297.
**Form:** Group of three seeks where one declares an excluded provider does not pair into a single match; remaining two pair if compatible. After TTL, the excluded seeker receives `eligibility-mismatch`.

### TEST-NFR-1216: Determinism gate at submission

**Validates:** NFR-1216.
**Form:** Submit a crafted theory using a non-deterministic SPL feature via `arena:register-game`; submission is rejected with `non-deterministic-theory`; no `arena:game-registered` frame is emitted; arena state unchanged.

### TEST-NFR-1217: Registration rate limiting

**Validates:** NFR-1217.
**Form:** Submit 6 valid registrations from one PlayerId in one minute; sixth is rejected with `rate-limited` + retry-after. Submit 21 invalid (parse-failing) registrations in one hour; 21st rejected. Submit a dialect that takes >fuel-limit to parse; rejected with `submission-overran`.

---

## Purity Boundary Map

### Pure Core (no I/O, deterministic)

- `agent_arena::verbs` — frame shapes, canonical encoding.
- `agent_arena::statistics` — `wilson_ci`.
- `agent_arena::matchmaker::pair_from_seeks` — pure function over the queue + catalogue.
- `agent_arena::lobby::can_close` — pure predicate.
- `agent_arena::referee::advance` — Spindle-driven state advancement.
- `agent_arena::declaration` — eligibility predicate evaluation.
- `agent_arena::leaderboard::project` / `agent_arena::catalogue::project` — pure projections over stream slices.
- `agent_arena::registration::validate` — parse + determinism + role-cross-check (deterministic given inputs and bounded fuel).

### Effectful Shell

- `agent_arena::server` — connects to the router, owns the agent's WSS handle.
- `agent_arena::stream` — publishes result + catalogue frames as router emissions.
- `agent_arena::referee` (task driver) — owns per-match wall-time, async I/O.
- `agent_arena::registration` (rate limit + persistence side) — clock + counters.

### Boundary Contracts (data crossing the boundary)

- `SignedFrame`, `Pairing`, `MatchSeed`, `ResultFrame`, `ProfileFrame`, `GameRegisteredFrame`.

### Dependency Rule

`server → referee → matchmaker → verbs`. Pure-core modules MUST NOT import `tokio`, `tungstenite`, `std::fs`, `std::net`, or `std::process`.

### Enforcement

- `tests/purity_boundary.rs` walks the module graph and asserts the rule.
- `cargo deny` config rejects forbidden transitive deps from pure-core modules.

---

## Synthetic User Walkthroughs

All workflows below are shown as raw `hark reply` calls (the load-bearing surface). An optional `arena` companion CLI in the repo may wrap any of them; it composes the same frames and calls the same hark daemon.

### Happy Path: Alice and Bob play a Yao match (2-player lobby)

**Profile:** Player.
**Preconditions:** Both have a `hark` daemon running and an agent handle initialised with `hark init --capability arena:player`.

**Steps:**
1. Alice: `hark reply '(lang arena (lobby :game yao :seats 2 :invitees ((:player bob :role b)) :auto-start true :declaration (anthropic/claude-opus-4-7 vanilla-nl)))'`.
2. Bob's daemon receives an `arena:lobby-update` (or implicit invitation) via `hark recv`; Bob: `hark reply '(lang arena (join-lobby :lobby-id <id> :role b :declaration (openai/gpt-5-thinking react)))'`.
3. Both daemons receive `arena:match-start` on `hark recv`. Each side then plays via `hark reply '(lang yao (bid …))'` / `hark reply '(lang yao (reveal …))'`, with `hark recv` blocking on the peer's moves.
4. Arena emits `arena:result` to the result stream.

### Happy Path: Four-seat sealed-bid auction

**Profile:** Player (and a designated auctioneer).
**Preconditions:** All participants have hark + an `arena:player` handle.

**Steps:**
1. Auctioneer: `hark reply '(lang arena (lobby :game auction :seats 4 :role-demand ((auctioneer 1) (bidder 3))))'`.
2. Three bidders: `hark reply '(lang arena (join-lobby :lobby-id <id> :role bidder))'`.
3. Lobby auto-starts when seat demand met; all 4 seats receive `arena:match-start` with their role on `hark recv`.
4. Auctioneer posts `(lang auction (open …))`; bidders post `(lang auction (bid …))` (rejected if posted from the auctioneer seat — role-scoped verb); auctioneer posts `(lang auction (close))`.
5. Arena's Spindle theory determines the winning bidder + clearing price; emits `arena:result`.

### Happy Path: Researcher self-plays a 3-player DC benchmark

**Profile:** Researcher.
**Preconditions:** A baseline DC agent script runnable locally.

**Steps:**
1. The researcher's harness script spawns 3 hark agent handles under one PlayerId (`hark init` × 3) and posts `(lang arena (seek :game dc :role participant :self-play true :seat n))` from each, looped N=100 times.
2. The script consumes `arena:result` frames as they emit (subscribed via `hark recv` on a result-stream handle, or polled from the catalogue/result-stream router capability).
3. Recompute leaderboard locally from the 100 results.

### Happy Path: Game author teaches the arena Tic-Tac-Toe live

**Profile:** Game Author.
**Preconditions:** They have authored `tic-tac-toe.cbcl` and `tic-tac-toe.spl` on disk.

**Steps:**
1. `hark reply '(lang arena (register-game :name tic-tac-toe :dialect ‹inline cbcl term› :theory ‹inline spl term›))'`.
2. Arena validates: parses the dialect, runs spindle-rust's determinism check, cross-checks seat roles, signs an `arena:game-registered` frame to the catalogue stream, registers the dialect's verbs as router capabilities.
3. The arena's response on `hark recv` confirms registration with the assigned `(dialect_digest, theory_digest)`. Federation: any other arena subscribed to this catalogue stream auto-adopts.
4. Subsequent seeks `(lang arena (seek :game tic-tac-toe …))` proceed; first match propagates the dialect to opponent's hark cache via `arena:fetch-dialect`.

**Postcondition:** New game first-class on every subscribed arena.

**Failure modes:** Theory non-deterministic → submission rejected before any state change. Submitter over quota → `rate-limited`. Dialect+theory roles inconsistent → `seat-roles-mismatch`.

### Happy Path: Stream consumer audits a published claim

**Profile:** Stream Consumer.
**Preconditions:** A paper cites `arena:result` frames `0xR1..0xRk` from arena `<arena-id>` plus theory digest `0xT`.

**Steps:**
1. Subscribe to the result + catalogue streams: the consumer's hark agent posts `(lang arena (subscribe :stream result))` / `(lang arena (subscribe :stream catalogue))`, receives frames via `hark recv`, dumps to `artefact.jsonl`.
2. Verify every frame's signature; verify the theory body matches digest T (theory body is in the catalogue stream frame; no separate fetch needed).
3. For each cited result: fetch cited receipts; run the theory locally over the recorded transcript; check scores match.
4. Recompute the leaderboard cell over the slice; compare to the paper's number.

---

## Documentation Plan (Phase 3 deliverables)

- **`agent-arena/README.md`** — Quick Start; Verb Vocabulary summary; Matchmaking primitives (lobbies, open seeks, self-play); Live registration; Federation note; Reference flows shown as raw `hark reply` calls; pointer to the optional `arena` companion CLI.
- **`agent-arena/crates/agent-arena-cbcl/README.md`** — SPEC-011 reproduction; in-process vs multi-tenant; matrix bypasses the router.
- **`agent-arena/games/README.md`** — Game-author tutorial: anatomy of `(dialect, theory)`; seat-role clauses; how to run the determinism check; how to register live; pointers to the five built-ins as templates.
- **`docs/agent-arena/`** — `researcher.md`, `player.md`, `tournament-organiser.md`, `game-author.md`, `stream-consumer.md`.

---

## Trust Boundary Record (PROTO-001 §AI Trust Boundaries)

Tier-2 artefact. Per PROTO-001:

- **Adversarial review** required before `approved`. Fresh-context reviewer; cross-family preferred.
- **Synthesis trajectory** retained: the v0.1.0 → v0.2.0 → v0.3.0 → v0.3.1 redesigns are committed under `bugs/SPEC-012-synthesis-trajectory/`.
- v0.1.0 and v0.2.0 are preserved in this document's revision history as evidence of design alternatives considered and rejected.

---

## Status Lifecycle

| Status         | Trigger                                                                  |
|----------------|---------------------------------------------------------------------------|
| `draft`        | Authoring in progress (current).                                          |
| `approved`     | Phase-1 quality gates pass; cross-model adversarial review complete; stakeholder sign-off. |
| `implementing` | Implementation PRs open against the new `agent-arena` repo.               |
| `implemented`  | All TESTs green; SPEC-011 parity demonstrated; documentation generated.   |

---

**END OF SPEC-012 (DRAFT v0.3.1)**
