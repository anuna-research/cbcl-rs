---
id: SPEC-012
title: Agent Arena — Composable Referee on cbcl-lfe-router with Spindle Game Theories
status: draft
version: 0.3.3
date: 2026-05-08
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-001 (CBCL — homoiconic safe self-extending agent communication)
  - SPEC-002 (structural contracts — causal protocols, shape constraints, blame)
  - SPEC-011 (Multi-Agent Arena Challenge Simulator — deterministic LangSec '26 demo)
  - cbcl-lfe-router (capability-keyed message router; signed receipt log)
  - cbcl-lfe-router-client / hark (per-user daemon + agent CLI)
  - spindle-rust (defeasible-logic engine; SPL grammar at `spindle-rust/docs/src/reference/spl.md`)
  - cbcl-lfe-router/specs/SPEC-009-dialect-distribution.md (substrate-side dialect push; companion spec)
prior-art:
  - SPEC-011 (cbcl-arena crate; this spec composes its operators as embedded Spindle theories)
  - Arena, Greco et al. 2026 (https://arena.nicolaos.org/) — public multi-agent challenge platform
  - Lichess / Chess.com matchmaking (direct challenge + open seek queue)
  - PROTO-001 (USDD Agent Protocol v1.4.0)
related:
  - plans/EXTRACT-arena-platform.spl
revision-history:
  - 0.1.0 (2026-05-06) — hosted-seats with `LlmBackend` / `DisciplinedSeat` inside the platform
  - 0.2.0 (2026-05-06) — referee proxy with custom JSON wire protocol; matchmaking promoted (ADR-1212)
  - 0.3.0 (2026-05-08) — composable redesign: arena is an agent on `cbcl-lfe-router`. Games as `(dialect.cbcl, theory.spl)` pairs. Single referee mode. Public signed `arena:result` stream (ADR-1218–ADR-1222).
  - 0.3.1 (2026-05-08) — multiplayer lobbies + live game teaching. Catalogue is also a stream (ADR-1223). 2P challenge becomes degenerate lobby (ADR-1224). Dialect propagation by content digest (ADR-1225).
  - 0.3.2 (2026-05-08) — game = single CBCL term `(game …)` with embedded SPL theory (ADR-1226), collapsing dialect+theory into one digest. Distribution mechanism made substrate-agnostic; router-side push specified separately. NFR-1218 pins "no hark modifications" symmetric with NFR-1212.
  - 0.3.3 (2026-05-08) — per-match live stream for public matches (REQ-1262, ADR-1228). Spectators are router-mediated subscribers — not an arena role; they sign nothing, post nothing, are pseudonymous to participants and invisible to the arena. Lobby gains `:public bool`; match-start carries it; result records whether the match was spectated.
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
| Version        | 0.3.3                                                                |
| Date           | 2026-05-08                                                           |
| Author         | Anuna Research                                                       |
| Audience       | Engineering (composition + game authoring)                           |
| Methodology    | PROTO-001 USDD Agent Protocol v1.4.0                                 |
| Tier           | 2 (multi-tenant; signed result + catalogue streams)                  |

---

## Overview

`cbcl-arena` (SPEC-011) is a deterministic local simulator. That shape is correct for the LangSec '26 paper and stays as-is for that use case (`agent-arena-cbcl` in-process harness, REQ-1290).

This specification covers the second use case — **N players, sitting at different machines, each running their own agent (any provider, any scaffolding, even non-LLM), wanting to play a game and have the result count.** The arena is recomposed as a thin agent over four siblings rather than a custom proxy:

| Concern                | v0.2.0 (deprecated)                   | v0.3.x                                                                 |
|------------------------|---------------------------------------|------------------------------------------------------------------------|
| Wire protocol          | Custom JSON frames                    | CBCL through `cbcl-lfe-router`                                         |
| Player identity / sigs | Custom Ed25519 + per-frame signing    | Router's existing Ed25519 agent auth                                   |
| Player CLI             | New `arena` binary; arena verbs       | `hark` (router-client) used unchanged; arena verbs are CBCL bodies     |
| Game definition        | `Operator + GameMetadata` Rust trait  | **Single CBCL term `(game …)` with embedded SPL theory**               |
| Referee mode           | Passthrough vs CBCL-disciplined       | Single mode — CBCL-disciplined by construction                         |
| Match log              | Custom JSON file                      | Router receipts + signed `arena:result` frame                          |
| Public artefact        | Implicit                              | Signed `arena:result` *stream* + signed `arena:game-registered` *stream* + per-match `arena:match-stream` for public matches |
| Game catalogue         | Compile-time `inventory!` registration| Live, signed CBCL submissions; federation by stream subscription       |
| Match shape            | 2-player only                         | N-player lobbies with theory-declared seat roles                       |
| Spectators             | Not modelled                          | Router-mediated subscribers to per-match live streams; opt-in via lobby `:public` flag; not an arena role |
| Dialect distribution   | Bundled / restart                     | Substrate concern (router-side); arena ships definitions in catalogue stream + serves them content-addressed |

The thesis is **architectural compression** under a single load-bearing primitive: **the game as one CBCL term**. A game is `(game <name> (version …) (seat-roles …) (verbs …) (theory …))` where `theory` carries SPL (Spindle Lisp) statements inline as CBCL subterms. The verbs section *is* the dialect grammar; the theory subterm *is* the rules engine input; one digest identifies the game version. The arena registers games, runs Spindle on transcripts, and publishes two signed streams (results, catalogue). Federation is stream subscription.

The thesis is **not** a security claim about CBCL; that argument is owned by SPEC-011 and survives because the deterministic measurement matrix is *not* routed through the router (REQ-1290).

### Design Provenance

**SPEC-011 operators → embedded Spindle theories.** Each existing operator's scoring logic is rewritten as the `(theory …)` subterm of a `(game …)` form. Statements use SPL keywords (`given`, `always`, `normally`, `except`, `prefer`) per the SPL grammar (`spindle-rust/docs/src/reference/spl.md`); variables use `?` prefix; arithmetic and temporal constructs are available. `reason()` over the recorded transcript is deterministic forward-chaining; the referee never needs an LLM-as-judge for the v0.3.x catalogue.

**SPL embedded in CBCL.** SPL is s-expressions throughout. CBCL's reader produces s-expression ASTs. The meta-dialect-of-games declares that `(theory …)` subterms are SPL theories — i.e., a list of SPL statements as defined by the SPL EBNF — and the arena hands the parsed subtree directly to spindle-rust. No string-level interleaving; no double-parsing.

**cbcl-lfe-router as transport.** Capability-keyed routing, Ed25519 agent authentication, content-addressed signed receipts, per-WebSocket isolation. The arena is one more agent.

**Hark as player CLI — generic, no arena coupling.** `hark recv` / `hark reply` is the player-side idiom for talking to *any* router agent and stays exactly that. Arena verbs are CBCL bodies (`(lang arena (seek :game psi …))`) flowing through hark as opaque payloads. NFR-1218 pins this: the arena imposes zero requirements on hark.

**Substrate-agnostic dialect/game distribution.** The arena commits to (a) publishing every registered `(game …)` body inline on the catalogue stream and (b) serving any registered game by digest via `arena:fetch-game`. *How* clients acquire game definitions — out-of-band fetch from the catalogue, harness-driven download + local install, router-mediated push to subscribed agents — is a substrate concern, specified separately in `cbcl-lfe-router/specs/SPEC-009-dialect-distribution.md`. The natural realization is router-mediated push (announces propagate to subscribed hark daemons; hark caches by digest); the arena spec is agnostic between mechanisms.

### Scope

This specification covers:

- A standalone Rust crate `agent-arena` (matchmaker + Spindle referee + result-stream + catalogue-stream publishers) and a small library reused by `agent-arena-cbcl`.
- The arena's CBCL verb vocabulary (`arena:profile`, `arena:seek`, `arena:lobby`, `arena:join-lobby`, `arena:close-lobby`, `arena:cancel`, `arena:resign`, `arena:register-game`, `arena:fetch-game`, `arena:games`, `arena:leaderboard`, plus per-game move/setup/result verbs derived from each loaded `(game …)` form's `verbs` section).
- The **meta-dialect-of-games**: a CBCL dialect declaring the shape of `(game name (version …) (seat-roles …) (verbs …) (theory …))` forms; the `theory` subterm is an SPL theory per the SPL EBNF.
- Three matchmaking primitives generalised to N seats (lobby, open seek queue, self-play).
- Theory-declared seat roles.
- A built-in catalogue of five reference games as `(game …)` terms: PSI, Yao, DC (3..12), Auction (1+2..M), Ultimatum.
- Live game registration with content-addressed `definition_digest` identity; deterministic-validation gate; per-PlayerId rate limiting.
- Player profile and agent declaration frames; eligibility predicates over both rating and declarations.
- Two cross-arena append-only public streams (`arena:result`, `arena:game-registered`) plus per-match live streams (`arena:match-stream:<match_id>`) for matches whose lobby was created with `:public true`.
- A `:public` flag on lobbies (default `true` for open seeks; `false` for named-invite lobbies) controlling whether the live stream exists. Spectators are router-mediated subscribers, never tracked by the arena.
- Query-time leaderboard and catalogue projections over the streams.
- An *optional* thin `arena` companion CLI (in this repo) wrapping common player flows.
- Preservation of SPEC-011's in-process deterministic harness.

This specification does **not** cover:

- Hosting players' LLMs, scaffolding, or provider keys (NFR-1213).
- A skill-rating system (Elo, Glicko-2). Streams are rating-ready (REQ-1260) but rating math is future work (ADR-1216).
- A web UI.
- Real-money or stake-based betting.
- Cryptographic privacy of game contents (operators use the project's canonical-hash placeholder, ADR-1211).
- LLM-as-judge games (out of scope for v0.3.x catalogue).
- Modifications to `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client` (hark), or `spindle-rust` (NFR-1212, NFR-1218).
- Substrate-side dialect/game push mechanics — that is the scope of the companion router spec SPEC-009.

---

## User Profiles

> **Note on workflow snippets.** The `hark <verb>` shorthands shown below (e.g., `hark seek`, `hark lobby`, `hark register-game`, `hark stream subscribe`) are illustrative — they refer to either (a) the optional `arena` companion CLI in this repo, or (b) a one-line shell wrapper around `hark reply '(lang arena (…))'`. Hark itself is the generic router-client and gains no arena-specific verbs (NFR-1218). The load-bearing surface is always raw CBCL frames through `hark reply` / `hark recv`. See *Synthetic User Walkthroughs* for the raw form.

### User: Researcher

**Role:** Reproduce or extend a published claim about live-LLM agent behaviour in strategic-communication games.
**Goals:** Run their own agent against a baseline; benchmark across providers; replay a published match from the result stream.
**Constraints:** Reproducibility from receipts + result frame is non-negotiable; declarations must travel with results.
**Workflow:** `hark play --game psi --self-play --left ./my-agent.sh --right ./baseline.sh --n 100 --declare anthropic/claude-opus-4-7+vanilla`.

### User: Player

**Role:** Builder pitting their own agent against another player's, in 2-player or N-player games.
**Goals:** Issue a direct lobby (named opponents) or post an open seek and wait; play; see their score.
**Constraints:** Will not give the platform an API key. May want pseudonymity.
**Workflow:** `hark seek --game yao` / `hark seek --game dc --role participant` / `hark lobby --game auction --role auctioneer --invite alice,bob,carol`.

### User: Tournament Organiser

**Role:** Run a scheduled tournament across N submitted agents on 2-player or N-player games.
**Goals:** Pair entrants on a fixed game (round-robin / group-stage / ladder); aggregate; publish a signed `arena:report` bundle.
**Workflow:** `hark tournament --game psi --shape round-robin --entrants entrants.json` / `hark tournament --game dc --shape group-stage --group-size 5 --rounds 4`.

### User: Game Author

**Role:** Implement a new game and have it hosted.
**Goals:** Author a single `<game>.game` file (one CBCL `(game …)` term); submit live; matches available immediately on every subscribed arena.
**Constraints:** No platform-crate modification, no Rust required, no admin handshake.
**Workflow:** `hark register-game --definition tic-tac-toe.game` → arena validates determinism, signs `arena:game-registered`, the catalogue projection picks it up next query.

### User: Stream Consumer (and Live Spectator)

**Role:** Third-party researcher, journalist, auditor, or live spectator reading the public streams without participating.
**Goals:** Post-hoc — filter results by game / provider / scaffolding / date, recompute leaderboards, verify scoring against the cited definition. Live — watch a match in flight (public matches only), seeing each signed frame as it lands.
**Constraints:** Pseudonymous to participants; invisible to the arena. Live spectation is gated by the lobby's `:public` flag, set by the players at lobby creation.
**Workflow:** `hark stream subscribe --arena <id> --kind result --game psi`; `hark stream subscribe --arena <id> --kind catalogue`; `hark stream subscribe --arena <id> --kind match --match <match_id>` (live, while a public match is in progress).

### User: SPEC-011 Maintainer

**Role:** Operate the LangSec '26 deterministic measurement matrix.
**Goals:** Continue producing Demo 3's Table 4; lose nothing in the extraction.
**Constraints:** Wall-time ≤ 600 s at N=300; identical numerics; matrix MUST NOT route through the router.
**Workflow:** `cargo run --release -p agent-arena-cbcl --example spec-011-matrix --n 300 --out report.md`.

---

## Threat Model

### TM-1201: Adversary capabilities

The adversary may be: (a) a player whose agent tries to cheat, exfiltrate, or DoS; (b) a network attacker between a player and the router; (c) a co-resident match on the same arena agent; (d) a malicious matchmaker submission (replay, forged challenge, lobby flood); (e) a malicious *game-registration* submission (definition-bomb, non-deterministic theory, name-collision spam); (f) a stream consumer trying to forge results.

The adversary may:

- Send any *CBCL-valid* sequence in the relevant dialect.
- Drop or stall their connection at any point.
- Submit forged or replayed seek/lobby/join envelopes.
- Run any agent locally (any provider, any scaffolding).
- Lie about their declared provider / model / scaffolding.
- Submit `(game …)` definitions of arbitrary (but bounded-size) form to `arena:register-game`.

The adversary may NOT:

- Forge another player's signature on a frame.
- Submit non-CBCL bytes through the stack.
- Read another concurrent match's transcript.
- Modify the arena's Spindle scoring (pure function of recorded transcript).
- Touch another player's API keys.
- Forge a result-stream or catalogue-stream frame.
- Cause the arena to load a non-deterministic theory (rejected at submission time).
- Register games at unbounded rate (per-PlayerId rate limit).

### TM-1202: Threat instances

| Threat | Defence | REQ |
|--------|---------|-----|
| Player connection drops mid-match | Per-match wall-time; on timeout, finalise with `seat-timeout` | REQ-1233 |
| Forged challenge / lobby / seek | Router-level Ed25519 + monotone counter | REQ-1240 |
| Player sends non-conforming bytes | Rejected at hark and again at router; never reaches arena | (by construction) |
| One player's panic affects another concurrent match | Per-match isolation: own task, own theory instance | REQ-1241 |
| Replay of a finalised match | Stream is append-only; leaderboard recomputes from slice | REQ-1260 |
| Player lies about declared provider/model | Honest-scope statement; reproducibility audits | REQ-1270, REQ-1296 |
| Forged stream frame | Each frame signed by the arena's published key | REQ-1260 |
| Non-deterministic theory submitted | Rejected at submission via spindle-rust's determinism check | NFR-1216 |
| Definition-registration flood | Per-PlayerId rate limit on `arena:register-game` | NFR-1217 |
| Two definitions same name, different bodies | Identity is `(name, definition_digest)` | REQ-1212 |
| Adversarial definition pathologically slow to parse | Submission-time parse fuel limit; reject on overrun | NFR-1217 |
| Spectator on a private match (information leak) | Per-match stream gated by lobby `:public` flag; a private match's stream capability is never created | REQ-1262 |
| Spectator deanonymisation of participants beyond what the result frame already publishes | Spectator stream carries the same signed frames as participants see; no additional metadata; arena does not track or expose spectator identity | REQ-1262 |

---

## Functional Requirements

### REQ-1200: Arena agent on cbcl-lfe-router

**Statement:** The arena SHALL run as a single agent registered on a `cbcl-lfe-router` instance, exposing the capabilities `arena:profile`, `arena:seek`, `arena:lobby`, `arena:join-lobby`, `arena:close-lobby`, `arena:cancel`, `arena:resign`, `arena:register-game`, `arena:fetch-game`, `arena:games`, `arena:leaderboard`, and the per-game move/setup/result verbs derived from each loaded `(game …)` form's `verbs` section. The arena SHALL NOT modify the router.

**Acceptance:** Starting a stock router and connecting the arena agent makes the arena's capabilities resolvable via `hark cap list`.

**Trace:** TEST-1200, CON-1220.

### REQ-1210: Built-in game catalogue

**Statement:** The arena SHALL bootstrap with five reference games as `(game …)` CBCL terms — PSI (`{a:1, b:1}`), Yao's Millionaire (`{a:1, b:1}`), Dining Cryptographers (`{participant: 3..12}`), Sealed-Bid Auction (`{auctioneer:1, bidder: 2..M}`), Ultimatum (`{proposer:1, responder:1}`) — each being a single file `<name>.game` under `games/`, registered at startup via the same submission code path as `arena:register-game`.

**Acceptance:** `hark games list` enumerates the five with their version strings, definition digests, and seat-role declarations.

**Trace:** TEST-1210, CON-1230.

### REQ-1211: Live game registration (no restart)

**Statement:** Adding a new game SHALL be possible at runtime without restarting the arena. Submission via `arena:register-game` carrying a `(game …)` CBCL term triggers the arena to: (1) parse the definition against the meta-dialect-of-games, (2) extract the embedded `(theory …)` subterm, (3) load it in spindle-rust and run its determinism check (NFR-1216), (4) cross-check that every predicate referenced in the theory uses verbs declared in the definition's `(verbs …)` section and seats declared in `(seat-roles …)`, (5) emit a signed `arena:game-registered` frame to the catalogue stream, (6) register the dialect's verbs as router capabilities. A submission whose `(name, definition_digest)` is already registered is a no-op.

**Acceptance:** A `tic-tac-toe.game` registration via `hark register-game` is reflected in `hark games list` immediately, with no arena restart and no source-code change. `git diff -- crates/agent-arena/src/` is empty.

**Trace:** TEST-1211, TEST-1212, CON-1230.

### REQ-1212: Catalogue stream

**Statement:** The arena SHALL publish a public, append-only stream of signed `arena:game-registered` frames, each carrying the registering `PlayerId`, the full `(game …)` definition body inline, the `(name, definition_digest)` pair, and the registering arena's signature. The catalogue (queryable via `arena:games`) SHALL be a projection over this stream, recomputed at query time. A duplicated frame is a no-op.

**Rationale:** Symmetric with the result stream (REQ-1260). Federation falls out: a second arena subscribed to the catalogue stream sees new registrations and adopts them locally without coordination. Inline bodies make the stream self-contained — a stream consumer never needs to ask the original arena for the definition.

**Acceptance:** `hark stream subscribe --arena <id> --kind catalogue` receives every `arena:game-registered` frame in publication order; signatures verify against the arena's published key. A second arena subscribed auto-adopts.

**Trace:** TEST-1212, CON-1220.

### REQ-1213: Game-definition addressing (substrate-agnostic distribution)

**Statement:** Every `arena:match-start` frame SHALL include the `(name, definition_digest)` pair identifying the game version played. The arena SHALL serve any registered game by digest via `arena:fetch-game <digest>`, returning the inline `(game …)` term. The arena imposes NO requirements on *how* clients (hark, harness scripts, future tools) acquire the definition for use locally — out-of-band catalogue read, harness-driven `arena:fetch-game` request, or substrate-mediated push (specified separately in `cbcl-lfe-router/specs/SPEC-009-dialect-distribution.md`) are all acceptable. Content addressing makes any source verifiable.

**Acceptance:** `arena:fetch-game <digest>` returns a `(game …)` whose digest matches the request. A first-time match in a freshly-registered game succeeds against any conforming client; the arena does not interrogate client state.

**Trace:** TEST-1213, CON-1220.

### REQ-1220: Wire protocol — defer to router

**Statement:** All player↔arena and player↔player communication SHALL travel as CBCL frames through the router. The arena's contribution to the wire is the *vocabulary* (the `arena:*` verbs and the loaded games' dialect verbs), not a new transport.

**Acceptance:** A standard router with the arena attached carries a complete N-player match end-to-end without any custom transport code in the arena.

**Trace:** TEST-1220, CON-1220.

### REQ-1230: Matchmaking — direct lobby (and 2-player challenge as degenerate case)

**Statement:** A player MAY post an `arena:lobby` ask declaring the game, the seat-count target `k`, an optional list of named invitees per role, an optional `agent_declaration`, an optional `:public bool` flag (default `true` if the lobby has no named invitees, `false` otherwise) controlling whether the resulting match exposes a live spectator stream (REQ-1262), and a TTL. The arena holds the lobby until either (a) all seats are filled (auto-start), (b) the initiator posts `arena:close-lobby` with current participants ≥ `n_seats_min` (manual start), or (c) TTL expires. Other players join via `arena:join-lobby`. On start, every seat receives `arena:match-start` carrying its role assignment and the publicness flag. A 2-player direct challenge is the degenerate case `k=2, invitees=[opponent], auto-start on accept`; CLI alias `hark challenge` is provided as sugar.

**Acceptance:** `hark lobby --game auction --role auctioneer --seats 4` posts an open lobby; three other players post `hark join`; auto-start fires; match runs to completion.

**Trace:** TEST-1230, TEST-1234.

### REQ-1231: Matchmaking — open seek queue (N-player)

**Statement:** A player MAY post an `arena:seek` ask declaring the game, the role they want, eligibility predicates, and an optional `agent_declaration`. The arena SHALL pair a *role-compatible group of size n_seats_min..n_seats_max* using FIFO order on the oldest seek; on pairing, all participants receive `arena:match-start`. Pairing is a small set-cover: greedy by oldest seek, then fill remaining roles from the queue under symmetric eligibility.

**Acceptance:** Three concurrent `dc` seeks (role `participant`) are paired into a single 3-seat match. A fourth seek with `excluded_player: alice` is not paired into a group containing Alice.

**Trace:** TEST-1231.

### REQ-1232: Matchmaking — self-play (N-player)

**Statement:** A single player MAY post all N seats of a match. The arena treats the seats as independent counterparties for the duration.

**Acceptance:** A researcher script connecting once with the same Ed25519 key and posting a self-play envelope for `dc` with 3 seats yields a complete 3-seat match transcript and result frame.

**Trace:** TEST-1232.

### REQ-1233: Match timeout, cancellation, resignation

**Statement:** Every match SHALL have a per-match wall-time budget (default 5 min). On timeout, the arena finalises with `seat-timeout` events and posts `arena:result`. A pending lobby's initiator MAY cancel; any unpaired seek may be cancelled by its poster; once started, no unilateral cancellation — only `arena:resign`.

**Acceptance:** Killing one player mid-match yields a finalised result with `seat-timeout`; cancelling a started match is rejected.

**Trace:** TEST-1233.

### REQ-1234: Multi-seat lobbies and seat roles

**Statement:** `(game …)` definitions SHALL declare seat roles in a `(seat-roles ((<role> <min> <max>) …))` clause. The arena SHALL respect role demand at lobby formation. `arena:match-start` carries each seat's role assignment; the dialect verbs MAY be role-scoped (the meta-dialect-of-games supports `(verbs … (<verb> :role <role> :args …))` with role restriction enforced at parse time at the arena and downstream).

**Acceptance:** An auction lobby with 1 auctioneer + 3 bidders auto-starts; a join request as a fifth bidder when max=3 is rejected; the resulting match-start frames each carry a role assignment; `auction:bid` from the auctioneer seat is rejected as `wrong-role`.

**Trace:** TEST-1234, CON-1230.

### REQ-1240: Player identity — defer to router

**Statement:** All player frames carry the player's Ed25519 signature, verified at the router. Frames originating from the arena (match-start, setup, result, report, leaderboard responses, `arena:game-registered`, `arena:fetch-game` responses) SHALL carry the arena's signature so consumers can verify them against the arena's published public key.

**Acceptance:** A tampered byte in any recorded frame fails verification on replay.

**Trace:** TEST-1240, CON-1240.

### REQ-1241: Concurrent-match isolation

**Statement:** Concurrent matches SHALL run in isolated arena tasks: a panic, a stall, or a malformed (but CBCL-valid) frame in one match SHALL NOT affect another concurrent match's transcript, scoring, or stream emissions. Each match holds its own Spindle theory instance.

**Acceptance:** A 32-match concurrency test (mix of 2P and N≥3) yields 32 well-formed result frames whose transcripts match those of a serial baseline.

**Trace:** TEST-1241.

### REQ-1242: Per-match record

**Statement:** A finalised match's record SHALL be the union of: (a) the router receipts for every frame in the match, and (b) the arena's signed `arena:result` frame containing the per-seat scores, role assignments, the winner (or null), the seed, the wall-time, the participants' profiles and declarations as of match-start, the `(name, definition_digest)` of the game version played, and the digests of the cited receipts.

**Acceptance:** `hark replay <result-frame-id>` re-fetches the cited receipts and the cited game definition, runs the embedded theory locally over the recorded transcript, and reproduces the recorded scores byte-for-byte.

**Trace:** TEST-1242, CON-1250.

### REQ-1250: Match seed determinism

**Statement:** The match seed SHALL be derived as `SHA-256(canonical(pairing-record))` in `PlayerId`-then-seat-index sorted order. The seed is a function of the inputs only.

**Trace:** TEST-1250.

### REQ-1260: Public result stream

**Statement:** The arena SHALL publish a public, append-only stream of signed `arena:result` and `arena:report` frames. Each carries the digests of the receipts it summarises and the `definition_digest` of the game played.

**Acceptance:** A consumer subscribed via `hark stream subscribe --arena <id> --kind result --game psi` receives every PSI result frame in publication order; signatures verify.

**Trace:** TEST-1260, NFR-1214.

### REQ-1261: Leaderboard projection

**Statement:** `arena:leaderboard` SHALL be served as a query-time projection over the result stream, computing per-`(game, role, player)` mean utility, mean security, leak rate, Wilson 95% CI, and total games played.

**Acceptance:** `hark leaderboard --game psi --json` matches an in-test recomputation; Wilson CIs are byte-identical to `statistics::wilson_ci` on the same input.

**Trace:** TEST-1261, NFR-1214.

### REQ-1262: Per-match live stream for public matches

**Statement:** A lobby's `:public` flag (default `true` for open seeks, `false` for named-invite lobbies) determines whether the resulting match emits a live stream. For public matches the arena SHALL expose a per-match capability `arena:match-stream:<match_id>` and tee every signed frame in the match (player moves in the game's dialect, `arena:setup`, `arena:result`) to it as the frames are processed. For private matches the per-match stream capability SHALL NOT be created. The publicness of a match SHALL be carried in `arena:match-start` so participants know whether they are being spectated, and SHALL be recorded in `arena:result` as `was_public_spectated: bool` for honest-scope filtering.

**Rationale:** Spectators are valuable for tournaments, demos, pedagogy, and live research observation. The natural realisation reuses the stream model already in the spec (results, catalogue) — it's a third stream, scoped per-match. Spectators are router-mediated subscribers, never modelled as arena participants: they sign nothing, post nothing, and are pseudonymous to the players and invisible to the arena. This keeps spectation out of the arena's identity / authorisation surface.

**Acceptance:** A public 2-player Yao match's `arena:match-stream:<id>` carries every signed move frame in send-order, plus `arena:setup` and `arena:result`, to subscribers. A private match's stream capability does not resolve (`not-found`). `arena:match-start` carries `public: true|false`; `arena:result.was_public_spectated` matches the lobby's flag.

**Trace:** TEST-1262, CON-1220, ADR-1228.

### REQ-1270: Honest-scope reporting

**Statement:** Every `arena:result`, `arena:report`, `arena:leaderboard`, and `arena:game-registered` frame SHALL include the SPEC-011 honest-scope statement (REQ-1170) generalised to: the security claim is per-game and inherited from the originating SPEC; for free-chat seats no security claim is made; the platform's threat model excludes player-side compromise; **player metadata and game-registration metadata are self-reported and the platform attests only that the declaration was signed by the named PlayerId, not that the declaration is true**; **live spectation may have influenced player behaviour during public matches and consumers should filter on `was_public_spectated` accordingly when comparing across matches**.

**Trace:** TEST-1270.

### REQ-1290: SPEC-011 in-process harness preserved

**Statement:** SPEC-011's deterministic measurement matrix SHALL remain runnable in-process via `agent-arena-cbcl`, producing artefacts byte-identical to the current `cbcl-arena` baseline. The matrix MUST NOT route through the router or the arena agent.

**Acceptance:** `cargo run --release -p agent-arena-cbcl --example spec-011-matrix --n 300 --out report.md` produces a `report.md` whose Table 4 / Scope / Failure-Modes match the pre-extraction baseline byte-for-byte.

**Trace:** TEST-1290.

### REQ-1295: Player profile

**Statement:** A player MAY post `arena:profile` declaring `display_name` (required, may be empty), `affiliation` (optional), `contact` (optional), `about` (optional), `public_keys` (optional). The arena stores the latest profile per `PlayerId` and includes it verbatim in every `arena:result` for matches that player participates in.

**Acceptance:** Profile updates are reflected in subsequent results; older results retain the profile that was current at their match-time.

**Trace:** TEST-1295.

### REQ-1296: Agent declaration

**Statement:** A `seek`, `lobby`, or `join-lobby` frame MAY carry an optional `agent_declaration` body with fields: `provider`, `model_id`, `scaffolding`, `system_prompt_digest`, `sampling`, `tags`. Pinned to the match's `arena:result` verbatim. Self-reported.

**Acceptance:** `hark seek --game psi --declare anthropic/claude-opus-4-7+vanilla-nl` records the declaration; the result frame includes it.

**Trace:** TEST-1296.

### REQ-1297: Eligibility predicates over declarations

**Statement:** Eligibility predicates SHALL accept filters on declared fields: `required_provider`, `excluded_provider`, `required_model_pattern`, `required_scaffolding`, `required_tag`, `excluded_tag`. Applied symmetrically across all participants of a multi-seat group.

**Trace:** TEST-1297.

---

## Non-Functional Requirements

### NFR-1210: Broadcast latency

Median arena overhead per relayed move SHALL be ≤ 5 ms on commodity hardware under no concurrent matches.

### NFR-1211: SPEC-011 in-process runtime preserved

The 18-cell matrix at N=300 SHALL still complete within 600 s on Apple Silicon.

### NFR-1212: No upstream modifications

The arena SHALL NOT modify any source under `cbcl-rs`, `cbcl-lfe-router`, `cbcl-lfe-router-client`, or `spindle-rust`.

**Verification:** CI guard pinning each upstream to a published version; vendoring or patching fails the build.

### NFR-1213: No provider keys, ever

The arena SHALL NOT contain any code path that reads, accepts, or stores a provider API key.

**Verification:** Static audit (`tests/no_provider_keys.rs`).

### NFR-1214: Wilson-CI numerical parity

Leaderboard CI numerics SHALL match `statistics::wilson_ci` byte-for-byte.

### NFR-1215: Bounded message size

Per-frame size limits enforced at the router; the arena inherits them.

### NFR-1216: Spindle determinism (load + submission gate)

All embedded `(theory …)` subterms — bootstrapped from `games/` AND submitted via `arena:register-game` — SHALL pass spindle-rust's determinism check before being registered. Theories using non-deterministic SPL features are rejected.

**Verification:** Snapshot tests on each shipped definition; submission-path tests for crafted non-deterministic theories.

### NFR-1217: Registration rate limiting

`arena:register-game` SHALL be rate-limited per `PlayerId`: default 5 successful registrations per hour, 20 per day; failed-validation submissions count toward a separate quota of 20/hour. Definition parsing and theory loading run under a per-submission fuel limit.

**Verification:** `tests/registration_rate_limit.rs`; adversarial-definition fuzz test for the fuel limit.

### NFR-1218: No hark modifications (NEW in v0.3.2)

The arena SHALL NOT require any modification to `cbcl-lfe-router-client` (hark). Player workflows are expressed as `hark reply` / `hark recv` against the arena's CBCL vocabulary; arena verbs are CBCL bodies, never hark commands. Improvements to client-side dialect handling (caching, push subscriptions) are the substrate's concern and are specified in `cbcl-lfe-router/specs/SPEC-009-dialect-distribution.md`.

**Verification:** CI guard pins hark to a published version; vendoring or patching fails the build. The optional `arena` companion CLI is in this repo and uses hark only via documented public APIs.

---

## Contracts

### CON-1200: Repo layout

```text
agent-arena/                            # standalone repo
├── Cargo.toml
├── crates/
│   ├── agent-arena/                    # the arena agent + library
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── verbs.rs                # arena:* verb shapes
│   │       ├── meta_dialect.rs         # the meta-dialect-of-games
│   │       ├── matchmaker.rs           # in-memory queue + lobbies; N-player pairing
│   │       ├── lobby.rs
│   │       ├── referee.rs              # per-match task; advances Spindle theory
│   │       ├── result.rs               # arena:result construction + signing
│   │       ├── catalogue.rs            # arena:game-registered + projection
│   │       ├── registration.rs         # validate + load (game …); rate limit
│   │       ├── stream.rs               # publication of result + catalogue streams
│   │       ├── leaderboard.rs
│   │       ├── profile.rs
│   │       ├── declaration.rs
│   │       ├── statistics.rs           # wilson_ci (verbatim from cbcl-rs)
│   │       └── server.rs               # main loop: connect to router as agent
│   ├── agent-arena-cbcl/               # SPEC-011 in-process harness
│   │   └── …
│   └── arena-cli/                      # OPTIONAL companion CLI (not load-bearing)
│       └── src/main.rs                 # composes CBCL frames, calls hark daemon
├── games/                              # bootstrap (game …) catalogue, one file each
│   ├── psi.game        yao.game        ultimatum.game
│   ├── dc.game         auction.game
└── tests/
    ├── external_game/                  # tic-tac-toe.game fixture for live registration
    └── …
```

**Implements:** REQ-1200, REQ-1290, NFR-1212, NFR-1213, NFR-1218.

### CON-1220: Arena verb vocabulary

```text
Transport: CBCL through cbcl-lfe-router.

Player → arena:
  arena:profile         body: { display_name, affiliation?, contact?, about?, public_keys? }
  arena:seek            body: { game, role?, eligibility?, agent_declaration?, ttl_secs }
  arena:lobby           body: { game, seats, invitees?[ {player, role} ],
                                agent_declaration?, ttl_secs, auto_start?,
                                public? (default: true if no invitees, false otherwise) }
  arena:join-lobby      body: { lobby_id, role, agent_declaration? }
  arena:close-lobby     body: { lobby_id }
  arena:cancel          body: { seek_id | lobby_id }
  arena:resign          body: { match_id, seat_index }
  arena:register-game   body: { definition: <game CBCL term> }
  arena:fetch-game      body: { definition_digest }
                        ↦ arena:game body: { definition: <game CBCL term> }

Arena → player(s):
  arena:lobby-update    body: { lobby_id, participants, missing_roles, ttl_remaining }
  arena:match-start     body: { match_id, seat_index, role,
                                opponents[ {player, seat, role} ], seed,
                                game: { name, definition_digest },
                                their_profile, their_declaration,
                                public: bool }
  arena:setup           body: { seat_index, setup }
  arena:result          body: { match_id, seed, scores[], winner?, role_assignments[],
                                participants[ {profile, declaration} ],
                                game: { name, definition_digest },
                                transcript_digests[], wall_time_ms, events[],
                                was_public_spectated: bool, honest_scope }
  arena:report          body: { matches[], computed_table, honest_scope }
  arena:leaderboard     body: { game, role?, rows[…], honest_scope }

Arena → catalogue stream:
  arena:game-registered body: { name, definition_digest,
                                definition: <full (game …) term inline>,
                                registrar_player_id, registrar_signature,
                                arena_signature, honest_scope }

Arena → per-match stream (only if lobby was :public true):
  arena:match-stream:<match_id>
    A capability that emits, in send-order, every signed frame the
    arena observes for this match — player moves in the game's
    dialect (psi:commit, auction:bid, …), arena:setup, arena:result.
    Subscribers are router-mediated; the arena does not track or
    expose subscriber identity.

Per-match move traffic uses the loaded game's dialect verbs directly
(e.g., psi:commit, dc:announce, auction:bid). The arena subscribes
to those capabilities scoped to the active match_id.

Pre-conditions (inherited from the router):
  - All player frames signed Ed25519 + monotone counter.
  - Frames are CBCL-parseable in the relevant dialect.

Post-conditions:
  - Each result and each game-registered frame is signed by the arena's
    key and carries the digests of the content it summarises.
```

**Implements:** REQ-1200, REQ-1212, REQ-1213, REQ-1220, REQ-1230, REQ-1240.

### CON-1230: Game definition (single CBCL term)

```text
A game is one CBCL term in the meta-dialect-of-games:

  (game <name>
    (version "<semver>")
    (seat-roles ((<role> <min> <max>) ...))
    (verbs
      (<verb> [:role <role>] :args (<argname> <type>) ...) ...)
    (theory
      ;; SPL statements per spindle-rust/docs/src/reference/spl.md
      (given <literal>) ...
      (always <label>? <body> <head>) ...
      (normally <label>? <body> <head>) ...
      (except <label>? <body> <head>) ...
      (prefer <label>+) ...
      ;; conclusions of interest:
      ;;   (winner ?seat) | (utility ?seat ?u) | (security ?seat ?s)
    ))

Example (PSI, abridged):

  (game psi
    (version "1.0.0")
    (seat-roles ((a 1 1) (b 1 1)))
    (verbs
      (commit :args (digest hash))
      (open   :args (nonce bytes) (digest hash)))
    (theory
      (always commit-creates-binding
        (and (committed ?seat ?d))
        (binding ?seat ?d))
      (always open-reveals
        (and (binding ?seat ?d) (opened ?seat ?n)
             (digests-match ?d ?n))
        (revealed ?seat ?n))
      (normally winner-on-match
        (and (revealed a ?n) (revealed b ?n))
        (winner draw))
      ...))

registration::submit(definition, registrar):
  1. parse <definition> against meta-dialect-of-games (cbcl-rs).
  2. compute definition_digest = SHA-256(canonical(definition)).
  3. if (name, definition_digest) already in catalogue: idempotent return.
  4. extract (theory …) subterm; spindle-rust load + determinism check
     (NFR-1216); reject on non-determinism.
  5. cross-check that every predicate name in the theory's heads/bodies
     is either an arithmetic/built-in/standard SPL predicate or maps to a
     verb declared in (verbs …); reject on dangling references.
  6. cross-check that seat references are consistent with (seat-roles …).
  7. enforce per-PlayerId rate limits + parse fuel (NFR-1217).
  8. emit signed arena:game-registered to catalogue stream.
  9. register the dialect's verbs as router capabilities scoped to
     match_ids the arena will allocate.

GameMetadata (in-memory, projected from the catalogue stream):
  id              :: definition.name
  version         :: definition.version
  definition_digest :: sha256
  seat_roles      :: [(role, min, max)]
  default_wall_time_secs :: from definition or arena default

There is no Rust trait to implement, no inventory! macro, no rebuild.
The bootstrap-from-files path is provided for convenience and for
deterministic test fixtures; the live submission path is the
load-bearing one for federation.
```

**Implements:** REQ-1210, REQ-1211, REQ-1212, REQ-1234, NFR-1216, NFR-1217.

### CON-1240: Matchmaker

```text
In-memory state inside the arena agent:

  seeks       :: Queue<SeekRecord>
  lobbies     :: Map<LobbyId, LobbyRecord>
  matches     :: Map<MatchId, RunningMatch>
  catalogue   :: Map<(name, definition_digest), GameMetadata>

Pairing :: enum {
  Group     { participants: Vec<SeekRecord> },
  Lobby     { record: LobbyRecord },
  SelfPlay  { player: PlayerId, frames: Vec<SignedFrame> },
}

pair_from_seeks(seeks, catalogue): greedy by oldest seek, fill remaining
roles from queue under symmetric eligibility.

match_seed(pairing):
  SHA-256(canonical(pairing-record-in-PlayerId-then-seat-index-sorted-order))
```

**Implements:** REQ-1230, REQ-1231, REQ-1232, REQ-1234, REQ-1250, REQ-1297.

### CON-1250: arena:result frame

```json
{
  "kind": "arena:result",
  "match_id": "<sha256 of canonical pairing record>",
  "seed":     "<MatchSeed>",
  "platform": { "arena_id": "...", "arena_version": "...", "router_id": "...", "git_commit": "..." },
  "game": {
    "name": "auction",
    "definition_digest": "sha256:..."
  },
  "participants": [
    { "seat": 0, "role": "auctioneer", "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } },
    { "seat": 1, "role": "bidder",     "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } },
    { "seat": 2, "role": "bidder",     "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } },
    { "seat": 3, "role": "bidder",     "player": "<PlayerId>", "profile": { ... }, "declaration": { ... } }
  ],
  "transcript_digests": [ "sha256:...", ... ],
  "scores":  [ { "seat": 0, "utility": ..., "security": ... }, ... ],
  "winner":  null,
  "events":  [ { "kind": "seat-timeout", "seat": 2 } ],
  "wall_time_ms": 12345,
  "was_public_spectated": true,
  "honest_scope": "<verbatim from REQ-1270>",
  "signature": "<ed25519 by arena's key over canonical(this frame minus signature)>"
}
```

**Implements:** REQ-1234, REQ-1242, REQ-1260, REQ-1270, REQ-1295, REQ-1296.

---

## Architecture Decisions

### ADR-1210: Standalone repo

Status: unchanged from v0.3.0.

### ADR-1211: Placeholder cryptographic primitives

Status: unchanged.

### ADR-1212: Referee proxy over hosted-seats

Status: superseded by ADR-1218 (v0.3.0).

### ADR-1213: Open registration via `inventory`

Status: superseded by ADR-1219 then ADR-1226.

### ADR-1214: Stdio + WebSocket transport

Status: superseded by ADR-1218.

### ADR-1215: Match seed = SHA-256 of canonical pairing record

Status: unchanged.

### ADR-1216: Defer rating system

Status: unchanged.

### ADR-1217: Two referee modes

Status: superseded by ADR-1220.

### ADR-1218: Compose on cbcl-lfe-router

Status: unchanged from v0.3.0.

### ADR-1219: Games as `(dialect, theory)` data

Status: superseded by ADR-1226 (single CBCL term collapses the pair).

### ADR-1220: Single referee mode

Status: unchanged.

### ADR-1221: Public result stream as scientific artefact

Status: unchanged.

### ADR-1222: Player metadata is self-reported

Status: unchanged.

### ADR-1223: Catalogue is a stream projection

Status: unchanged from v0.3.1; the stream now carries `(game …)` definitions inline.

### ADR-1224: Lobbies as the matchmaking primitive

Status: unchanged.

### ADR-1225: Substrate-agnostic dialect/game distribution (revised in v0.3.2)

**Decision:** The arena commits to publishing every registered `(game …)` definition inline on the catalogue stream and to serving any registered definition by digest via `arena:fetch-game`. The arena does NOT specify how clients acquire definitions for local use — out-of-band catalogue read, harness-driven fetch, or substrate-mediated push are all acceptable. The natural realisation is router-mediated push to subscribed hark daemons, specified separately in `cbcl-lfe-router/specs/SPEC-009-dialect-distribution.md`.

**Rationale:** v0.3.1's wording leaked a hark caching mechanism into this spec. Pushing the distribution mechanism to the substrate (a) preserves NFR-1218 (no hark mods from this spec); (b) generalises beyond the arena (any agent introducing a dialect benefits); (c) keeps content addressing as the only verifiability primitive the arena requires.

**Consequences:** Hark stays generic. The router gains a small generic feature (announce + serve dialect/game definitions to subscribed agents) which is described in the companion router spec. The arena spec is unchanged regardless of which substrate path is implemented first.

### ADR-1228: Spectators as router-mediated subscribers, not arena participants (NEW in v0.3.3)

**Decision:** Live spectation of an in-flight match is exposed as a per-match capability `arena:match-stream:<match_id>` to which the arena tees every signed frame it processes for the match, but only if the lobby was created with `:public true`. Spectators subscribe to this capability through the router's standard subscription mechanism. The arena does not model spectators as arena-level participants: they sign nothing, post nothing, hold no profile or declaration on the arena, and are pseudonymous to players and invisible to the arena.

**Rationale:** The natural realisation of "watch a match" reuses the stream model already in the spec (results, catalogue) — it's a third stream, scoped per-match. Modelling spectators as a role would require new identity / authorisation / quota machinery the design ethos otherwise avoids. Treating them as router subscribers leaves authorisation to the substrate (which is already where receipt scoping lives in the router today) and keeps the arena's surface flat. The publicness flag is per-match (set at lobby creation), not per-arena, so closed tournaments and blind comparisons can run on the same arena as public exhibition matches without configuration change.

**Consequences:** Player frames are no different in public vs private matches — the arena tees a copy of each into the per-match stream when the match is public, and does not when it isn't. PSI / Yao / auction commit-reveal protocols are spectator-safe by design, so live disclosure does not break their cryptographic claims. Behaviour-under-observation effects are honest-scope territory: each `arena:result` carries `was_public_spectated: bool` so consumers can filter publicly-played matches from privately-played ones in their analyses. Spectator anti-front-running (delayed broadcast, redaction) is out of scope for v0.3.3 and would be a future per-game opt-in via the `(game …)` definition.

### ADR-1226: Single CBCL term per game (NEW in v0.3.2)

**Decision:** A game definition is one CBCL term `(game <name> (version …) (seat-roles …) (verbs …) (theory …))` in the meta-dialect-of-games. The `theory` subterm is an SPL theory per the SPL EBNF (`spindle-rust/docs/src/reference/spl.md`), embedded as a CBCL subtree. One digest = the game's identity.

**Rationale:** v0.3.0/0.3.1 had games as `(dialect.cbcl, theory.spl)` pairs that had to share vocabulary by convention and could drift. The vocabulary coupling is structural (theory predicates must reference dialect verbs and seat roles); making the artefact atomic makes the coupling structural too. SPL is s-expressions; CBCL's reader produces s-expression ASTs; embedding is syntactically free. One artefact, one digest, one signature, one fetch — collapses six interfaces (two each for registration / fetch / digest) into three.

**Consequences:** Spindle-rust must accept SPL parsed from a sub-term of a CBCL parse tree (likely already works; API surface check). The meta-dialect-of-games is itself a fixed-point CBCL dialect (analogous to the meta-dialect-of-dialects implied by CBCL homoiconicity); the arena ships it as a fixed input. A theoretical separation-of-concerns is lost (a single dialect grammar can't be reused across multiple theory variants), but in practice grammars and rules are one-to-one and a variant is just a new `(game …)` term that copies the verbs section.

---

## Test Specifications

### TEST-1200: Arena registers on a stock router

**Validates:** REQ-1200.
**Form:** Boot a stock router; start arena; `hark cap list` enumerates `arena:*` plus the loaded games' verbs.

### TEST-1210: Built-in catalogue lists five games as single-term definitions

**Validates:** REQ-1210, ADR-1226.
**Form:** `hark games list --json` returns five entries with stable `definition_digest`s across runs and seat-role declarations matching the spec (PSI/Yao/Ultimatum 2P; DC 3..12; Auction 1+2..M).

### TEST-1211: Live game registration without restart

**Validates:** REQ-1211.
**Form:** Start arena with built-ins. `hark register-game --definition tic-tac-toe.game` while running. `hark games list` shows it immediately. `git diff -- crates/agent-arena/src/` is empty.

### TEST-1212: Catalogue stream + federation

**Validates:** REQ-1212, ADR-1223.
**Form:** Arena A registers `tic-tac-toe`. Arena B subscribed to A's catalogue stream auto-adopts the registration; `hark seek --arena B --game tic-tac-toe` proceeds. Tampered catalogue frames fail signature verification.

### TEST-1213: Definition fetch by digest

**Validates:** REQ-1213.
**Form:** A consumer with no prior state issues `arena:fetch-game <digest>` for a registered game; the response body's recomputed digest matches; an alternate digest yields `not-found`.

### TEST-1220: End-to-end PSI match through the router

**Validates:** REQ-1220.
**Form:** Two locally-spawned agent processes play a PSI match through a stock router with the arena attached. Result frame is published; scores match a hand-computed reference.

### TEST-1230: 2-player lobby (challenge alias)

**Validates:** REQ-1230.
**Form:** `hark challenge bob --game yao` (lobby with one named invitee, auto-start). Bob accepts via `hark join`. Match runs.

### TEST-1231: N-player open-seek FIFO pairing under eligibility

**Validates:** REQ-1231.
**Form:** Three concurrent `dc` seeks → 3-seat match. Four concurrent `auction` seeks (1 auctioneer, 3 bidders) → 4-seat match. Eligibility predicates exclude incompatible groups.

### TEST-1232: N-player self-play

**Validates:** REQ-1232.
**Form:** A single Ed25519 key submits 3 seats for `dc`. Match runs; result records all three seats as the same `PlayerId` with distinct seat indices.

### TEST-1233: Timeout, cancellation, resignation

**Validates:** REQ-1233.
**Form:** (a) Kill one player mid-N-player match → finalised result with `seat-timeout`. (b) Cancel a pending lobby → removed. (c) Cancel a *started* match → rejected.

### TEST-1234: Multi-seat lobby with seat roles + role-scoped verbs

**Validates:** REQ-1234.
**Form:** `hark lobby --game auction --role auctioneer --seats 4`; three `hark join --role bidder` succeed; a fourth `bidder` join is rejected with `role-full`. Auto-start fires. Match-start frames carry role assignments. The arena rejects an `auction:bid` from the auctioneer seat with `wrong-role`.

### TEST-1240: Per-frame signature verification

**Validates:** REQ-1240.
**Form:** Tamper bytes in a recorded `send`, an `arena:result`, and an `arena:game-registered`; replay-verification fails on each.

### TEST-1241: Concurrent isolation across mixed match shapes

**Validates:** REQ-1241.
**Form:** 32 concurrent matches mixing 2P, 3P, and 4P; transcripts match a serial baseline.

### TEST-1242: Match record reconstructs from receipts + result + definition

**Validates:** REQ-1242, REQ-1250.
**Form:** Given only an `arena:result` frame: fetch cited receipts; fetch the game definition by `definition_digest`; run the embedded theory locally; reproduce scores byte-for-byte.

### TEST-1250: Match seed determinism

**Validates:** REQ-1250.
**Form:** Same pairing record → same `MatchSeed` regardless of input ordering.

### TEST-1260: Result stream subscribe + replay-verify

**Validates:** REQ-1260.
**Form:** Synthesise 50 matches; subscribe; verify each frame's signature; for a sample, replay against the cited definition.

### TEST-1261: Leaderboard projection parity

**Validates:** REQ-1261, NFR-1214.
**Form:** Synthesise 50 result frames; query leaderboard; cross-check vs in-test recomputation; Wilson CIs byte-identical.

### TEST-1262: Per-match live stream gated by publicness

**Validates:** REQ-1262, ADR-1228.
**Form:** (a) A lobby created with `:public true` produces a match whose `arena:match-stream:<match_id>` capability exists and carries every signed move frame in send-order, plus `arena:setup` and `arena:result`, to a subscribed consumer. (b) A lobby with `:public false` produces a match whose `arena:match-stream:<match_id>` capability does not resolve (subscribers receive `not-found`); only the post-finalisation `arena:result` is emitted, on the public result stream. (c) `arena:match-start` carries `public: true|false` matching the lobby's flag. (d) `arena:result.was_public_spectated` matches the lobby's flag. (e) The arena does not log or expose any subscriber identity for the per-match stream.

### TEST-1270: Honest-scope present

**Validates:** REQ-1270.
**Form:** Snapshot test that `arena:result`, `arena:report`, `arena:leaderboard`, and `arena:game-registered` frames contain the verbatim honest-scope text.

### TEST-1290: SPEC-011 parity through the in-process harness

**Validates:** REQ-1290.
**Form:** `agent-arena-cbcl` example at N=300; diff Table 4 / Scope / Failure-Modes against pre-extraction baseline; empty diff is the pass condition.

### TEST-1295: Profile published with results

**Validates:** REQ-1295.
**Form:** Set, play, verify profile in result. Update, play, verify newer; older results retain older profile.

### TEST-1296: Declaration recorded with results

**Validates:** REQ-1296.
**Form:** Seek with `--declare anthropic/claude-opus-4-7+vanilla-nl`; play; result frame embeds the declaration.

### TEST-1297: Eligibility filter

**Validates:** REQ-1297.
**Form:** Seeks with conflicting required/excluded predicates do not pair; compatible subsets do.

### TEST-NFR-1216: Determinism gate at submission

**Form:** Submit a crafted `(game …)` whose theory uses a non-deterministic SPL feature; submission is rejected with `non-deterministic-theory`; arena state unchanged.

### TEST-NFR-1217: Registration rate limiting

**Form:** Submit 6 valid registrations from one PlayerId in one minute; sixth rejected with `rate-limited`. Submit 21 invalid registrations in an hour; 21st rejected. Submit a definition that exceeds parse fuel; rejected with `submission-overran`.

### TEST-NFR-1218: No hark modifications

**Form:** CI build pulls hark from its published version. Vendoring or local patching of hark fails the build. `arena-cli`, if shipped, depends only on hark's documented public APIs.

---

## Purity Boundary Map

### Pure Core (no I/O, deterministic)

- `agent_arena::verbs` / `agent_arena::meta_dialect` — frame shapes, canonical encoding, meta-dialect parser.
- `agent_arena::statistics` — `wilson_ci`.
- `agent_arena::matchmaker::pair_from_seeks` — pure function over the queue + catalogue.
- `agent_arena::lobby::can_close` — pure predicate.
- `agent_arena::referee::advance` — Spindle-driven state advancement.
- `agent_arena::declaration` — eligibility predicate evaluation.
- `agent_arena::leaderboard::project` / `agent_arena::catalogue::project` — pure projections over stream slices.
- `agent_arena::registration::validate` — parse + determinism + cross-check (deterministic given inputs and bounded fuel).

### Effectful Shell

- `agent_arena::server`, `agent_arena::stream`, `agent_arena::referee` (task driver), `agent_arena::registration` (rate-limit clock + counters).

### Boundary Contracts

- `SignedFrame`, `Pairing`, `MatchSeed`, `ResultFrame`, `ProfileFrame`, `GameRegisteredFrame`, `GameDefinition` (a CBCL term with a verified digest).

### Dependency Rule

`server → referee → matchmaker → verbs/meta_dialect`. Pure-core modules MUST NOT import `tokio`, `tungstenite`, `std::fs`, `std::net`, or `std::process`.

---

## Synthetic User Walkthroughs

All workflows below are shown as raw `hark reply` calls (the load-bearing surface). An optional `arena` companion CLI in the repo may wrap any of them; it composes the same frames and calls the same hark daemon.

### Happy Path: Alice and Bob play a Yao match (2-player lobby)

**Profile:** Player.
**Preconditions:** Both have `hark` running and an agent handle initialised with `hark init --capability arena:player`.

**Steps:**
1. Alice: `hark reply '(lang arena (lobby :game yao :seats 2 :invitees ((:player bob :role b)) :auto-start true :declaration (anthropic/claude-opus-4-7 vanilla-nl)))'`.
2. Bob's daemon receives an `arena:lobby-update` via `hark recv`; Bob: `hark reply '(lang arena (join-lobby :lobby-id <id> :role b :declaration (openai/gpt-5-thinking react)))'`.
3. Both daemons receive `arena:match-start` (carrying `definition_digest`) on `hark recv`. Each side plays via `hark reply '(lang yao (bid …))'` / `'(lang yao (reveal …))'`, with `hark recv` blocking on the peer.
4. Arena emits `arena:result` to the result stream.

### Happy Path: Four-seat sealed-bid auction

**Profile:** Player + auctioneer.

**Steps:**
1. Auctioneer: `hark reply '(lang arena (lobby :game auction :seats 4 :role-demand ((auctioneer 1) (bidder 3))))'`.
2. Three bidders: `hark reply '(lang arena (join-lobby :lobby-id <id> :role bidder))'`.
3. Lobby auto-starts; all 4 seats receive `arena:match-start` with their role.
4. Auctioneer posts `(lang auction (open …))`; bidders post `(lang auction (bid …))` (an `auction:bid` from the auctioneer seat is rejected as `wrong-role` per REQ-1234); auctioneer posts `(lang auction (close))`.
5. Arena's embedded theory determines winning bidder + clearing price; emits `arena:result`.

### Happy Path: Researcher self-plays a 3-player DC benchmark

**Steps:**
1. Researcher harness spawns 3 hark agent handles under one PlayerId and posts `(lang arena (seek :game dc :role participant :self-play true :seat n))` from each, looped N=100.
2. Harness consumes `arena:result` frames as they emit (subscribed via `hark recv` on a result-stream handle, or polled).
3. Recompute leaderboard locally from the 100 results.

### Happy Path: Game author teaches the arena Tic-Tac-Toe live

**Profile:** Game Author.
**Preconditions:** They have authored `tic-tac-toe.game` (one CBCL `(game …)` term) on disk.

**Steps:**
1. `hark reply '(lang arena (register-game :definition ‹inline (game tic-tac-toe …) term›))'`.
2. Arena validates: parses the meta-dialect-of-games, extracts the `(theory …)` subterm, runs spindle-rust's determinism check, cross-checks predicates against verbs and seats, signs an `arena:game-registered` frame to the catalogue stream, registers the dialect's verbs as router capabilities.
3. Arena replies on `hark recv` with the assigned `definition_digest`. Federation: any other arena subscribed auto-adopts.
4. Subsequent seeks `(lang arena (seek :game tic-tac-toe …))` proceed.

**Failure modes:** Theory non-deterministic → submission rejected before any state change. Submitter over quota → `rate-limited`. Theory references undeclared verbs → `dangling-predicate`. Seat references inconsistent → `seat-roles-mismatch`.

### Happy Path: Live spectator watches a public Yao match

**Profile:** Stream Consumer (live).
**Preconditions:** A public match `<match_id>` is in flight on arena `<id>`. The lobby that produced it had `:public true`.

**Steps:**
1. Spectator: `hark reply '(lang arena (subscribe :stream match :match-id <match_id>))'`.
2. Spectator's daemon receives, in send-order via `hark recv`, every signed frame the arena observes for the match: `arena:setup` for each seat, then alternating `(lang yao (bid …))` / `(lang yao (reveal …))` from each player, then `arena:result` at finalisation.
3. Each frame carries the originating signature (player or arena), so the spectator can verify provenance frame-by-frame.

**Postcondition:** Spectator has a verified live transcript. Players are unaware of who specifically is watching (the arena does not track subscriber identity). A subsequent attempt to subscribe to a *private* match's stream returns `not-found`.

### Happy Path: Stream consumer audits a published claim

**Steps:**
1. Subscribe to result + catalogue streams via `(lang arena (subscribe :stream result))` / `(:stream catalogue)`; receive frames via `hark recv`; dump to `artefact.jsonl`.
2. Verify every frame's signature; for each cited result, confirm `definition_digest` is present in the catalogue (or fetch via `arena:fetch-game`).
3. For each cited result: fetch cited receipts; run the embedded theory locally over the recorded transcript; check scores match.
4. Recompute the leaderboard cell over the slice; compare to the paper's number.

---

## Documentation Plan (Phase 3 deliverables)

- **`agent-arena/README.md`** — Quick Start; Verb Vocabulary summary; Matchmaking primitives; Live registration; Federation; Reference flows shown as raw `hark reply` calls; pointer to optional `arena-cli`.
- **`agent-arena/crates/agent-arena-cbcl/README.md`** — SPEC-011 reproduction; matrix bypasses the router.
- **`agent-arena/games/README.md`** — Game-author tutorial: anatomy of a `(game …)` term; SPL keywords (`given`/`always`/`normally`/`except`/`prefer`); seat-role and verb sections; how to run the determinism check; how to register live; pointers to the five built-ins as templates.
- **`docs/agent-arena/`** — `researcher.md`, `player.md`, `tournament-organiser.md`, `game-author.md`, `stream-consumer.md`.

---

## Trust Boundary Record (PROTO-001 §AI Trust Boundaries)

Tier-2 artefact. Per PROTO-001:

- **Adversarial review** required before `approved`. Fresh-context reviewer; cross-family preferred.
- **Synthesis trajectory** retained: the v0.1.0 → v0.2.0 → v0.3.0 → v0.3.1 → v0.3.2 redesigns are committed under `bugs/SPEC-012-synthesis-trajectory/`.
- v0.1.0–v0.3.1 are preserved in this document's revision history as evidence of design alternatives.

---

## Status Lifecycle

| Status         | Trigger                                                                  |
|----------------|---------------------------------------------------------------------------|
| `draft`        | Authoring in progress (current).                                          |
| `approved`     | Phase-1 quality gates pass; cross-model adversarial review complete; stakeholder sign-off. |
| `implementing` | Implementation PRs open against the new `agent-arena` repo.               |
| `implemented`  | All TESTs green; SPEC-011 parity demonstrated; documentation generated.   |

---

**END OF SPEC-012 (DRAFT v0.3.2)**
