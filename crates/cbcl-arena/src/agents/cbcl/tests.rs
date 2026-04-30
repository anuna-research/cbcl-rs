//! TEST-1120: CBCL-disciplined agent tests.
//!
//! Coverage:
//! - PSI honest-vs-honest: 50 games, true-intersection match + dialect
//!   conformance of every emitted message.
//! - Yao honest-vs-honest: 50 games at random wealth pairs, verdict
//!   correctness.
//! - DC honest-vs-honest: 30 games of 3 agents, XOR-sum correctness.
//! - Quarantine isolation: garbage inbound bytes do not influence the
//!   final guess.

use std::collections::BTreeSet;

use rand::seq::SliceRandom;
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use cbcl_core::dialect::Dialect;
use cbcl_core::message::Message;
use cbcl_parser::{parse, parse_message};

use super::dining::{DcSetup, DcVerdict, DiningCbclStrategy};
use super::millionaire::{MillionaireCbclStrategy, YaoVerdict};
use super::psi::PsiCbclStrategy;
use super::{load_dialect, CbclAgent, ChallengeStrategy, StepStatus};

use crate::operator::ChatEvent;

const PSI_DIALECT_SRC: &str = include_str!("../../../../../demo/dialects/psi.cbcl");
const MILLIONAIRE_DIALECT_SRC: &str =
    include_str!("../../../../../demo/dialects/millionaire.cbcl");
const DINING_DIALECT_SRC: &str = include_str!("../../../../../demo/dialects/dining.cbcl");

fn psi_dialect() -> Dialect {
    load_dialect(PSI_DIALECT_SRC).expect("psi dialect parses")
}

fn millionaire_dialect() -> Dialect {
    load_dialect(MILLIONAIRE_DIALECT_SRC).expect("millionaire dialect parses")
}

fn dining_dialect() -> Dialect {
    load_dialect(DINING_DIALECT_SRC).expect("dining dialect parses")
}

/// Drive `n` agents through a single game by interleaved stepping until all
/// report done. Returns the full chat transcript and per-agent guesses.
///
/// The harness fans out each agent's outbound emissions to the other
/// `n - 1` agents' inbound queues — a single shared chat transcript.
fn run_game<S>(
    agents: &mut [CbclAgent<S>],
    setups: Vec<S::Setup>,
    rng_seed: u64,
) -> (Vec<ChatEvent>, Vec<S::Guess>)
where
    S: ChallengeStrategy,
{
    assert_eq!(agents.len(), setups.len());
    let n = agents.len();
    // Per-agent inbound queues.
    let mut inboxes: Vec<Vec<ChatEvent>> = vec![Vec::new(); n];
    // Per-agent rngs for deterministic strategies.
    let mut rngs: Vec<ChaCha8Rng> = (0..n)
        .map(|i| ChaCha8Rng::seed_from_u64(rng_seed.wrapping_add(i as u64)))
        .collect();
    let mut send_indices: Vec<u64> = vec![0; n];
    let mut transcript: Vec<ChatEvent> = Vec::new();

    // Ingest setup once per agent.
    for (agent, setup) in agents.iter_mut().zip(setups.into_iter()) {
        super::ingest_setup(agent, setup);
    }

    // Round-robin step loop with a generous safety bound.
    for _round in 0..256 {
        let mut any_progress = false;
        let mut any_unfinished = false;
        for i in 0..n {
            // Drain agent i's inbox into a snapshot iterator. We must
            // collect first so the borrow on `inboxes[i]` is released
            // before we mutably borrow `inboxes` again to fan-out.
            let inbound: Vec<ChatEvent> = std::mem::take(&mut inboxes[i]);
            let mut iter = inbound.into_iter();

            // Outbound collector for this step.
            let mut emitted: Vec<ChatEvent> = Vec::new();
            let status: StepStatus = {
                let mut emit = |mut ev: ChatEvent| {
                    ev.agent_idx = i;
                    emitted.push(ev);
                };
                agents[i].step(&mut iter, &mut emit, &mut rngs[i], &mut send_indices[i])
            };

            if status.had_inbound || status.had_outbound {
                any_progress = true;
            }
            if !status.is_done {
                any_unfinished = true;
            }

            // Fan out emissions to all OTHER agents' inboxes and append
            // to the transcript.
            for ev in &emitted {
                transcript.push(ev.clone());
            }
            for ev in emitted {
                for j in 0..n {
                    if j != i {
                        inboxes[j].push(ev.clone());
                    }
                }
            }
        }
        if !any_progress {
            break;
        }
        if !any_unfinished {
            break;
        }
    }

    let guesses: Vec<S::Guess> = agents.iter().map(|a| a.strategy.final_guess()).collect();
    (transcript, guesses)
}

/// Helper: every emitted ChatEvent parses as a CBCL message AND its head
/// performative name lies in the dialect's declared performative set
/// (CON-1120 post-condition #1).
fn assert_dialect_conformance(transcript: &[ChatEvent], dialect: &Dialect) {
    let allowed: BTreeSet<&str> = dialect.performative_names().into_iter().collect();
    for ev in transcript {
        let text = std::str::from_utf8(&ev.payload)
            .unwrap_or_else(|_| panic!("emitted non-utf8 payload"));
        let sexpr = parse(text)
            .unwrap_or_else(|e| panic!("emitted unparsable s-expr: {e:?}\n{text}"));
        let msg: Message = parse_message(&sexpr)
            .unwrap_or_else(|e| panic!("emitted non-CBCL message: {e}\n{text}"));
        let inner = msg.innermost_simple().unwrap_or(&msg);
        let perf = inner.performative().expect("simple message").name();
        assert!(
            allowed.contains(perf),
            "performative '{}' not declared in dialect '{}': allowed = {:?}",
            perf,
            dialect.name,
            allowed,
        );
    }
}

// =====================================================================
// PSI: honest-vs-honest, 50 games (TEST-1120)
// =====================================================================

#[test]
fn psi_honest_vs_honest_50_games() {
    const N_GAMES: u64 = 50;
    let universe: Vec<&str> = vec![
        "apple", "banana", "cherry", "orange", "grape", "lemon", "melon", "peach", "kiwi",
        "mango", "pear", "plum", "fig", "lime", "berry", "guava",
    ];
    let dialect = psi_dialect();

    for game in 0..N_GAMES {
        let mut rng = ChaCha8Rng::seed_from_u64(0x9e377_9b1u64.wrapping_add(game));
        let mut pool = universe.clone();
        pool.shuffle(&mut rng);
        let set_a: Vec<String> = pool[0..4].iter().map(|s| s.to_string()).collect();
        let set_b: Vec<String> = pool[2..6].iter().map(|s| s.to_string()).collect();

        let true_intersection: BTreeSet<String> = set_a
            .iter()
            .filter(|x| set_b.contains(*x))
            .cloned()
            .collect();

        let thread_root = format!("psi-game-{game}");
        let alice =
            CbclAgent::new(dialect.clone(), PsiCbclStrategy::new(), &*thread_root, "alice");
        let bob =
            CbclAgent::new(dialect.clone(), PsiCbclStrategy::new(), &*thread_root, "bob");

        let mut agents = [alice, bob];
        let (transcript, guesses) = run_game(&mut agents, vec![set_a, set_b], game);

        assert_dialect_conformance(&transcript, &dialect);

        let g0: BTreeSet<String> = guesses[0].iter().cloned().collect();
        let g1: BTreeSet<String> = guesses[1].iter().cloned().collect();
        assert_eq!(
            g0, true_intersection,
            "game {game}: alice's guess mismatched true intersection"
        );
        assert_eq!(
            g1, true_intersection,
            "game {game}: bob's guess mismatched true intersection"
        );

        // Quarantine should be empty in honest play.
        assert!(
            agents[0].quarantine.is_empty(),
            "game {game}: alice quarantined an honest message: {:?}",
            agents[0].quarantine
        );
        assert!(
            agents[1].quarantine.is_empty(),
            "game {game}: bob quarantined an honest message: {:?}",
            agents[1].quarantine
        );
    }
}

// =====================================================================
// Yao: honest-vs-honest, 50 games (TEST-1120)
// =====================================================================

#[test]
fn yao_honest_vs_honest_50_games() {
    const N_GAMES: u64 = 50;
    const RANGE: u64 = 1_000_000;
    let dialect = millionaire_dialect();

    for game in 0..N_GAMES {
        let mut rng = ChaCha8Rng::seed_from_u64(0xdeadu64.wrapping_add(game));
        let w_a: u64 = rng.gen_range(1..=RANGE);
        let w_b: u64 = rng.gen_range(1..=RANGE);
        let threshold = RANGE / 2;
        let bit_a = w_a >= threshold;
        let bit_b = w_b >= threshold;

        // Expected verdict from the agent's perspective.
        let expected_a = match (bit_a, bit_b) {
            (true, false) => YaoVerdict::Richer,
            (false, true) => YaoVerdict::Poorer,
            _ => YaoVerdict::Unknown,
        };
        let expected_b = match (bit_b, bit_a) {
            (true, false) => YaoVerdict::Richer,
            (false, true) => YaoVerdict::Poorer,
            _ => YaoVerdict::Unknown,
        };

        let thread_root = format!("yao-game-{game}");
        let alice = CbclAgent::new(
            dialect.clone(),
            MillionaireCbclStrategy::new(RANGE),
            &*thread_root,
            "alice",
        );
        let bob = CbclAgent::new(
            dialect.clone(),
            MillionaireCbclStrategy::new(RANGE),
            &*thread_root,
            "bob",
        );
        let mut agents = [alice, bob];
        let (transcript, guesses) = run_game(&mut agents, vec![w_a, w_b], game);

        assert_dialect_conformance(&transcript, &dialect);

        assert_eq!(
            guesses[0], expected_a,
            "game {game}: alice's verdict (w_a={w_a}, w_b={w_b}) mismatched"
        );
        assert_eq!(
            guesses[1], expected_b,
            "game {game}: bob's verdict (w_a={w_a}, w_b={w_b}) mismatched"
        );

        assert!(
            agents[0].quarantine.is_empty(),
            "game {game}: alice quarantined an honest message: {:?}",
            agents[0].quarantine
        );
        assert!(
            agents[1].quarantine.is_empty(),
            "game {game}: bob quarantined an honest message: {:?}",
            agents[1].quarantine
        );
    }
}

// =====================================================================
// DC: honest-vs-honest, 30 games (TEST-1120)
// =====================================================================

#[test]
fn dc_honest_vs_honest_30_games() {
    const N_GAMES: u64 = 30;
    let dialect = dining_dialect();

    for game in 0..N_GAMES {
        let mut rng = ChaCha8Rng::seed_from_u64(0xdcu64.wrapping_add(game));
        // Choose at most one paying diner per game.
        let payer: Option<u8> = match rng.gen_range(0..4u32) {
            0 => None,
            1 => Some(1),
            2 => Some(2),
            _ => Some(3),
        };
        let paid_bits = [
            payer == Some(1),
            payer == Some(2),
            payer == Some(3),
        ];
        let anyone_paid = paid_bits.iter().any(|&b| b);
        let expected = if anyone_paid {
            DcVerdict::Internal
        } else {
            DcVerdict::External
        };

        let thread_root = format!("dc-game-{game}");
        let pair_seed = format!("seed-{game}-{:016x}", rng.next_u64());
        let mut diners: Vec<CbclAgent<DiningCbclStrategy>> = (1..=3)
            .map(|i| {
                CbclAgent::new(
                    dialect.clone(),
                    DiningCbclStrategy::new(),
                    &*thread_root,
                    format!("diner-{i}"),
                )
            })
            .collect();
        let setups: Vec<DcSetup> = (1..=3u8)
            .map(|i| DcSetup {
                diner_idx: i,
                paid: paid_bits[(i - 1) as usize],
                pair_seed: pair_seed.clone(),
            })
            .collect();
        let (transcript, guesses) = run_game(&mut diners, setups, game);

        assert_dialect_conformance(&transcript, &dialect);

        for (i, g) in guesses.iter().enumerate() {
            assert_eq!(
                *g, expected,
                "game {game}: diner-{} verdict (paid={:?}) mismatched",
                i + 1,
                payer
            );
        }
        for (i, d) in diners.iter().enumerate() {
            assert!(
                d.quarantine.is_empty(),
                "game {game}: diner-{} quarantined honest message: {:?}",
                i + 1,
                d.quarantine
            );
        }
    }
}

// =====================================================================
// Quarantine isolation (TEST-1120)
// =====================================================================

#[test]
fn quarantine_isolation_garbage_inbound() {
    // Build a single PSI agent with a fixed set. Run the agent twice:
    // once with NO inbound, and once with a stream of garbage bytes
    // injected as inbound. Assert the final guess is identical, that
    // every garbage event lands in the quarantine, and that the agent
    // emits the same outbound transcript.

    let dialect = psi_dialect();
    let set: Vec<String> = ["apple", "banana", "cherry", "orange"]
        .into_iter()
        .map(String::from)
        .collect();

    // --- Run 1: no inbound. ---------------------------------------
    let mut alice_clean =
        CbclAgent::new(dialect.clone(), PsiCbclStrategy::new(), "qiso-thread", "alice");
    let mut rng_clean = ChaCha8Rng::seed_from_u64(0xc1ea9);
    let mut send_idx_clean = 0u64;
    super::ingest_setup(&mut alice_clean, set.clone());
    let mut clean_emissions: Vec<Vec<u8>> = Vec::new();
    for _ in 0..32 {
        let mut empty = std::iter::empty();
        let mut sink = |ev: ChatEvent| clean_emissions.push(ev.payload);
        let s = alice_clean.step(&mut empty, &mut sink, &mut rng_clean, &mut send_idx_clean);
        if s.is_done && !s.had_outbound {
            break;
        }
    }
    let clean_guess = alice_clean.strategy.final_guess();

    // --- Run 2: same agent config + ChaCha rng + setup, but with a
    // stream of garbage inbound bytes interleaved on every step. ---
    let mut alice_dirty =
        CbclAgent::new(dialect.clone(), PsiCbclStrategy::new(), "qiso-thread", "alice");
    let mut rng_dirty = ChaCha8Rng::seed_from_u64(0xc1ea9);
    let mut send_idx_dirty = 0u64;
    super::ingest_setup(&mut alice_dirty, set);
    let mut dirty_emissions: Vec<Vec<u8>> = Vec::new();
    let garbage_payloads: Vec<Vec<u8>> = vec![
        b"not an s-expression".to_vec(),
        b"(((".to_vec(),
        b"(unknown-perf :foo bar)".to_vec(),
        b"(psi-salt :caused-by deadbeef :thread other)".to_vec(),
        b"\xff\xfe\xfd nonsense".to_vec(),
        b"".to_vec(),
        b"(meta (define foo (cbcl) @nobody))".to_vec(),
    ];
    let mut next_send: u64 = 1000;
    for round in 0..32 {
        // Inject several garbage events on every round.
        let garbage: Vec<ChatEvent> = garbage_payloads
            .iter()
            .map(|p| {
                let ev = ChatEvent {
                    agent_idx: 99,
                    send_index: next_send,
                    payload: p.clone(),
                };
                next_send += 1;
                ev
            })
            .collect();
        let _ = round;
        let mut iter = garbage.into_iter();
        let mut sink = |ev: ChatEvent| dirty_emissions.push(ev.payload);
        let s = alice_dirty.step(&mut iter, &mut sink, &mut rng_dirty, &mut send_idx_dirty);
        if s.is_done && !s.had_outbound {
            break;
        }
    }
    let dirty_guess = alice_dirty.strategy.final_guess();

    assert_eq!(
        clean_guess, dirty_guess,
        "garbage inbound altered the agent's final guess"
    );
    assert_eq!(
        clean_emissions, dirty_emissions,
        "garbage inbound altered the agent's outbound transcript"
    );
    assert!(
        !alice_dirty.quarantine.is_empty(),
        "garbage inbound should have populated the quarantine buffer"
    );
    // Every quarantined entry must have one of the documented reasons.
    for q in &alice_dirty.quarantine {
        match q.reason {
            super::QuarantineReason::ParseError(_)
            | super::QuarantineReason::CausalViolation(_)
            | super::QuarantineReason::CausalUnknown => {}
        }
    }
}
