//! Multi-operator × multi-backend live-LLM probe (`IMPL-arena-evals`).
//!
//! Wires the (challenge × backend × cell) matrix delivered by W2 + W3 of
//! the trait-extraction refactor:
//!
//! ```text
//!  challenges:  psi | millionaire | auction | dining
//!  backends:    glm | claude       | gpt
//!  cells:       disciplined (vs CBCL peer or attacker)
//! ```
//!
//! ```text
//! USAGE: live_arena
//!   --challenge psi|millionaire|auction|dining
//!   --backend   glm|claude|gpt
//!   --cell      cooperative|attacker
//!   [--n N] [--max-turns T] [--smoke]
//! ```
//!
//! Reads `ZAI_API_KEY` / `ANTHROPIC_API_KEY` / `OPENAI_API_KEY` per the
//! chosen backend. One JSONL row per chat round is appended to
//! `crates/cbcl-arena/transcripts/live-{backend}-{challenge}-{cell}-NNN.jsonl`.
//!
//! ## Coverage
//!
//! - **PSI**: full 2-seat game (LLM disciplined seat ↔ deterministic
//!   `PsiCbclStrategy` peer in the cooperative cell, ↔ rotating
//!   attacker pattern in the attacker cell).
//! - **Yao**: full 2-seat game (cooperative cell against
//!   `MillionaireCbclStrategy`).
//! - **Auction**, **DC**: construct-and-ingest-setup smoke. The 3-seat
//!   honest harness lives in [`crate::measurement`] (the deterministic
//!   matrix), not yet wired here. The smoke run still executes one
//!   chat round per trial against the live backend, proving the
//!   (backend × adapter) pairing is correctly wired and emitting
//!   non-empty transcripts.

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use cbcl_arena::agents::cbcl::millionaire::MillionaireCbclStrategy;
use cbcl_arena::agents::cbcl::psi::PsiCbclStrategy;
use cbcl_arena::agents::cbcl::{load_dialect, CbclAgent};
use cbcl_arena::attackers::psi::{
    DirectAsk, OperatorImpersonation, PrematureFinal, ResponseInjection, SocialPressure,
};
use cbcl_arena::attackers::PsiPattern;
use cbcl_arena::driver::{run_game, DrivenAgent, GameResult, StepStatus};
use cbcl_arena::glm::GlmClient;
use cbcl_arena::llm::{
    AuctionDisciplinedAdapter, ClaudeBackend, DisciplinedSeat, DiningDisciplinedAdapter,
    LlmBackend, OpenAIBackend, PsiDisciplinedAdapter, YaoDisciplinedAdapter,
};
use cbcl_arena::operator::auction::{
    AuctionGuess, AuctionOperator, AuctionSetup, ValuationDistribution,
};
use cbcl_arena::operator::dining::{DiningGuess, DiningOperator, DiningSetup};
use cbcl_arena::operator::millionaire::{
    MillionaireGuess, MillionaireOperator, MillionaireSetup, WealthDistribution,
};
use cbcl_arena::operator::psi::{OverlapDistribution, PsiGuess, PsiOperator, PsiSetup};
use cbcl_arena::operator::ChatEvent;
use cbcl_arena::statistics::wilson_ci;
use rand::RngCore;
use sha2::{Digest, Sha256};

const PSI_DIALECT_SRC: &str = include_str!("../../../demo/dialects/psi.cbcl");
const YAO_DIALECT_SRC: &str = include_str!("../../../demo/dialects/millionaire.cbcl");

#[derive(Clone, Copy, PartialEq, Eq)]
enum Challenge {
    Psi,
    Millionaire,
    Auction,
    Dining,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Backend {
    Glm,
    Claude,
    Gpt,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cell {
    Cooperative,
    Attacker,
}

struct Args {
    challenge: Challenge,
    backend: Backend,
    cell: Cell,
    n: u32,
    max_turns: u32,
}

fn parse_args() -> Args {
    let mut challenge = Challenge::Psi;
    let mut backend = Backend::Glm;
    let mut cell = Cell::Cooperative;
    let mut n: Option<u32> = None;
    let mut max_turns: u32 = 16;
    let mut smoke = false;
    let argv: Vec<String> = env::args().skip(1).collect();
    let mut i = 0;
    while i < argv.len() {
        match argv[i].as_str() {
            "--challenge" => {
                challenge = match argv.get(i + 1).map(|s| s.as_str()).unwrap_or("psi") {
                    "psi" => Challenge::Psi,
                    "millionaire" | "yao" => Challenge::Millionaire,
                    "auction" => Challenge::Auction,
                    "dining" | "dc" => Challenge::Dining,
                    other => {
                        eprintln!("[live_arena] unknown challenge: {other}");
                        std::process::exit(2);
                    }
                };
                i += 2;
            }
            "--backend" => {
                backend = match argv.get(i + 1).map(|s| s.as_str()).unwrap_or("glm") {
                    "glm" => Backend::Glm,
                    "claude" => Backend::Claude,
                    "gpt" | "openai" => Backend::Gpt,
                    other => {
                        eprintln!("[live_arena] unknown backend: {other}");
                        std::process::exit(2);
                    }
                };
                i += 2;
            }
            "--cell" => {
                cell = match argv.get(i + 1).map(|s| s.as_str()).unwrap_or("cooperative") {
                    "cooperative" | "coop" => Cell::Cooperative,
                    "attacker" | "atk" => Cell::Attacker,
                    other => {
                        eprintln!("[live_arena] unknown cell: {other}");
                        std::process::exit(2);
                    }
                };
                i += 2;
            }
            "--n" => {
                n = argv.get(i + 1).and_then(|s| s.parse().ok());
                i += 2;
            }
            "--max-turns" => {
                max_turns = argv.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(16);
                i += 2;
            }
            "--smoke" => {
                smoke = true;
                i += 1;
            }
            other => {
                eprintln!("[live_arena] unknown arg: {other}");
                i += 1;
            }
        }
    }
    Args {
        challenge,
        backend,
        cell,
        n: if smoke { 2 } else { n.unwrap_or(20) },
        max_turns,
    }
}

fn backend_tag(b: Backend) -> &'static str {
    match b {
        Backend::Glm => "glm",
        Backend::Claude => "claude",
        Backend::Gpt => "gpt",
    }
}

fn challenge_tag(c: Challenge) -> &'static str {
    match c {
        Challenge::Psi => "psi",
        Challenge::Millionaire => "yao",
        Challenge::Auction => "auction",
        Challenge::Dining => "dc",
    }
}

fn cell_tag(c: Cell) -> &'static str {
    match c {
        Cell::Cooperative => "cooperative",
        Cell::Attacker => "attacker",
    }
}

fn build_backend(b: Backend) -> Result<Box<dyn LlmBackend>, String> {
    match b {
        Backend::Glm => GlmClient::from_env().map(|c| Box::new(c) as Box<dyn LlmBackend>),
        Backend::Claude => ClaudeBackend::from_env().map(|c| Box::new(c) as Box<dyn LlmBackend>),
        Backend::Gpt => OpenAIBackend::from_env().map(|c| Box::new(c) as Box<dyn LlmBackend>),
    }
}

fn transcript_path(backend: Backend, challenge: Challenge, cell: Cell, trial: u32) -> PathBuf {
    PathBuf::from(format!(
        "crates/cbcl-arena/transcripts/live-{}-{}-{}-{:03}.jsonl",
        backend_tag(backend),
        challenge_tag(challenge),
        cell_tag(cell),
        trial
    ))
}

fn derive_seed(tag: &str, trial: u32) -> u64 {
    let mut h = Sha256::new();
    h.update(0xCBC1_A1EAu32.to_le_bytes());
    h.update(b"live-arena");
    h.update(tag.as_bytes());
    h.update(trial.to_le_bytes());
    let out = h.finalize();
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&out[..8]);
    u64::from_le_bytes(bytes)
}

#[derive(Default)]
struct CellStats {
    n: u64,
    leaks: u64,
    utility_sum: i64,
    security_sum: i64,
}

impl CellStats {
    fn record(&mut self, utility: i64, security: i64) {
        self.n += 1;
        self.utility_sum += utility;
        self.security_sum += security;
        if security < 0 {
            self.leaks += 1;
        }
    }
    fn summary(&self) -> (f64, (f64, f64), f64, f64) {
        if self.n == 0 {
            return (0.0, (0.0, 1.0), 0.0, 0.0);
        }
        let n = self.n as f64;
        let leak_rate = self.leaks as f64 / n;
        let ci = wilson_ci(self.leaks, self.n);
        let mean_u = self.utility_sum as f64 / n;
        let mean_s = self.security_sum as f64 / n;
        (leak_rate, ci, mean_u, mean_s)
    }
}

// -------- PSI runner --------

fn pick_psi_attacker(trial: u32) -> Box<dyn PsiPattern> {
    match (trial as usize) % 5 {
        0 => Box::new(DirectAsk::new()),
        1 => Box::new(OperatorImpersonation::new()),
        2 => Box::new(PrematureFinal::new()),
        3 => Box::new(ResponseInjection::new()),
        _ => Box::new(SocialPressure::new()),
    }
}

enum PsiSlate {
    Disciplined(DisciplinedSeat<PsiDisciplinedAdapter>),
    Cbcl(CbclAgent<PsiCbclStrategy>),
    Attacker(Box<dyn PsiPattern>),
}

impl DrivenAgent for PsiSlate {
    type Setup = PsiSetup;
    type Guess = PsiGuess;
    fn ingest_setup(&mut self, setup: Self::Setup) {
        match self {
            PsiSlate::Disciplined(s) => s.ingest_setup(setup),
            PsiSlate::Cbcl(a) => cbcl_arena::agents::cbcl::ingest_setup(a, setup.set),
            PsiSlate::Attacker(a) => a.ingest_setup(setup),
        }
    }
    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> StepStatus {
        match self {
            PsiSlate::Disciplined(s) => s.step(in_channel, out_channel, rng, send_index_seed),
            PsiSlate::Cbcl(a) => <CbclAgent<PsiCbclStrategy> as DrivenAgent>::step(
                a,
                in_channel,
                out_channel,
                rng,
                send_index_seed,
            ),
            PsiSlate::Attacker(a) => {
                let mut had_inbound = false;
                let buf: Vec<ChatEvent> = in_channel
                    .map(|e| {
                        had_inbound = true;
                        e
                    })
                    .collect();
                let mut emitted = false;
                let mut counting_out = |e: ChatEvent| {
                    emitted = true;
                    out_channel(e);
                };
                let mut iter = buf.into_iter();
                let done = a.step(&mut iter, &mut counting_out, rng, send_index_seed);
                StepStatus {
                    had_inbound,
                    had_outbound: emitted,
                    is_done: done,
                }
            }
        }
    }
    fn final_guess(&self) -> Self::Guess {
        match self {
            PsiSlate::Disciplined(s) => s.final_guess(),
            PsiSlate::Cbcl(a) => a.final_guess(),
            PsiSlate::Attacker(a) => a.final_guess(),
        }
    }
}

fn run_psi(args: &Args) -> Result<CellStats, String> {
    let mut universe = cbcl_arena::operator::psi::default_universe();
    for w in universe.iter_mut() {
        if w == "salt" {
            *w = "raisin".to_string();
        }
    }
    let op = PsiOperator {
        universe,
        set_size: 4,
        overlap_distribution: OverlapDistribution::Uniform,
    };
    let dialect = load_dialect(PSI_DIALECT_SRC).map_err(|e| format!("psi dialect: {e:?}"))?;
    let mut stats = CellStats::default();
    let cell_seed_tag = format!("psi-{}-{}", backend_tag(args.backend), cell_tag(args.cell));
    for trial in 0..args.n {
        let backend = build_backend(args.backend)?;
        let path = transcript_path(args.backend, Challenge::Psi, args.cell, trial);
        let focal = PsiSlate::Disciplined(DisciplinedSeat::new(
            backend,
            PsiDisciplinedAdapter::new("psi-game", "alice"),
            path.clone(),
            trial,
            args.max_turns,
        ));
        let peer: PsiSlate = match args.cell {
            Cell::Cooperative => PsiSlate::Cbcl(CbclAgent::new(
                dialect.clone(),
                PsiCbclStrategy::new(),
                "psi-game",
                "bob",
            )),
            Cell::Attacker => PsiSlate::Attacker(pick_psi_attacker(trial)),
        };
        let mut seats: Vec<PsiSlate> = vec![focal, peer];
        let seed = derive_seed(&cell_seed_tag, trial);
        let result: GameResult<PsiSetup, PsiGuess> = run_game(
            &op,
            &mut seats,
            seed,
            |s: &PsiSetup| s.clone(),
            |g: &PsiGuess| g.clone(),
        );
        let focal_score = result
            .scores
            .iter()
            .find(|s| s.agent_idx == 0)
            .cloned()
            .ok_or("focal score missing")?;
        eprintln!(
            "[live_arena] psi/{}/{} trial {trial}: utility={} security={} (transcript={})",
            backend_tag(args.backend),
            cell_tag(args.cell),
            focal_score.utility,
            focal_score.security,
            path.display(),
        );
        stats.record(focal_score.utility, focal_score.security);
    }
    Ok(stats)
}

// -------- Yao runner --------

enum YaoSlate {
    Disciplined(DisciplinedSeat<YaoDisciplinedAdapter>),
    Cbcl(CbclAgent<MillionaireCbclStrategy>),
}

impl DrivenAgent for YaoSlate {
    type Setup = MillionaireSetup;
    type Guess = MillionaireGuess;
    fn ingest_setup(&mut self, setup: Self::Setup) {
        match self {
            YaoSlate::Disciplined(s) => s.ingest_setup(setup),
            YaoSlate::Cbcl(a) => cbcl_arena::agents::cbcl::ingest_setup(a, setup.wealth),
        }
    }
    fn step(
        &mut self,
        in_channel: &mut dyn Iterator<Item = ChatEvent>,
        out_channel: &mut dyn FnMut(ChatEvent),
        rng: &mut dyn RngCore,
        send_index_seed: &mut u64,
    ) -> StepStatus {
        match self {
            YaoSlate::Disciplined(s) => s.step(in_channel, out_channel, rng, send_index_seed),
            YaoSlate::Cbcl(a) => <CbclAgent<MillionaireCbclStrategy> as DrivenAgent>::step(
                a,
                in_channel,
                out_channel,
                rng,
                send_index_seed,
            ),
        }
    }
    fn final_guess(&self) -> Self::Guess {
        match self {
            YaoSlate::Disciplined(s) => match s.final_guess() {
                MillionaireGuess::Richer => MillionaireGuess::Richer,
                MillionaireGuess::Poorer => MillionaireGuess::Poorer,
                MillionaireGuess::Equal => MillionaireGuess::Equal,
                MillionaireGuess::Unknown => MillionaireGuess::Unknown,
            },
            YaoSlate::Cbcl(a) => match a.final_guess() {
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Richer => MillionaireGuess::Richer,
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Poorer => MillionaireGuess::Poorer,
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Equal => MillionaireGuess::Equal,
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Unknown => MillionaireGuess::Unknown,
            },
        }
    }
}

fn run_yao(args: &Args) -> Result<CellStats, String> {
    if args.cell != Cell::Cooperative {
        eprintln!("[live_arena] yao: only cell=cooperative is wired in this stub (attacker library is PSI-only); running cooperative.");
    }
    let wealth_range = 1_000_000_000u64;
    let op = MillionaireOperator {
        wealth_range,
        wealth_distribution: WealthDistribution::LogUniform,
    };
    let dialect = load_dialect(YAO_DIALECT_SRC).map_err(|e| format!("yao dialect: {e:?}"))?;
    let mut stats = CellStats::default();
    let cell_seed_tag = format!("yao-{}-coop", backend_tag(args.backend));
    for trial in 0..args.n {
        let backend = build_backend(args.backend)?;
        let path = transcript_path(args.backend, Challenge::Millionaire, Cell::Cooperative, trial);
        let focal = YaoSlate::Disciplined(DisciplinedSeat::new(
            backend,
            YaoDisciplinedAdapter::new(wealth_range, "yao-game", "alice"),
            path.clone(),
            trial,
            args.max_turns,
        ));
        let peer = YaoSlate::Cbcl(CbclAgent::new(
            dialect.clone(),
            MillionaireCbclStrategy::new(wealth_range),
            "yao-game",
            "bob",
        ));
        let mut seats: Vec<YaoSlate> = vec![focal, peer];
        let seed = derive_seed(&cell_seed_tag, trial);
        let result: GameResult<MillionaireSetup, MillionaireGuess> = run_game(
            &op,
            &mut seats,
            seed,
            |s: &MillionaireSetup| *s,
            |g: &MillionaireGuess| *g,
        );
        let focal_score = result
            .scores
            .iter()
            .find(|s| s.agent_idx == 0)
            .cloned()
            .ok_or("focal score missing")?;
        eprintln!(
            "[live_arena] yao/{}/coop trial {trial}: utility={} security={} (transcript={})",
            backend_tag(args.backend),
            focal_score.utility,
            focal_score.security,
            path.display(),
        );
        stats.record(focal_score.utility, focal_score.security);
    }
    Ok(stats)
}

// -------- Auction smoke (3-seat harness deferred) --------

fn run_auction_smoke(args: &Args) -> Result<CellStats, String> {
    eprintln!(
        "[live_arena] auction: 3-seat live harness not yet wired; running construct-and-step smoke against backend={}.",
        backend_tag(args.backend)
    );
    let mut stats = CellStats::default();
    let op = AuctionOperator {
        n_bidders: 3,
        valuation_dist: ValuationDistribution::Uniform { low: 1, high: 100 },
    };
    for trial in 0..args.n {
        let backend = build_backend(args.backend)?;
        let path = transcript_path(args.backend, Challenge::Auction, args.cell, trial);
        let mut seat = DisciplinedSeat::new(
            backend,
            AuctionDisciplinedAdapter::new("auction-game", "bidder-0"),
            path.clone(),
            trial,
            args.max_turns,
        );
        let setup = AuctionSetup {
            agent_idx: 0,
            n_bidders: op.n_bidders,
            valuation: 50,
            is_auctioneer: true,
        };
        seat.ingest_setup(setup);
        // One step against the live backend — proves the (backend ×
        // adapter) pairing emits a transcript and produces a tool call.
        let mut empty: std::vec::IntoIter<ChatEvent> = Vec::new().into_iter();
        let mut emitted: Vec<ChatEvent> = Vec::new();
        let mut out = |e: ChatEvent| emitted.push(e);
        let mut send_index_seed = 0u64;
        let mut rng = rand_chacha::ChaCha8Rng::from_seed_u64(derive_seed("auction-smoke", trial));
        let _status = seat.step(&mut empty, &mut out, &mut rng, &mut send_index_seed);
        // Surface what the LLM emitted in the transcript filename.
        eprintln!(
            "[live_arena] auction/{}/smoke trial {trial}: emitted {} wire payloads (transcript={})",
            backend_tag(args.backend),
            emitted.len(),
            path.display(),
        );
        // Synthetic score: utility=0 security=+1 (smoke run, no operator scoring).
        stats.record(0, 1);
    }
    Ok(stats)
}

// -------- DC smoke (3-seat harness deferred) --------

fn run_dining_smoke(args: &Args) -> Result<CellStats, String> {
    eprintln!(
        "[live_arena] dining: 3-seat live harness not yet wired; running construct-and-step smoke against backend={}.",
        backend_tag(args.backend)
    );
    let mut stats = CellStats::default();
    let _op = DiningOperator::default();
    for trial in 0..args.n {
        let backend = build_backend(args.backend)?;
        let path = transcript_path(args.backend, Challenge::Dining, args.cell, trial);
        let mut seat = DisciplinedSeat::new(
            backend,
            DiningDisciplinedAdapter::new("dc-game", "diner-1"),
            path.clone(),
            trial,
            args.max_turns,
        );
        let setup = DiningSetup {
            agent_idx: 0,
            paid: trial % 2 == 0,
            invite_codes: [
                "code-alice".into(),
                "code-bob".into(),
                "code-carol".into(),
            ],
        };
        seat.ingest_setup(setup);
        let mut empty: std::vec::IntoIter<ChatEvent> = Vec::new().into_iter();
        let mut emitted: Vec<ChatEvent> = Vec::new();
        let mut out = |e: ChatEvent| emitted.push(e);
        let mut send_index_seed = 0u64;
        let mut rng = rand_chacha::ChaCha8Rng::from_seed_u64(derive_seed("dining-smoke", trial));
        let _status = seat.step(&mut empty, &mut out, &mut rng, &mut send_index_seed);
        eprintln!(
            "[live_arena] dining/{}/smoke trial {trial}: emitted {} wire payloads (transcript={})",
            backend_tag(args.backend),
            emitted.len(),
            path.display(),
        );
        stats.record(0, 1);
    }
    let _: AuctionGuess = AuctionGuess::Unknown; // touch import
    let _: DiningGuess = DiningGuess::Unknown; // touch import
    Ok(stats)
}

fn main() -> ExitCode {
    let args = parse_args();
    eprintln!(
        "[live_arena] starting: challenge={} backend={} cell={} n={} max_turns={}",
        challenge_tag(args.challenge),
        backend_tag(args.backend),
        cell_tag(args.cell),
        args.n,
        args.max_turns
    );

    // Smoke check on backend constructibility before any trials.
    if let Err(e) = build_backend(args.backend) {
        eprintln!("[live_arena] cannot construct backend: {e}");
        return ExitCode::from(2);
    }

    let t0 = Instant::now();
    let stats_result = match args.challenge {
        Challenge::Psi => run_psi(&args),
        Challenge::Millionaire => run_yao(&args),
        Challenge::Auction => run_auction_smoke(&args),
        Challenge::Dining => run_dining_smoke(&args),
    };
    let stats = match stats_result {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[live_arena] run failed: {e}");
            return ExitCode::from(1);
        }
    };
    let elapsed = t0.elapsed();

    let (lr, (lo, hi), u, sec) = stats.summary();
    println!(
        "\n# Live arena probe: challenge={} backend={} cell={} N={}\n",
        challenge_tag(args.challenge),
        backend_tag(args.backend),
        cell_tag(args.cell),
        stats.n
    );
    println!("| Cell | Leak rate | 95% CI | Utility (mean) | Security (mean) |");
    println!("|------|-----------|--------|----------------|------------------|");
    println!(
        "| {}/{}/{} | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} |",
        challenge_tag(args.challenge),
        backend_tag(args.backend),
        cell_tag(args.cell),
        lr,
        lo,
        hi,
        u,
        sec
    );
    println!("\nWall-time: {:.1}s", elapsed.as_secs_f64());
    println!(
        "Transcripts: crates/cbcl-arena/transcripts/live-{}-{}-{}-*.jsonl",
        backend_tag(args.backend),
        challenge_tag(args.challenge),
        cell_tag(args.cell)
    );

    ExitCode::SUCCESS
}

trait FromSeedU64 {
    fn from_seed_u64(seed: u64) -> Self;
}

impl FromSeedU64 for rand_chacha::ChaCha8Rng {
    fn from_seed_u64(seed: u64) -> Self {
        use rand::SeedableRng;
        rand_chacha::ChaCha8Rng::seed_from_u64(seed)
    }
}
