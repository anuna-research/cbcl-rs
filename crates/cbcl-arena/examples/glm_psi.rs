//! Live-LLM probe of the PSI arena challenge using GLM-5.1.
//!
//! Runs two cells back-to-back over the same operator setup:
//!
//! 1. **Free-chat.** The LLM has no tool restriction; it sends raw
//!    chat messages.
//! 2. **Disciplined.** The LLM is restricted to dialect-shaped tool
//!    calls; the only plaintext channel is the `members` list of
//!    `claim_intersection` / `finalize`.
//!
//! ```text
//! USAGE: glm_psi [--n N] [--cell free|disciplined|both] [--smoke]
//! ```
//!
//! Reads `ZAI_API_KEY` from the environment. Logs one JSONL row per
//! API call to `crates/cbcl-arena/transcripts/glm51-<cell>-<NNN>.jsonl`.

use std::env;
use std::process::ExitCode;
use std::time::Instant;

use cbcl_arena::agents::cbcl::psi::PsiCbclStrategy;
use cbcl_arena::agents::cbcl::{load_dialect, CbclAgent};
use cbcl_arena::attackers::psi::{
    DirectAsk, OperatorImpersonation, PrematureFinal, ResponseInjection, SocialPressure,
};
use cbcl_arena::attackers::PsiPattern;
use cbcl_arena::driver::{run_game, DrivenAgent, GameResult, StepStatus};
use cbcl_arena::glm::{
    new_disciplined_seat, transcript_path_for, GlmCbclNativeSeat, GlmClient,
    GlmDisciplinedSeat, GlmFreeChatSeat,
};
use cbcl_arena::llm::{CodexBackend, LlmBackend};
use cbcl_arena::operator::psi::{OverlapDistribution, PsiGuess, PsiOperator, PsiSetup};
use cbcl_arena::operator::ChatEvent;
use cbcl_arena::statistics::wilson_ci;

const PSI_DIALECT_SRC: &str = include_str!("../../../demo/dialects/psi.cbcl");
use rand::RngCore;
use sha2::{Digest, Sha256};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cell {
    Free,
    Disciplined,
    Cooperative,
    Native,
    NativeAttacker,
    Both,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BackendKind {
    /// Z.ai GLM-5.1 (the original live-LLM probe; ZAI_API_KEY).
    Glm,
    /// OpenAI gpt-5.5 via the local codex-responses-proxy (no API key;
    /// uses ChatGPT/Codex subscription auth from ~/.codex/auth.json).
    Codex,
}

impl BackendKind {
    /// Short transcript-filename tag (`glm51`, `gpt55`).
    fn provider_tag(self) -> &'static str {
        match self {
            BackendKind::Glm => "glm51",
            BackendKind::Codex => "gpt55",
        }
    }

    /// Construct a fresh backend instance.
    fn make(self) -> Box<dyn LlmBackend> {
        match self {
            BackendKind::Glm => Box::new(GlmClient::from_env().expect("ZAI_API_KEY")),
            BackendKind::Codex => Box::new(CodexBackend::new()),
        }
    }
}

struct Args {
    n: u32,
    cell: Cell,
    smoke: bool,
    max_turns: u32,
    backend: BackendKind,
}

fn parse_args() -> Args {
    let mut n: Option<u32> = None;
    let mut cell = Cell::Both;
    let mut smoke = false;
    let mut max_turns: u32 = 16;
    let mut backend = BackendKind::Glm;
    let argv: Vec<String> = env::args().skip(1).collect();
    let mut i = 0;
    while i < argv.len() {
        match argv[i].as_str() {
            "--n" => {
                let v = argv.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(20);
                n = Some(v);
                i += 2;
            }
            "--cell" => {
                let v = argv.get(i + 1).map(|s| s.as_str()).unwrap_or("both");
                cell = match v {
                    "free" => Cell::Free,
                    "disciplined" => Cell::Disciplined,
                    "cooperative" => Cell::Cooperative,
                    "native" => Cell::Native,
                    "native-attacker" => Cell::NativeAttacker,
                    _ => Cell::Both,
                };
                i += 2;
            }
            "--smoke" => {
                smoke = true;
                i += 1;
            }
            "--max-turns" => {
                let v = argv.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(16);
                max_turns = v;
                i += 2;
            }
            "--backend" => {
                let v = argv.get(i + 1).map(|s| s.as_str()).unwrap_or("glm");
                backend = match v {
                    "glm" | "glm51" | "glm-5.1" => BackendKind::Glm,
                    "codex" | "gpt55" | "gpt-5.5" => BackendKind::Codex,
                    other => {
                        eprintln!("[glm_psi] unknown --backend {other}, defaulting to glm");
                        BackendKind::Glm
                    }
                };
                i += 2;
            }
            _ => {
                eprintln!("[glm_psi] unknown arg: {}", argv[i]);
                i += 1;
            }
        }
    }
    Args {
        n: if smoke { 2 } else { n.unwrap_or(20) },
        cell,
        smoke,
        max_turns,
        backend,
    }
}

fn psi_operator() -> PsiOperator {
    // Same `salt` -> `raisin` substitution the deterministic measurement
    // module uses to avoid the naming collision with the `psi-salt`
    // performative's `:salt` keyword.
    let mut universe = cbcl_arena::operator::psi::default_universe();
    for w in universe.iter_mut() {
        if w == "salt" {
            *w = "raisin".to_string();
        }
    }
    PsiOperator {
        universe,
        set_size: 4,
        overlap_distribution: OverlapDistribution::Uniform,
    }
}

/// SHA-256-based seed derivation: hash the tag bytes and take the first
/// 8 bytes as a u64.
fn derive_seed(cell_name: &str, trial: u32) -> u64 {
    let mut h = Sha256::new();
    h.update(0xCBC1_A1EAu32.to_le_bytes());
    h.update(b"glm51-psi");
    h.update(cell_name.as_bytes());
    h.update(trial.to_le_bytes());
    let out = h.finalize();
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&out[..8]);
    u64::from_le_bytes(bytes)
}

fn pick_attacker(trial: u32) -> Box<dyn PsiPattern> {
    let i = (trial as usize) % 5;
    match i {
        0 => Box::new(DirectAsk::new()),
        1 => Box::new(OperatorImpersonation::new()),
        2 => Box::new(PrematureFinal::new()),
        3 => Box::new(ResponseInjection::new()),
        _ => Box::new(SocialPressure::new()),
    }
}

/// Mixed-seat enum so the driver can drive a 2-seat slate of
/// `(GLM seat, Box<dyn PsiPattern>)`.
enum PsiCellSeat {
    Free(GlmFreeChatSeat),
    Disciplined(GlmDisciplinedSeat),
    Native(GlmCbclNativeSeat),
    Attacker(Box<dyn PsiPattern>),
    Cbcl(CbclAgent<PsiCbclStrategy>),
}

impl DrivenAgent for PsiCellSeat {
    type Setup = PsiSetup;
    type Guess = PsiGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        match self {
            PsiCellSeat::Free(s) => s.ingest_setup(setup),
            PsiCellSeat::Disciplined(s) => s.ingest_setup(setup),
            PsiCellSeat::Native(s) => s.ingest_setup(setup),
            PsiCellSeat::Attacker(a) => a.ingest_setup(setup),
            PsiCellSeat::Cbcl(a) => {
                // PsiCbclStrategy::Setup is Vec<String> (the set itself).
                cbcl_arena::agents::cbcl::ingest_setup(a, setup.set);
            }
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
            PsiCellSeat::Free(s) => s.step(in_channel, out_channel, rng, send_index_seed),
            PsiCellSeat::Disciplined(s) => {
                s.step(in_channel, out_channel, rng, send_index_seed)
            }
            PsiCellSeat::Native(s) => s.step(in_channel, out_channel, rng, send_index_seed),
            PsiCellSeat::Attacker(a) => {
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
            PsiCellSeat::Cbcl(a) => <CbclAgent<PsiCbclStrategy> as DrivenAgent>::step(
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
            PsiCellSeat::Free(s) => s.final_guess(),
            PsiCellSeat::Disciplined(s) => s.final_guess(),
            PsiCellSeat::Native(s) => s.final_guess(),
            PsiCellSeat::Attacker(a) => a.final_guess(),
            PsiCellSeat::Cbcl(a) => a.final_guess(),
        }
    }
}

#[derive(Default)]
struct CellStats {
    leaks: u64,
    n: u64,
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

fn run_one_trial(
    cell_name: &str,
    trial: u32,
    max_turns: u32,
    backend_kind: BackendKind,
) -> (i64, i64) {
    let backend = backend_kind.make();
    let path = transcript_path_for(backend_kind.provider_tag(), cell_name, trial);
    let (focal, peer) = match cell_name {
        "free" => (
            PsiCellSeat::Free(GlmFreeChatSeat::new(
                backend,
                path.clone(),
                trial,
                max_turns,
            )),
            PsiCellSeat::Attacker(pick_attacker(trial)),
        ),
        "disciplined" => (
            PsiCellSeat::Disciplined(new_disciplined_seat(
                backend,
                path.clone(),
                trial,
                max_turns,
            )),
            PsiCellSeat::Attacker(pick_attacker(trial)),
        ),
        "cooperative" => {
            let dialect = load_dialect(PSI_DIALECT_SRC).expect("psi dialect");
            (
                PsiCellSeat::Disciplined(new_disciplined_seat(
                    backend,
                    path.clone(),
                    trial,
                    max_turns,
                )),
                PsiCellSeat::Cbcl(CbclAgent::new(
                    dialect,
                    PsiCbclStrategy::new(),
                    "psi-game",
                    "bob",
                )),
            )
        }
        "native-cooperative" => {
            let dialect = load_dialect(PSI_DIALECT_SRC).expect("psi dialect");
            (
                PsiCellSeat::Native(GlmCbclNativeSeat::new(
                    backend,
                    path.clone(),
                    trial,
                    max_turns,
                    dialect.clone(),
                    "psi-game",
                    "alice",
                )),
                PsiCellSeat::Cbcl(CbclAgent::new(
                    dialect,
                    PsiCbclStrategy::new(),
                    "psi-game",
                    "bob",
                )),
            )
        }
        "native-attacker" => {
            let dialect = load_dialect(PSI_DIALECT_SRC).expect("psi dialect");
            (
                PsiCellSeat::Native(GlmCbclNativeSeat::new(
                    backend,
                    path.clone(),
                    trial,
                    max_turns,
                    dialect,
                    "psi-game",
                    "alice",
                )),
                PsiCellSeat::Attacker(pick_attacker(trial)),
            )
        }
        other => panic!("unknown cell: {other}"),
    };
    let mut seats: Vec<PsiCellSeat> = vec![focal, peer];
    let op = psi_operator();
    let seed = derive_seed(cell_name, trial);
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
        .expect("focal score");
    eprintln!(
        "[glm_psi] {cell_name} trial {trial}: utility={} security={} (transcript={})",
        focal_score.utility,
        focal_score.security,
        path.display(),
    );
    (focal_score.utility, focal_score.security)
}

fn run_cell(cell_name: &str, n: u32, max_turns: u32, backend: BackendKind) -> CellStats {
    let mut stats = CellStats::default();
    for trial in 0..n {
        let (u, s) = run_one_trial(cell_name, trial, max_turns, backend);
        stats.record(u, s);
    }
    stats
}

fn main() -> ExitCode {
    let args = parse_args();
    eprintln!(
        "[glm_psi] starting: n={} cell={} smoke={} max_turns={}",
        args.n,
        match args.cell {
            Cell::Free => "free",
            Cell::Disciplined => "disciplined",
            Cell::Cooperative => "cooperative",
            Cell::Native => "native",
            Cell::NativeAttacker => "native-attacker",
            Cell::Both => "both",
        },
        args.smoke,
        args.max_turns,
    );

    if args.backend == BackendKind::Glm {
        if let Err(e) = GlmClient::from_env() {
            eprintln!("[glm_psi] cannot construct client: {e}");
            return ExitCode::from(2);
        }
    }
    // Codex backend has no env-side precheck — the proxy must be running
    // on 127.0.0.1:8787; first call will surface a connect error if not.

    let t0 = Instant::now();
    let mut free_stats: Option<CellStats> = None;
    let mut disc_stats: Option<CellStats> = None;
    let mut coop_stats: Option<CellStats> = None;
    let mut native_stats: Option<CellStats> = None;
    if matches!(args.cell, Cell::Free | Cell::Both) {
        free_stats = Some(run_cell("free", args.n, args.max_turns, args.backend));
    }
    if matches!(args.cell, Cell::Disciplined | Cell::Both) {
        disc_stats = Some(run_cell("disciplined", args.n, args.max_turns, args.backend));
    }
    if matches!(args.cell, Cell::Cooperative) {
        coop_stats = Some(run_cell("cooperative", args.n, args.max_turns, args.backend));
    }
    if matches!(args.cell, Cell::Native) {
        native_stats = Some(run_cell("native-cooperative", args.n, args.max_turns, args.backend));
    }
    let mut native_atk_stats: Option<CellStats> = None;
    if matches!(args.cell, Cell::NativeAttacker) {
        native_atk_stats = Some(run_cell("native-attacker", args.n, args.max_turns, args.backend));
    }
    let elapsed = t0.elapsed();

    let model_label = match args.backend {
        BackendKind::Glm => "GLM-5.1",
        BackendKind::Codex => "GPT-5.5 (Codex)",
    };
    let tag = args.backend.provider_tag();
    println!("# {model_label} PSI live-LLM probe (N={} per cell)\n", args.n);
    println!("| Cell | Leak rate | 95% CI | Utility (mean) | Security (mean) | Transcripts |");
    println!("|------|-----------|--------|----------------|------------------|-------------|");
    if let Some(s) = &free_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Free-chat   | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-free-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &disc_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Disciplined | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-disciplined-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &coop_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Cooperative | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-cooperative-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &native_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Native (CBCL) | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-native-cooperative-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &native_atk_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Native × Attacker | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-native-attacker-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    println!(
        "\nWall-time: {:.1}s",
        elapsed.as_secs_f64()
    );

    ExitCode::SUCCESS
}
