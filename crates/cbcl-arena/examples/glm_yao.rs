//! Live-LLM probe of the Yao Millionaire arena challenge using GLM-5.1.
//!
//! Mirrors [`glm_psi`] but for the `arena-millionaire` dialect. Runs
//! cells over the same operator setup:
//!
//! 1. **Free-chat.** The LLM has no tool restriction; it sends raw
//!    chat messages.
//! 2. **Disciplined.** The LLM is restricted to dialect-shaped tool
//!    calls (`propose_threshold`, `commit_bit`, `reveal_bit`,
//!    `submit_verdict`); all crypto + serialisation handled by the
//!    shim.
//! 3. **Cooperative.** Disciplined LLM seat against a deterministic
//!    `MillionaireCbclStrategy` peer (the structural-conformance
//!    cell — security must hold under honest play).
//! 4. **Native.** The LLM emits real Yao dialect S-expressions, with
//!    parser + verify_causal gating each emission.
//! 5. **Native-attacker.** Native LLM seat against a rotating
//!    Yao-attacker library.
//!
//! ```text
//! USAGE: glm_yao
//!   [--n N]
//!   [--cell free|disciplined|cooperative|native|native-attacker|both]
//!   [--smoke]
//! ```
//!
//! Reads `ZAI_API_KEY` from the environment. Logs one JSONL row per API
//! call to `crates/cbcl-arena/transcripts/glm51-yao-<cell>-<NNN>.jsonl`.

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use cbcl_arena::agents::cbcl::millionaire::MillionaireCbclStrategy;
use cbcl_arena::agents::cbcl::{load_dialect, CbclAgent};
use cbcl_arena::attackers::millionaire::{
    BracketFlooding, CompareByNaming, DirectAsk, OperatorImpersonation, PrematureFinal,
    ProtocolMimicry, RangeReframe, SocialPressure, ThresholdInjection,
};
use cbcl_arena::attackers::MillionairePattern;
use cbcl_arena::driver::{run_game, DrivenAgent, GameResult, StepStatus};
use cbcl_arena::glm::{GlmCbclNativeYaoSeat, GlmClient, GlmFreeChatYaoSeat};
use cbcl_arena::llm::{CodexBackend, DisciplinedSeat, LlmBackend, YaoDisciplinedAdapter};
use cbcl_arena::operator::millionaire::{
    MillionaireGuess, MillionaireOperator, MillionaireSetup, WealthDistribution,
};
use cbcl_arena::operator::ChatEvent;
use cbcl_arena::statistics::wilson_ci;

const YAO_DIALECT_SRC: &str = include_str!("../../../demo/dialects/millionaire.cbcl");

use rand::RngCore;
use sha2::{Digest, Sha256};

/// Wealth range for the Yao operator; matches `live_arena.rs`'s setting.
const WEALTH_RANGE: u64 = 1_000_000_000;

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
    Glm,
    Codex,
}

impl BackendKind {
    fn provider_tag(self) -> &'static str {
        match self {
            BackendKind::Glm => "glm51",
            BackendKind::Codex => "gpt55",
        }
    }
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
                        eprintln!("[glm_yao] unknown --backend {other}, defaulting to glm");
                        BackendKind::Glm
                    }
                };
                i += 2;
            }
            _ => {
                eprintln!("[glm_yao] unknown arg: {}", argv[i]);
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

fn yao_operator() -> MillionaireOperator {
    MillionaireOperator {
        wealth_range: WEALTH_RANGE,
        wealth_distribution: WealthDistribution::LogUniform,
    }
}

fn derive_seed(cell_name: &str, trial: u32) -> u64 {
    let mut h = Sha256::new();
    h.update(0xCBC1_A1EAu32.to_le_bytes());
    h.update(b"glm51-yao");
    h.update(cell_name.as_bytes());
    h.update(trial.to_le_bytes());
    let out = h.finalize();
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&out[..8]);
    u64::from_le_bytes(bytes)
}

/// Pick a Yao attacker, rotating through the published library by trial
/// index. Mirrors `glm_psi::pick_attacker`.
fn pick_attacker(trial: u32) -> Box<dyn MillionairePattern> {
    let i = (trial as usize) % 9;
    match i {
        0 => Box::new(DirectAsk::new()),
        1 => Box::new(CompareByNaming::new()),
        2 => Box::new(ThresholdInjection::new()),
        3 => Box::new(SocialPressure::new()),
        4 => Box::new(OperatorImpersonation::new()),
        5 => Box::new(BracketFlooding::new()),
        6 => Box::new(PrematureFinal::new()),
        7 => Box::new(RangeReframe::new()),
        _ => Box::new(ProtocolMimicry::new()),
    }
}

fn transcript_path(provider_tag: &str, cell_name: &str, trial: u32) -> PathBuf {
    PathBuf::from(format!(
        "crates/cbcl-arena/transcripts/{}-yao-{}-{:03}.jsonl",
        provider_tag, cell_name, trial
    ))
}

/// Mixed-seat enum so the driver can drive a 2-seat slate of
/// `(GLM seat, Box<dyn MillionairePattern>)` or
/// `(GLM seat, CbclAgent<MillionaireCbclStrategy>)`.
enum YaoCellSeat {
    Free(GlmFreeChatYaoSeat),
    Disciplined(DisciplinedSeat<YaoDisciplinedAdapter>),
    Native(GlmCbclNativeYaoSeat),
    Attacker(Box<dyn MillionairePattern>),
    Cbcl(CbclAgent<MillionaireCbclStrategy>),
}

impl DrivenAgent for YaoCellSeat {
    type Setup = MillionaireSetup;
    type Guess = MillionaireGuess;

    fn ingest_setup(&mut self, setup: Self::Setup) {
        match self {
            YaoCellSeat::Free(s) => s.ingest_setup(setup),
            YaoCellSeat::Disciplined(s) => s.ingest_setup(setup),
            YaoCellSeat::Native(s) => s.ingest_setup(setup),
            YaoCellSeat::Attacker(a) => a.ingest_setup(setup),
            YaoCellSeat::Cbcl(a) => {
                cbcl_arena::agents::cbcl::ingest_setup(a, setup.wealth);
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
            YaoCellSeat::Free(s) => s.step(in_channel, out_channel, rng, send_index_seed),
            YaoCellSeat::Disciplined(s) => {
                s.step(in_channel, out_channel, rng, send_index_seed)
            }
            YaoCellSeat::Native(s) => s.step(in_channel, out_channel, rng, send_index_seed),
            YaoCellSeat::Attacker(a) => {
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
            YaoCellSeat::Cbcl(a) => <CbclAgent<MillionaireCbclStrategy> as DrivenAgent>::step(
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
            YaoCellSeat::Free(s) => s.final_guess(),
            YaoCellSeat::Disciplined(s) => s.final_guess(),
            YaoCellSeat::Native(s) => s.final_guess(),
            YaoCellSeat::Attacker(a) => a.final_guess(),
            YaoCellSeat::Cbcl(a) => match a.final_guess() {
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Richer => {
                    MillionaireGuess::Richer
                }
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Poorer => {
                    MillionaireGuess::Poorer
                }
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Equal => {
                    MillionaireGuess::Equal
                }
                cbcl_arena::agents::cbcl::millionaire::YaoVerdict::Unknown => {
                    MillionaireGuess::Unknown
                }
            },
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
    let path = transcript_path(backend_kind.provider_tag(), cell_name, trial);
    let dialect = load_dialect(YAO_DIALECT_SRC).expect("yao dialect");
    let (focal, peer) = match cell_name {
        "free" => (
            YaoCellSeat::Free(GlmFreeChatYaoSeat::new(
                backend,
                path.clone(),
                trial,
                max_turns,
                WEALTH_RANGE,
            )),
            YaoCellSeat::Attacker(pick_attacker(trial)),
        ),
        "disciplined" => (
            YaoCellSeat::Disciplined(DisciplinedSeat::new(
                backend,
                YaoDisciplinedAdapter::new(WEALTH_RANGE, "yao-game", "alice"),
                path.clone(),
                trial,
                max_turns,
            )),
            YaoCellSeat::Attacker(pick_attacker(trial)),
        ),
        "cooperative" => (
            YaoCellSeat::Disciplined(DisciplinedSeat::new(
                backend,
                YaoDisciplinedAdapter::new(WEALTH_RANGE, "yao-game", "alice"),
                path.clone(),
                trial,
                max_turns,
            )),
            YaoCellSeat::Cbcl(CbclAgent::new(
                dialect,
                MillionaireCbclStrategy::new(WEALTH_RANGE),
                "yao-game",
                "bob",
            )),
        ),
        "native-cooperative" => (
            YaoCellSeat::Native(GlmCbclNativeYaoSeat::new(
                backend,
                path.clone(),
                trial,
                max_turns,
                dialect.clone(),
                "yao-game",
                "alice",
                WEALTH_RANGE,
            )),
            YaoCellSeat::Cbcl(CbclAgent::new(
                dialect,
                MillionaireCbclStrategy::new(WEALTH_RANGE),
                "yao-game",
                "bob",
            )),
        ),
        "native-attacker" => (
            YaoCellSeat::Native(GlmCbclNativeYaoSeat::new(
                backend,
                path.clone(),
                trial,
                max_turns,
                dialect,
                "yao-game",
                "alice",
                WEALTH_RANGE,
            )),
            YaoCellSeat::Attacker(pick_attacker(trial)),
        ),
        other => panic!("unknown cell: {other}"),
    };
    let mut seats: Vec<YaoCellSeat> = vec![focal, peer];
    let op = yao_operator();
    let seed = derive_seed(cell_name, trial);
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
        .expect("focal score");
    eprintln!(
        "[glm_yao] {cell_name} trial {trial}: utility={} security={} (transcript={})",
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
        "[glm_yao] starting: n={} cell={} smoke={} max_turns={}",
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
            eprintln!("[glm_yao] cannot construct client: {e}");
            return ExitCode::from(2);
        }
    }

    let t0 = Instant::now();
    let mut free_stats: Option<CellStats> = None;
    let mut disc_stats: Option<CellStats> = None;
    let mut coop_stats: Option<CellStats> = None;
    let mut native_stats: Option<CellStats> = None;
    let mut native_atk_stats: Option<CellStats> = None;
    if matches!(args.cell, Cell::Free | Cell::Both) {
        free_stats = Some(run_cell("free", args.n, args.max_turns, args.backend));
    }
    if matches!(args.cell, Cell::Disciplined | Cell::Both) {
        disc_stats = Some(run_cell("disciplined", args.n, args.max_turns, args.backend));
    }
    if matches!(args.cell, Cell::Cooperative) {
        coop_stats = Some(run_cell("cooperative", args.n, args.max_turns, args.backend));
    }
    if matches!(args.cell, Cell::Native | Cell::Both) {
        native_stats = Some(run_cell("native-cooperative", args.n, args.max_turns, args.backend));
    }
    if matches!(args.cell, Cell::NativeAttacker) {
        native_atk_stats = Some(run_cell("native-attacker", args.n, args.max_turns, args.backend));
    }
    let elapsed = t0.elapsed();

    let model_label = match args.backend {
        BackendKind::Glm => "GLM-5.1",
        BackendKind::Codex => "GPT-5.5 (Codex)",
    };
    let tag = args.backend.provider_tag();
    println!("# {model_label} Yao Millionaire live-LLM probe (N={} per cell)\n", args.n);
    println!("| Cell | Leak rate | 95% CI | Utility (mean) | Security (mean) | Transcripts |");
    println!("|------|-----------|--------|----------------|------------------|-------------|");
    if let Some(s) = &free_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Free-chat   | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-yao-free-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &disc_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Disciplined | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-yao-disciplined-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &coop_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Cooperative | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-yao-cooperative-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &native_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Native (CBCL) | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-yao-native-cooperative-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    if let Some(s) = &native_atk_stats {
        let (lr, (lo, hi), u, sec) = s.summary();
        println!(
            "| Native × Attacker | {:.3} | ({:.3}, {:.3}) | {:.2} | {:.2} | crates/cbcl-arena/transcripts/{tag}-yao-native-attacker-*.jsonl |",
            lr, lo, hi, u, sec
        );
    }
    println!("\nWall-time: {:.1}s", elapsed.as_secs_f64());

    ExitCode::SUCCESS
}
