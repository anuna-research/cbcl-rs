//! `cbcl checkpoint`: file and stdio shell over `cbcl-state-proof`
//! (SPEC-035 REQ-3510, CON-3505). Compiled only with the `state-proof` feature.
//!
//! Exit codes: 0 success, 1 rejection or verification failure, 2 usage error
//! (clap). No input panics; every rejection is an `Err(String)` printed as
//! `error: ...` on stderr.

use std::collections::BTreeSet;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use cbcl_state_proof::{Candidate, Chain, Checkpoint, Profile, Proof, Prover, Verifier};
use clap::{Args, Subcommand};
use serde::Deserialize;
use serde_json::Value;

/// Largest `profile.json` accepted (CON-3505).
const MAX_PROFILE_FILE: usize = 1 << 20;
/// Read caps for packages (CON-3502). The library recognisers apply their own
/// limits after the read; these only stop an oversize file being read at all.
const MAX_PROOF_FILE: usize = 100_000;
const MAX_CHAIN_FILE: usize = 1 << 20;
const WARNING: &str = "warning: candidates are unauthenticated; signer labels are host-asserted";

type Result<T> = std::result::Result<T, String>;

#[derive(Args)]
pub struct CheckpointArgs {
    #[command(subcommand)]
    op: Op,
}

#[derive(Subcommand)]
enum Op {
    /// Compile a profile and print its identity and candidate addresses
    Compile {
        /// Profile file: {"dialect", "thread", "candidates": [{"text", "label"}]}
        profile: PathBuf,
    },
    /// Prove the transition from --before to --after and write the proof package
    Prove {
        profile: PathBuf,
        /// Comma-separated wire addresses of the accepted set before; `-` for empty
        #[arg(long)]
        before: String,
        /// Comma-separated wire addresses of the accepted set after; `-` for empty
        #[arg(long)]
        after: String,
        /// Output file (stdout when absent)
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Verify a proof package against the receiver's --before/--after statement
    Verify {
        profile: PathBuf,
        proof: PathBuf,
        /// Comma-separated wire addresses of the accepted set before; `-` for empty
        #[arg(long)]
        before: String,
        /// Comma-separated wire addresses of the accepted set after; `-` for empty
        #[arg(long)]
        after: String,
    },
    /// Verify a chain package from genesis (or --start) and print the final checkpoint
    ChainVerify {
        profile: PathBuf,
        chain: PathBuf,
        /// Start set as comma-separated wire addresses; `-` for empty; genesis when absent
        #[arg(long)]
        start: Option<String>,
        /// Expected final set as comma-separated wire addresses; `-` for empty
        #[arg(long)]
        end: Option<String>,
    },
}

/// Recogniser for `profile.json` (CON-3505). Unknown and duplicate members
/// are rejected by serde.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProfileFile {
    dialect: String,
    thread: String,
    candidates: Vec<CandidateFile>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CandidateFile {
    text: String,
    label: String,
}

/// Runs one operation and maps its outcome to an exit code.
pub fn run(args: CheckpointArgs) -> i32 {
    eprintln!("{WARNING}");
    match execute(args.op) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("error: {e}");
            1
        }
    }
}

fn execute(op: Op) -> Result<()> {
    match op {
        Op::Compile { profile } => {
            let profile = compile(&profile)?;
            let addresses: Vec<&str> = profile.addresses().iter().map(String::as_str).collect();
            emit(&serde_json::json!({"profile": hex(&profile.id()), "addresses": addresses}))
        }
        Op::Prove {
            profile,
            before,
            after,
            out,
        } => {
            let profile = compile(&profile)?;
            let (before, after) = (mask(&profile, &before)?, mask(&profile, &after)?);
            let proof = Prover::new(profile)?.prove(before, after)?;
            let bytes = proof.to_json()?;
            match out {
                Some(path) => {
                    fs::write(&path, bytes).map_err(|e| format!("{}: {e}", path.display()))
                }
                None => write_stdout(&bytes),
            }
        }
        Op::Verify {
            profile,
            proof,
            before,
            after,
        } => {
            let profile = compile(&profile)?;
            let proof = Proof::from_json(&read_file(&proof, MAX_PROOF_FILE)?)?;
            // The expectation is the receiver's (REQ-3502 a); the package's
            // statement is only ever compared against it.
            let expected = profile.statement(mask(&profile, &before)?, mask(&profile, &after)?)?;
            Verifier::new(profile)?.verify(&proof, &expected)?;
            emit(&serde_json::json!({"verified": true, "after": checkpoint_json(&expected.after)}))
        }
        Op::ChainVerify {
            profile,
            chain,
            start,
            end,
        } => {
            let profile = compile(&profile)?;
            let chain = Chain::from_json(&read_file(&chain, MAX_CHAIN_FILE)?)?;
            let start = match start {
                Some(s) => profile.checkpoint(mask(&profile, &s)?)?,
                None => profile.genesis(),
            };
            let end: Option<Checkpoint> = match end {
                Some(e) => Some(profile.checkpoint(mask(&profile, &e)?)?),
                None => None,
            };
            let last = chain.verify(&Verifier::new(profile)?, start, end)?;
            emit(&checkpoint_json(&last))
        }
    }
}

/// Reads and recognises `profile.json`, then compiles it. Rejects a file over
/// 1 MiB, unknown or duplicate members, a positional array where the profile
/// or a candidate object is required, and anything `Profile::compile` rejects.
fn compile(path: &Path) -> Result<Profile> {
    let bytes = read_file(path, MAX_PROFILE_FILE)?;
    let value: Value = serde_json::from_slice(&bytes).map_err(|e| format!("profile: {e}"))?;
    let top = value.as_object().ok_or("profile: expected a JSON object")?;
    if let Some(Value::Array(candidates)) = top.get("candidates") {
        if !candidates.iter().all(Value::is_object) {
            return Err("profile: candidate must be a JSON object".into());
        }
    }
    let file: ProfileFile = serde_json::from_slice(&bytes).map_err(|e| format!("profile: {e}"))?;
    let candidates: Vec<Candidate> = file
        .candidates
        .into_iter()
        .map(|c| Candidate::unauthenticated(c.text, c.label))
        .collect();
    Profile::compile(&file.dialect, &file.thread, &candidates)
}

/// Reads at most `limit + 1` bytes through `Read::take`; a file with more
/// than `limit` bytes is rejected without being parsed (CON-3505).
fn read_file(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let file = fs::File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    if bytes.len() > limit {
        return Err(format!("{}: exceeds {limit} bytes", path.display()));
    }
    Ok(bytes)
}

/// Parses a CON-3505 address list: `-` is the empty set; otherwise every
/// comma-separated item must be a `sha256-<hex64>` address in the profile,
/// and no address may repeat.
fn mask(profile: &Profile, list: &str) -> Result<u16> {
    if list == "-" {
        return profile.mask(&[]);
    }
    let addresses: Vec<&str> = list.split(',').collect();
    let mut seen = BTreeSet::new();
    for a in &addresses {
        if !seen.insert(*a) {
            return Err(format!("repeated address {a:?}"));
        }
        let hex = a
            .strip_prefix("sha256-")
            .ok_or_else(|| format!("malformed address {a:?}"))?;
        if hex.len() != 64 || !hex.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err(format!("malformed address {a:?}"));
        }
    }
    profile.mask(&addresses)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// CON-3505: checkpoints print as `{"accepted": hex64, "state": hex64}`.
fn checkpoint_json(cp: &Checkpoint) -> Value {
    serde_json::json!({"accepted": hex(&cp.accepted), "state": hex(&cp.state)})
}

/// One line of compact JSON on stdout.
fn emit<T: serde::Serialize>(value: &T) -> Result<()> {
    let mut bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    write_stdout(&bytes)
}

fn write_stdout(bytes: &[u8]) -> Result<()> {
    let mut out = std::io::stdout().lock();
    out.write_all(bytes)
        .and_then(|()| out.flush())
        .map_err(|e| format!("stdout: {e}"))
}
