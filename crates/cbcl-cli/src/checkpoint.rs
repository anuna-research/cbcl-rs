//! `cbcl checkpoint`: file and stdio shell over `cbcl-state-proof`
//! (SPEC-035 REQ-3510, CON-3505). Compiled only with the `state-proof` feature.
//!
//! Exit codes: 0 success, 1 rejection or verification failure, 2 usage error
//! (clap). No input panics; every rejection is an `Err(String)` printed as
//! `error: ...` on stderr.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use cbcl_state_proof::{Candidate, Chain, Checkpoint, Profile, Proof, Prover, Verifier};
use clap::{Args, Subcommand};
use serde::Deserialize;

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
            emit(&serde_json::json!({"verified": true, "after": expected.after}))
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
            emit(&last)
        }
    }
}

/// Reads and recognises `profile.json`, then compiles it. Rejects a file over
/// 1 MiB, unknown or duplicate members, and anything `Profile::compile` rejects.
fn compile(path: &Path) -> Result<Profile> {
    let bytes = read_file(path, MAX_PROFILE_FILE)?;
    let file: ProfileFile = serde_json::from_slice(&bytes).map_err(|e| format!("profile: {e}"))?;
    let candidates: Vec<Candidate> = file
        .candidates
        .into_iter()
        .map(|c| Candidate::unauthenticated(c.text, c.label))
        .collect();
    Profile::compile(&file.dialect, &file.thread, &candidates)
}

/// Reads at most `limit` bytes; a longer file is rejected without being parsed.
fn read_file(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let len = fs::metadata(path)
        .map_err(|e| format!("{}: {e}", path.display()))?
        .len();
    if len > limit as u64 {
        return Err(format!("{}: exceeds {limit} bytes", path.display()));
    }
    fs::read(path).map_err(|e| format!("{}: {e}", path.display()))
}

/// Parses a CON-3505 address list: `-` is the empty set; otherwise every
/// comma-separated item must be a `sha256-<hex64>` address in the profile.
fn mask(profile: &Profile, list: &str) -> Result<u16> {
    if list == "-" {
        return profile.mask(&[]);
    }
    let addresses: Vec<&str> = list.split(',').collect();
    for a in &addresses {
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
