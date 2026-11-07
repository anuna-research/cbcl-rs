use anyhow::{anyhow, ensure, Result};
use cbcl_vote_browser::{encode, hash, BrowserProfile, Trust, MAX_TRACE, PIN};
use common::jolt_device::{MemoryConfig, MemoryLayout};
use jolt_program::{execution::build_jolt_program, preprocess::JoltProgramPreprocessing};
use jolt_prover::{dory, JoltSharedPreprocessing};
use std::{fs, path::PathBuf};
fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().collect();
    ensure!(args.len() == 4, "browser-profile elf existing-trust output");
    let elf = fs::read(&args[1])?;
    let trust: Trust = serde_json::from_slice(&fs::read(&args[2])?)?;
    ensure!(
        trust.jolt_commit == PIN && trust.zk && hash(&elf) == trust.elf_sha256,
        "untrusted guest"
    );
    let program = build_jolt_program(&elf).map_err(|e| anyhow!("program: {e:?}"))?;
    let memory = MemoryConfig {
        heap_size: 16777216,
        stack_size: 1048576,
        max_input_size: 0,
        max_output_size: 8192,
        max_untrusted_advice_size: 131072,
        max_trusted_advice_size: 0,
        program_size: Some(program.program_end - common::constants::RAM_START_ADDRESS),
    };
    let full = JoltProgramPreprocessing::new(
        program.expanded_bytecode,
        program.memory_init,
        MemoryLayout::try_new(&memory)?,
        program.entry_address,
        MAX_TRACE,
        program.profile,
    )
    .map_err(|e| anyhow!("preprocessing: {e:?}"))?;
    let setup = dory::from_shared(
        JoltSharedPreprocessing::new(full).map_err(|e| anyhow!("shared: {e:?}"))?,
    )
    .map_err(|e| anyhow!("Dory: {e:?}"))?;
    let verifier = encode(&setup.verifier)?;
    ensure!(
        hash(&verifier) == trust.setup_sha256,
        "existing verifier pin differs"
    );
    let bytes = encode(&setup)?;
    let profile = BrowserProfile {
        version: 1,
        kind: "experimental-private-vote-v0".into(),
        trust,
        prover_setup_sha256: hash(&bytes),
    };
    let out = PathBuf::from(&args[3]);
    fs::create_dir_all(&out)?;
    fs::write(out.join("prover-setup.bin"), &bytes)?;
    fs::write(out.join("setup.bin"), verifier)?;
    fs::write(
        out.join("profile.json"),
        serde_json::to_vec_pretty(&profile)?,
    )?;
    println!(
        "{}",
        serde_json::json!({"prover_setup_bytes":bytes.len(),"verifier_pin_matches":true})
    );
    Ok(())
}
