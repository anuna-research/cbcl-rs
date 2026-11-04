// SPDX-License-Identifier: Apache-2.0
// Uses the public upstream Akita flow demonstrated in Jolt's e2e_matrix.rs.
use anyhow::{anyhow, ensure, Result};
use checkpoint_common::{compute, state_hash, Journal};
use common::jolt_device::{JoltDevice, MemoryConfig, MemoryLayout};
use jolt_akita::{AkitaChunkProfile, AkitaField, AkitaScheduleArtifacts, AkitaScheme};
use jolt_host::{JoltProgramSource, Program};
use jolt_program::{
    execution::{ExecutionBackend, TraceInputs},
    preprocess::JoltProgramPreprocessing,
};
use jolt_prover::{
    akita::{
        self,
        preprocessing::{self, AkitaVc},
    },
    JoltBackend, ProverConfig,
};
use jolt_transcript::{Keccak, ProverState, VerifierState};
use jolt_witness::{JoltVmWitnessConfig, JoltVmWitnessInputs, TraceBackend};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fs,
    path::{Path, PathBuf},
    sync::Arc,
    time::Instant,
};
use tracer::execution_backend::TracerBackend;

type Proof = jolt_verifier::JoltProof<AkitaScheme, AkitaVc>;
type Setup = jolt_verifier::JoltVerifierPreprocessing<AkitaScheme, AkitaVc>;
const PIN: &str = "beebf45d829f5aecc5d330f78879cd914e47541e";
const MAX_TRACE: usize = 1 << 22;
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Trust {
    jolt_commit: String,
    setup_sha256: [u8; 32],
    elf_sha256: [u8; 32],
}
fn hash(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
fn read(path: impl AsRef<Path>, limit: u64) -> Result<Vec<u8>> {
    let p = path.as_ref();
    ensure!(fs::metadata(p)?.len() <= limit, "file bound");
    Ok(fs::read(p)?)
}
fn encode<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    Ok(bincode::serde::encode_to_vec(
        value,
        bincode::config::standard(),
    )?)
}
fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T> {
    let (value, used) = bincode::serde::decode_from_slice(
        bytes,
        bincode::config::standard().with_limit::<536870912>(),
    )?;
    ensure!(used == bytes.len(), "trailing encoded data");
    Ok(value)
}
fn check_output(io: &JoltDevice, expected: &Journal, state: &str) -> Result<()> {
    ensure!(!io.panic, "guest panic cannot certify a checkpoint");
    ensure!(io.inputs.is_empty(), "history must not be public input");
    let json: Vec<u8> = postcard::from_bytes(&io.outputs)?;
    let journal: Journal = serde_json::from_slice(&json)?;
    ensure!(&journal == expected, "expected checkpoint differs");
    ensure!(journal.state_hash == state_hash(state), "snapshot differs");
    Ok(())
}
fn verify(
    setup: &Setup,
    io: &JoltDevice,
    proof: &Proof,
    expected: &Journal,
    state: &str,
) -> Result<()> {
    check_output(io, expected, state)?;
    jolt_verifier::verify::<AkitaField, AkitaScheme, AkitaVc, VerifierState<'_, Keccak>>(
        setup, io, proof, None,
    )
    .map_err(|e| anyhow!("verification: {e:?}"))?;
    Ok(())
}
fn phase(out: &Path, name: &str) -> Result<()> {
    fs::write(
        out.join("phase.json"),
        serde_json::to_vec(&serde_json::json!({"phase":name}))?,
    )?;
    println!("phase={name}");
    Ok(())
}
fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("verify") => {
            ensure!(
                args.len() == 9,
                "verify setup proof io expected state trusted-pin marker"
            );
            ensure!(args[8] == "no-history", "explicit receiver mode required");
            let trust: Trust = serde_json::from_slice(&read(&args[7], 65536)?)?;
            ensure!(trust.jolt_commit == PIN, "backend version differs");
            let setup_bytes = read(&args[2], 536870912)?;
            ensure!(
                hash(&setup_bytes) == trust.setup_sha256,
                "untrusted program/setup"
            );
            let setup: Setup = decode(&setup_bytes)?;
            let proof: Proof = decode(&read(&args[3], 67108864)?)?;
            let io: JoltDevice = decode(&read(&args[4], 65536)?)?;
            ensure!(
                io.untrusted_advice.is_empty() && io.trusted_advice.is_empty(),
                "receiver must not receive history advice"
            );
            let expected: Journal = serde_json::from_slice(&read(&args[5], 65536)?)?;
            let state = String::from_utf8(read(&args[6], 8388608)?)?;
            let t = Instant::now();
            verify(&setup, &io, &proof, &expected, &state)?;
            println!(
                "{}",
                serde_json::json!({"verified":true,"verify_us":t.elapsed().as_micros(),"count":expected.count,"history_files_read":0})
            );
        }
        Some("run") => {
            ensure!(
                args.len() == 6,
                "run input expected output-directory trusted-pin-directory"
            );
            let input = read(&args[2], checkpoint_common::MAX_INPUT as u64)?;
            let expected: Journal = serde_json::from_slice(&read(&args[3], 65536)?)?;
            let native = compute(&input).map_err(|e| anyhow!(e))?;
            ensure!(native.journal == expected, "native statement changed");
            let out = PathBuf::from(&args[4]);
            let pins = PathBuf::from(&args[5]);
            fs::create_dir_all(&out)?;
            fs::create_dir_all(&pins)?;
            for file in ["proof.bin", "metrics.json"] {
                match fs::remove_file(out.join(file)) {
                    Ok(()) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                    Err(e) => return Err(e.into()),
                }
            }
            fs::write(
                pins.join("expected.json"),
                serde_json::to_vec_pretty(&expected)?,
            )?;
            fs::write(pins.join("state.json"), &native.state)?;
            let mut metrics = serde_json::json!({"jolt_commit":PIN,"backend":"Akita optimized CPU","count":expected.count,"proof_generated":false});
            phase(&out, "guest-build")?;
            let mut source = Program::new("cbcl-akita-guest");
            source.set_func("checkpoint");
            source.set_heap_size(8388608);
            source.set_stack_size(1048576);
            source.set_max_input_size(0);
            source.set_max_output_size(8192);
            source.set_max_untrusted_advice_size(2097152);
            source.set_max_trusted_advice_size(0);
            let t = Instant::now();
            source.build_with_features(&std::env::var("CBCL_GUEST_TARGET")?, &[]);
            metrics["guest_build_ms"] = (t.elapsed().as_millis() as u64).into();
            fs::write(
                out.join("progress.json"),
                serde_json::to_vec_pretty(&metrics)?,
            )?;
            let elf = source
                .get_elf_contents()
                .ok_or_else(|| anyhow!("missing guest ELF"))?;
            phase(&out, "trace")?;
            let t = Instant::now();
            let program = Arc::new(
                source
                    .build_jolt_program()
                    .map_err(|e| anyhow!("program: {e:?}"))?,
            );
            let memory = MemoryConfig {
                heap_size: 8388608,
                stack_size: 1048576,
                max_input_size: 0,
                max_output_size: 8192,
                max_untrusted_advice_size: 2097152,
                max_trusted_advice_size: 0,
                program_size: Some(program.program_end - common::constants::RAM_START_ADDRESS),
            };
            let layout = MemoryLayout::try_new(&memory)?;
            let advice = postcard::to_stdvec(&input)?;
            let trace = TracerBackend::new()
                .trace(
                    &program,
                    TraceInputs::new(Vec::new(), advice, Vec::new(), memory),
                )
                .map_err(|e| anyhow!("trace: {e:?}"))?;
            check_output(&trace.device, &expected, &native.state)?;
            ensure!(
                (trace.dimensions.trace_length + 1).next_power_of_two() <= MAX_TRACE,
                "trace bound"
            );
            metrics["trace_ms"] = (t.elapsed().as_millis() as u64).into();
            metrics["trace_rows"] = trace.dimensions.trace_length.into();
            fs::write(
                out.join("progress.json"),
                serde_json::to_vec_pretty(&metrics)?,
            )?;
            phase(&out, "preprocess")?;
            let t = Instant::now();
            let program_setup = JoltProgramPreprocessing::new(
                program.expanded_bytecode.clone(),
                program.memory_init.clone(),
                layout,
                program.entry_address,
                MAX_TRACE,
                source.instruction_profile(),
            )
            .map_err(|e| anyhow!("preprocessing: {e:?}"))?;
            let mut config = ProverConfig::derive_from_dimensions::<AkitaField>(
                trace.dimensions,
                &program_setup.memory_layout,
                program_setup.ram.min_bytecode_address,
                program_setup.ram.bytecode_words.len(),
                MAX_TRACE,
            )
            .map_err(|e| anyhow!("config: {e:?}"))?;
            config.rw_config.ram_rw_phase1_num_rounds = 0;
            config.rw_config.registers_rw_phase1_num_rounds = 0;
            let schedules =
                AkitaScheduleArtifacts::shared_from_default_directory(AkitaChunkProfile::new(8, 2));
            let setup = preprocessing::preprocess_full_with_advice(
                &schedules,
                program_setup,
                &config,
                true,
                false,
            )
            .map_err(|e| anyhow!("Akita setup: {e:?}"))?;
            let setup_bytes = encode(&setup.verifier)?;
            let trust = Trust {
                jolt_commit: PIN.into(),
                setup_sha256: hash(&setup_bytes),
                elf_sha256: hash(&elf),
            };
            fs::write(
                pins.join("trusted.json"),
                serde_json::to_vec_pretty(&trust)?,
            )?;
            fs::write(out.join("verifier-setup.bin"), &setup_bytes)?;
            metrics["preprocess_ms"] = (t.elapsed().as_millis() as u64).into();
            metrics["verifier_setup_bytes"] = setup_bytes.len().into();
            fs::write(
                out.join("progress.json"),
                serde_json::to_vec_pretty(&metrics)?,
            )?;
            let program_preprocessing = setup
                .program_arc()
                .ok_or_else(|| anyhow!("missing full program"))?;
            let public_io = trace.device.clone();
            let witness = TraceBackend::new(
                JoltVmWitnessConfig::new(
                    config.trace_length.ilog2() as usize,
                    config.ram_K,
                    config.one_hot_config,
                )
                .include_untrusted_advice(true)
                .include_trusted_advice(false),
                JoltVmWitnessInputs::new(&program, &program_preprocessing, trace),
            );
            phase(&out, "prove")?;
            let t = Instant::now();
            let proof = akita::prove::<AkitaField, AkitaScheme, AkitaVc, ProverState<Keccak>>(
                JoltBackend::optimized().with_witness(&witness),
                &setup,
                &config,
                None,
                &public_io,
            )
            .map_err(|e| anyhow!("prove: {e:?}"))?;
            metrics["prove_ms"] = (t.elapsed().as_millis() as u64).into();
            phase(&out, "verify")?;
            let t = Instant::now();
            verify(
                &setup.verifier,
                &public_io,
                &proof,
                &expected,
                &native.state,
            )?;
            metrics["verify_ms"] = (t.elapsed().as_millis() as u64).into();
            let proof_bytes = encode(&proof)?;
            let public_bytes = encode(&public_io)?;
            let public_decoded: JoltDevice = decode(&public_bytes)?;
            ensure!(
                public_decoded.untrusted_advice.is_empty()
                    && public_decoded.trusted_advice.is_empty(),
                "advice serialization leaked"
            );
            fs::write(out.join("proof.bin"), &proof_bytes)?;
            fs::write(out.join("io.bin"), &public_bytes)?;
            metrics["proof_bytes"] = proof_bytes.len().into();
            metrics["public_io_bytes"] = public_bytes.len().into();
            metrics["proof_generated"] = true.into();
            fs::write(
                out.join("metrics.json"),
                serde_json::to_vec_pretty(&metrics)?,
            )?;
            println!("{metrics}");
        }
        _ => return Err(anyhow!("run or verify command required")),
    }
    Ok(())
}
