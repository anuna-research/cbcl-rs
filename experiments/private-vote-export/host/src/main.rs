use anyhow::{anyhow, ensure, Result};
use common::jolt_device::{JoltDevice, MemoryConfig, MemoryLayout};
use jolt_crypto::{Bn254G1, Pedersen};
use jolt_dory::DoryScheme;
use jolt_field::Fr;
use jolt_host::{JoltProgramSource, Program};
use jolt_program::{
    execution::{ChunkedExecutionBackend, ExecutionBackend, TraceInputs},
    preprocess::JoltProgramPreprocessing,
};
use jolt_prover::{dory, JoltBackend, JoltSharedPreprocessing, ProverConfig};
use jolt_transcript::{Keccak, ProverState, VerifierState};
use jolt_verifier::config::JoltProtocolConfig;
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
use vote_common::{compute, Journal};

type Proof = jolt_verifier::JoltProof<DoryScheme, Pedersen<Bn254G1>>;
type Setup = dory::DoryVerifierPreprocessing;
const PIN: &str = "beebf45d829f5aecc5d330f78879cd914e47541e";
const MAX_TRACE: usize = 1 << 24;
const ZK: bool = cfg!(feature = "zk");
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Trust {
    jolt_commit: String,
    zk: bool,
    setup_sha256: [u8; 32],
    elf_sha256: [u8; 32],
}
fn hash(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
fn read(p: impl AsRef<Path>, limit: u64) -> Result<Vec<u8>> {
    ensure!(fs::metadata(p.as_ref())?.len() <= limit, "file bound");
    Ok(fs::read(p)?)
}
fn encode<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    Ok(bincode::serde::encode_to_vec(
        value,
        bincode::config::standard(),
    )?)
}
fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T> {
    let (v, n) = bincode::serde::decode_from_slice(
        bytes,
        bincode::config::standard().with_limit::<536870912>(),
    )?;
    ensure!(n == bytes.len(), "trailing bytes");
    Ok(v)
}
fn output(io: &JoltDevice) -> Result<Result<Journal, String>> {
    ensure!(!io.panic, "guest panic");
    ensure!(io.inputs.is_empty(), "unexpected public input");
    let bytes: Vec<u8> = postcard::from_bytes(&io.outputs)?;
    Ok(serde_json::from_slice(&bytes)?)
}
fn verify(setup: &Setup, io: &JoltDevice, proof: &Proof, expected: &Journal) -> Result<()> {
    ensure!(
        proof.protocol == JoltProtocolConfig::for_zk(ZK),
        "wrong proof protocol"
    );
    ensure!(proof.claims.is_zk() == ZK, "wrong proof claims mode");
    ensure!(
        output(io)?.map_err(|e| anyhow!(e))? == *expected,
        "expected statement differs"
    );
    jolt_verifier::verify::<Fr, DoryScheme, Pedersen<Bn254G1>, VerifierState<'_, Keccak>>(
        setup, io, proof, None,
    )
    .map_err(|e| anyhow!("verification: {e:?}"))?;
    Ok(())
}
fn write_json(p: impl AsRef<Path>, v: &impl Serialize) -> Result<()> {
    fs::write(p, serde_json::to_vec_pretty(v)?)?;
    Ok(())
}
fn phase(out: &Path, name: &str) -> Result<()> {
    write_json(out.join("phase.json"), &serde_json::json!({"phase":name}))?;
    println!("phase={name}");
    Ok(())
}
fn main() -> Result<()> {
    std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024)
        .spawn(run)?
        .join()
        .map_err(|_| anyhow!("host thread panic"))?
}
fn run() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let command = args
        .get(1)
        .map(String::as_str)
        .ok_or_else(|| anyhow!("command required"))?;
    if command == "verify" {
        ensure!(
            args.len() == 8 && args[7] == "no-history",
            "verify setup proof io expected trusted-pin no-history"
        );
        let start = Instant::now();
        let trust: Trust = serde_json::from_slice(&read(&args[6], 65536)?)?;
        ensure!(
            trust.jolt_commit == PIN && trust.zk == ZK,
            "wrong backend/mode pin"
        );
        let setup_bytes = read(&args[2], 536870912)?;
        ensure!(hash(&setup_bytes) == trust.setup_sha256, "untrusted setup");
        let setup: Setup = decode(&setup_bytes)?;
        let proof: Proof = decode(&read(&args[3], 67108864)?)?;
        let io: JoltDevice = decode(&read(&args[4], 65536)?)?;
        ensure!(
            io.untrusted_advice.is_empty() && io.trusted_advice.is_empty(),
            "advice leaked"
        );
        let expected: Journal = serde_json::from_slice(&read(&args[5], 65536)?)?;
        let loaded_us = start.elapsed().as_micros();
        let verify_start = Instant::now();
        verify(&setup, &io, &proof, &expected)?;
        println!(
            "{}",
            serde_json::json!({"verified":true,"zk":ZK,"history_files_read":0,"load_decode_us":loaded_us,"verify_us":verify_start.elapsed().as_micros(),"receiver_total_us":start.elapsed().as_micros()})
        );
        return Ok(());
    }
    if command == "tamper-advice" {
        ensure!(args.len() == 4, "tamper-advice io output");
        let io: JoltDevice = decode(&read(&args[2], 65536)?)?;
        // Typed wire fixture bypasses JoltDevice's intentional advice-stripping serializer.
        let bytes = encode(&(
            io.inputs,
            io.trusted_advice,
            vec![1u8],
            io.outputs,
            io.panic,
            io.memory_layout,
        ))?;
        let check: JoltDevice = decode(&bytes)?;
        ensure!(
            !check.untrusted_advice.is_empty(),
            "forged advice fixture empty"
        );
        fs::write(&args[3], bytes)?;
        return Ok(());
    }
    if command == "tamper-io" {
        ensure!(args.len() == 5, "tamper-io io expected output");
        let mut io: JoltDevice = decode(&read(&args[2], 65536)?)?;
        let expected: Journal = serde_json::from_slice(&read(&args[3], 65536)?)?;
        let changed: Result<Journal, String> = Ok(expected);
        io.outputs = postcard::to_stdvec(&serde_json::to_vec(&changed)?)?;
        fs::write(&args[4], encode(&io)?)?;
        return Ok(());
    }
    ensure!(
        matches!(command, "count" | "run" | "guest-check"),
        "unknown command"
    );
    ensure!(
        args.len() == 5,
        "count/run input expected out; guest-check input error-substring out"
    );
    let input = read(&args[2], vote_common::MAX_INPUT as u64)?;
    let expected: Option<Journal> = if command == "guest-check" {
        None
    } else {
        Some(serde_json::from_slice(&read(&args[3], 65536)?)?)
    };
    let out = PathBuf::from(&args[4]);
    fs::create_dir_all(&out)?;
    ensure!(
        !out.join("metrics.json").exists() && !out.join("proof.bin").exists(),
        "fresh output directory required"
    );
    let mut metrics = serde_json::json!({"backend":"Jolt Dory CPU","jolt_commit":PIN,"zk":ZK,"proof_generated":false,"max_trace":MAX_TRACE});
    if let Some(expected) = &expected {
        let t = Instant::now();
        ensure!(
            compute(&input).map_err(|e| anyhow!(e))? == *expected,
            "native mismatch"
        );
        metrics["native_us"] = (t.elapsed().as_micros() as u64).into();
    }
    phase(&out, "guest-build")?;
    let mut source = Program::new("cbcl-vote-guest");
    source.set_func("export_vote");
    source.set_heap_size(16777216);
    source.set_stack_size(1048576);
    source.set_max_input_size(0);
    source.set_max_output_size(8192);
    source.set_max_untrusted_advice_size(131072);
    source.set_max_trusted_advice_size(0);
    let t = Instant::now();
    source.build_with_features(&std::env::var("CBCL_GUEST_TARGET")?, &[]);
    metrics["guest_build_ms"] = (t.elapsed().as_millis() as u64).into();
    let elf = source
        .get_elf_contents()
        .ok_or_else(|| anyhow!("missing ELF"))?;
    metrics["guest_elf_sha256"] = serde_json::json!(hash(&elf));
    let program = Arc::new(
        source
            .build_jolt_program()
            .map_err(|e| anyhow!("program: {e:?}"))?,
    );
    let memory = MemoryConfig {
        heap_size: 16777216,
        stack_size: 1048576,
        max_input_size: 0,
        max_output_size: 8192,
        max_untrusted_advice_size: 131072,
        max_trusted_advice_size: 0,
        program_size: Some(program.program_end - common::constants::RAM_START_ADDRESS),
    };
    let layout = MemoryLayout::try_new(&memory)?;
    let advice = postcard::to_stdvec(&input)?;
    ensure!(advice.len() <= 131072, "encoded advice bound");
    // Count first without retaining the complete trace; refuse oversized work before tracing.
    phase(&out, "count")?;
    let t = Instant::now();
    let counted = TracerBackend::new()
        .execute(
            &program,
            TraceInputs::new(Vec::new(), advice.clone(), Vec::new(), memory),
            1 << 28,
        )
        .map_err(|e| anyhow!("execution: {e:?}"))?;
    metrics["execute_ms"] = (t.elapsed().as_millis() as u64).into();
    metrics["trace_rows"] = counted.trace_len.into();
    let padded = (counted.trace_len + 1).next_power_of_two();
    metrics["padded_trace_rows"] = padded.into();
    metrics["within_trace_bound"] = (padded <= MAX_TRACE).into();
    let counted_rows = counted.trace_len;
    let result = output(&counted.device)?;
    drop(counted);
    if let Some(expected) = &expected {
        ensure!(
            result.map_err(|e| anyhow!(e))? == *expected,
            "guest output mismatch"
        );
    } else {
        let error = result.expect_err("negative guest unexpectedly accepted");
        ensure!(error.contains(&args[3]), "wrong rejection: {error}");
        metrics["guest_rejected"] = true.into();
        metrics["reason"] = error.into();
    }
    write_json(out.join("execution.json"), &metrics)?;
    if command != "run" {
        println!("{metrics}");
        return Ok(());
    }
    ensure!(padded <= MAX_TRACE, "trace bound");
    // A recorded count also establishes an explicit practical trace envelope for this input.
    phase(&out, "trace")?;
    let t = Instant::now();
    let trace = TracerBackend::new()
        .trace(
            &program,
            TraceInputs::new(
                Vec::new(),
                advice,
                Vec::new(),
                MemoryConfig {
                    heap_size: 16777216,
                    stack_size: 1048576,
                    max_input_size: 0,
                    max_output_size: 8192,
                    max_untrusted_advice_size: 131072,
                    max_trusted_advice_size: 0,
                    program_size: Some(program.program_end - common::constants::RAM_START_ADDRESS),
                },
            ),
        )
        .map_err(|e| anyhow!("trace: {e:?}"))?;
    ensure!(
        trace.dimensions.trace_length == counted_rows,
        "trace/count disagreement"
    );
    metrics["trace_ms"] = (t.elapsed().as_millis() as u64).into();
    phase(&out, "preprocess")?;
    let t = Instant::now();
    let full = JoltProgramPreprocessing::new(
        program.expanded_bytecode.clone(),
        program.memory_init.clone(),
        layout,
        program.entry_address,
        MAX_TRACE,
        source.instruction_profile(),
    )
    .map_err(|e| anyhow!("preprocess: {e:?}"))?;
    let config = ProverConfig::derive_from_dimensions::<Fr>(
        trace.dimensions,
        &full.memory_layout,
        full.ram.min_bytecode_address,
        full.ram.bytecode_words.len(),
        MAX_TRACE,
    )
    .map_err(|e| anyhow!("config: {e:?}"))?;
    let setup = dory::from_shared(
        JoltSharedPreprocessing::new(full).map_err(|e| anyhow!("shared: {e:?}"))?,
    )
    .map_err(|e| anyhow!("Dory: {e:?}"))?;
    let setup_bytes = encode(&setup.verifier)?;
    write_json(
        out.join("trusted.json"),
        &Trust {
            jolt_commit: PIN.into(),
            zk: ZK,
            setup_sha256: hash(&setup_bytes),
            elf_sha256: hash(&elf),
        },
    )?;
    fs::write(out.join("setup.bin"), &setup_bytes)?;
    metrics["preprocess_ms"] = (t.elapsed().as_millis() as u64).into();
    metrics["setup_bytes"] = setup_bytes.len().into();
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
    write_json(out.join("progress.json"), &metrics)?;
    let t = Instant::now();
    let proof = dory::prove::<Fr, DoryScheme, Pedersen<Bn254G1>, ProverState<Keccak>>(
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
        expected.as_ref().unwrap(),
    )?;
    metrics["verify_us"] = (t.elapsed().as_micros() as u64).into();
    let t = Instant::now();
    let proof_bytes = encode(&proof)?;
    let io_bytes = encode(&public_io)?;
    let clean: JoltDevice = decode(&io_bytes)?;
    ensure!(
        clean.untrusted_advice.is_empty() && clean.trusted_advice.is_empty(),
        "advice serialization leaked"
    );
    fs::write(out.join("proof.bin"), &proof_bytes)?;
    fs::write(out.join("io.bin"), &io_bytes)?;
    metrics["serialize_ms"] = (t.elapsed().as_millis() as u64).into();
    metrics["proof_bytes"] = proof_bytes.len().into();
    metrics["io_bytes"] = io_bytes.len().into();
    metrics["proof_generated"] = true.into();
    write_json(out.join("metrics.json"), &metrics)?;
    println!("{metrics}");
    Ok(())
}
