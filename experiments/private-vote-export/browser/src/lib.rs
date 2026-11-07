use anyhow::{anyhow, ensure, Result};
use common::jolt_device::{JoltDevice, MemoryConfig};
use jolt_crypto::{Bn254G1, Pedersen};
use jolt_dory::DoryScheme;
use jolt_field::Fr;
use jolt_program::execution::{
    build_jolt_program, ChunkedExecutionBackend, ExecutionBackend, TraceInputs,
};
use jolt_prover::{dory, JoltBackend, ProverConfig};
use jolt_transcript::{Keccak, ProverState, VerifierState};
use jolt_verifier::config::JoltProtocolConfig;
use jolt_witness::{JoltVmWitnessConfig, JoltVmWitnessInputs, TraceBackend};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::sync::Arc;
use tracer::execution_backend::TracerBackend;
use vote_common::Journal;
use wasm_bindgen::prelude::*;

pub const PIN: &str = "beebf45d829f5aecc5d330f78879cd914e47541e";
pub const MAX_TRACE: usize = 1 << 24;
pub type Proof = jolt_verifier::JoltProof<DoryScheme, Pedersen<Bn254G1>>;
pub type Setup = dory::DoryVerifierPreprocessing;
pub type ProverSetup = dory::DoryProverPreprocessing;
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Trust {
    pub jolt_commit: String,
    pub zk: bool,
    pub setup_sha256: [u8; 32],
    pub elf_sha256: [u8; 32],
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BrowserProfile {
    pub version: u32,
    pub kind: String,
    pub trust: Trust,
    pub prover_setup_sha256: [u8; 32],
}
pub fn hash(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}
pub fn encode<T: Serialize>(v: &T) -> Result<Vec<u8>> {
    Ok(bincode::serde::encode_to_vec(
        v,
        bincode::config::standard(),
    )?)
}
pub fn decode<T: serde::de::DeserializeOwned>(b: &[u8]) -> Result<T> {
    ensure!(b.len() <= 32 * 1024 * 1024, "encoded bound");
    let (v, n) =
        bincode::serde::decode_from_slice(b, bincode::config::standard().with_limit::<33554432>())?;
    ensure!(n == b.len(), "trailing bytes");
    Ok(v)
}
fn expected(b: &[u8]) -> Result<Journal> {
    ensure!(b.len() <= 8192, "expected bound");
    Ok(serde_json::from_slice(b)?)
}
fn trust(b: &[u8]) -> Result<Trust> {
    ensure!(b.len() <= 8192, "trust bound");
    let t: Trust = serde_json::from_slice(b)?;
    ensure!(t.jolt_commit == PIN && t.zk, "untrusted backend/mode");
    Ok(t)
}
fn check_output(io: &JoltDevice, expected: &Journal) -> Result<()> {
    ensure!(!io.panic && io.inputs.is_empty(), "invalid guest IO");
    let bytes: Vec<u8> = postcard::from_bytes(&io.outputs)?;
    let result: Result<Journal, String> = serde_json::from_slice(&bytes)?;
    ensure!(
        result.map_err(|e| anyhow!(e))? == *expected,
        "expected statement differs"
    );
    Ok(())
}
fn verify(setup: &Setup, proof: &Proof, io: &JoltDevice, journal: &Journal) -> Result<()> {
    ensure!(
        proof.protocol == JoltProtocolConfig::for_zk(true) && proof.claims.is_zk(),
        "ZK required"
    );
    check_output(io, journal)?;
    jolt_verifier::verify::<Fr, DoryScheme, Pedersen<Bn254G1>, VerifierState<'_, Keccak>>(
        setup, io, proof, None,
    )
    .map_err(|e| anyhow!("verification: {e:?}"))?;
    Ok(())
}
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace=performance,js_name=now)]
    fn now() -> f64;
    #[wasm_bindgen(js_namespace=globalThis,js_name=cbclPhase)]
    fn progress(phase: &str);
}
fn error(e: anyhow::Error) -> JsError {
    JsError::new(&e.to_string())
}
#[wasm_bindgen(start)]
pub fn init() {
    console_error_panic_hook::set_once();
}
#[wasm_bindgen]
pub fn verify_export(
    setup_bytes: &[u8],
    proof_bytes: &[u8],
    io_bytes: &[u8],
    expected_bytes: &[u8],
    trust_bytes: &[u8],
) -> Result<String, JsError> {
    (||->Result<String>{
        let start=now();let t=trust(trust_bytes)?;ensure!(hash(setup_bytes)==t.setup_sha256,"untrusted setup");
        let setup:Setup=decode(setup_bytes)?;let proof:Proof=decode(proof_bytes)?;let io:JoltDevice=decode(io_bytes)?;
        ensure!(io.untrusted_advice.is_empty() && io.trusted_advice.is_empty(),"advice leaked");
        let j=expected(expected_bytes)?;let loaded=now()-start;let before=now();verify(&setup,&proof,&io,&j)?;
        Ok(serde_json::json!({"verified":true,"zk":true,"history_files_read":0,"decode_ms":loaded,"verify_ms":now()-before,"total_ms":now()-start}).to_string())
    })().map_err(error)
}
#[wasm_bindgen]
pub struct BrowserExport {
    proof: Vec<u8>,
    io: Vec<u8>,
    metrics: String,
}
#[wasm_bindgen]
impl BrowserExport {
    pub fn proof_bytes(&self) -> Vec<u8> {
        self.proof.clone()
    }
    pub fn io_bytes(&self) -> Vec<u8> {
        self.io.clone()
    }
    pub fn metrics(&self) -> String {
        self.metrics.clone()
    }
}
fn profile(bytes: &[u8], prover_bytes: &[u8], elf: &[u8]) -> Result<BrowserProfile> {
    ensure!(bytes.len() <= 8192, "profile bound");
    let p: BrowserProfile = serde_json::from_slice(bytes)?;
    ensure!(
        p.version == 1
            && p.kind == "experimental-private-vote-v0"
            && p.trust.jolt_commit == PIN
            && p.trust.zk,
        "untrusted profile"
    );
    ensure!(
        elf.len() <= 2 * 1024 * 1024 && hash(elf) == p.trust.elf_sha256,
        "untrusted guest"
    );
    ensure!(
        prover_bytes.len() <= 32 * 1024 * 1024 && hash(prover_bytes) == p.prover_setup_sha256,
        "untrusted proving profile"
    );
    Ok(p)
}
fn memory(program_size: u64) -> MemoryConfig {
    MemoryConfig {
        heap_size: 16777216,
        stack_size: 1048576,
        max_input_size: 0,
        max_output_size: 8192,
        max_untrusted_advice_size: 131072,
        max_trusted_advice_size: 0,
        program_size: Some(program_size),
    }
}
#[wasm_bindgen]
pub fn prove_export(
    elf: &[u8],
    input: &[u8],
    expected_bytes: &[u8],
    prover_bytes: &[u8],
    profile_bytes: &[u8],
    count_only: bool,
) -> Result<BrowserExport, JsError> {
    (|| -> Result<BrowserExport> {
        let started = now();
        progress("recognize");
        let p = profile(profile_bytes, prover_bytes, elf)?;
        ensure!(input.len() <= vote_common::MAX_INPUT, "input bound");
        let j = expected(expected_bytes)?;
        let native_start = now();
        ensure!(
            vote_common::compute(input).map_err(|e| anyhow!(e))? == j,
            "native mismatch"
        );
        let mut metrics =
            serde_json::json!({"zk":true,"proof_generated":false,"native_ms":now()-native_start});
        progress("load-program");
        let program = Arc::new(build_jolt_program(elf).map_err(|e| anyhow!("program: {e:?}"))?);
        let program_size = program.program_end - common::constants::RAM_START_ADDRESS;
        let advice = postcard::to_stdvec(&input.to_vec())?;
        ensure!(advice.len() <= 131072, "advice bound");
        progress("execute-count");
        let before = now();
        let counted = TracerBackend::new()
            .execute(
                &program,
                TraceInputs::new(Vec::new(), advice.clone(), Vec::new(), memory(program_size)),
                1 << 28,
            )
            .map_err(|e| anyhow!("count: {e:?}"))?;
        check_output(&counted.device, &j)?;
        let rows = counted.trace_len;
        drop(counted);
        metrics["execute_ms"] = (now() - before).into();
        metrics["trace_rows"] = rows.into();
        let padded = (rows + 1).next_power_of_two();
        metrics["padded_trace_rows"] = padded.into();
        ensure!(padded <= MAX_TRACE, "trace bound");
        if count_only {
            metrics["total_ms"] = (now() - started).into();
            return Ok(BrowserExport {
                proof: Vec::new(),
                io: Vec::new(),
                metrics: metrics.to_string(),
            });
        }
        progress("load-proving-profile");
        let before = now();
        let setup: ProverSetup = decode(prover_bytes)?;
        ensure!(
            hash(&encode(&setup.verifier)?) == p.trust.setup_sha256,
            "prover/verifier pin mismatch"
        );
        let program_preprocessing = setup
            .program_arc()
            .ok_or_else(|| anyhow!("full profile required"))?;
        ensure!(
            program_preprocessing.max_padded_trace_length == MAX_TRACE,
            "profile bound mismatch"
        );
        metrics["profile_load_ms"] = (now() - before).into();
        progress("trace");
        let before = now();
        let trace = TracerBackend::new()
            .trace(
                &program,
                TraceInputs::new(Vec::new(), advice, Vec::new(), memory(program_size)),
            )
            .map_err(|e| anyhow!("trace: {e:?}"))?;
        ensure!(
            trace.dimensions.trace_length == rows,
            "trace/count mismatch"
        );
        check_output(&trace.device, &j)?;
        metrics["trace_ms"] = (now() - before).into();
        let config = ProverConfig::derive_from_dimensions::<Fr>(
            trace.dimensions,
            &program_preprocessing.memory_layout,
            program_preprocessing.ram.min_bytecode_address,
            program_preprocessing.ram.bytecode_words.len(),
            MAX_TRACE,
        )
        .map_err(|e| anyhow!("config: {e:?}"))?;
        let io = trace.device.clone();
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
        progress("prove");
        let before = now();
        let proof = dory::prove::<Fr, DoryScheme, Pedersen<Bn254G1>, ProverState<Keccak>>(
            JoltBackend::optimized().with_witness(&witness),
            &setup,
            &config,
            None,
            &io,
        )
        .map_err(|e| anyhow!("prove: {e:?}"))?;
        metrics["prove_ms"] = (now() - before).into();
        progress("verify");
        let before = now();
        verify(&setup.verifier, &proof, &io, &j)?;
        metrics["verify_ms"] = (now() - before).into();
        let proof = encode(&proof)?;
        let io = encode(&io)?;
        let exported: JoltDevice = decode(&io)?;
        ensure!(
            exported.untrusted_advice.is_empty() && exported.trusted_advice.is_empty(),
            "advice leaked"
        );
        metrics["proof_generated"] = true.into();
        metrics["proof_bytes"] = proof.len().into();
        metrics["io_bytes"] = io.len().into();
        metrics["total_ms"] = (now() - started).into();
        progress("done");
        Ok(BrowserExport {
            proof,
            io,
            metrics: metrics.to_string(),
        })
    })()
    .map_err(error)
}

/// Tests the pinned guest rejection path without the native consumer precheck.
#[wasm_bindgen]
pub fn check_guest_rejection(
    elf: &[u8],
    input: &[u8],
    prover_bytes: &[u8],
    profile_bytes: &[u8],
    reason: &str,
) -> Result<String, JsError> {
    (||->Result<String>{
        profile(profile_bytes,prover_bytes,elf)?;ensure!(input.len()<=vote_common::MAX_INPUT,"input bound");
        let program=build_jolt_program(elf).map_err(|e|anyhow!("program: {e:?}"))?;
        let advice=postcard::to_stdvec(&input.to_vec())?;ensure!(advice.len()<=131072,"advice bound");
        let start=now();let counted=TracerBackend::new().execute(&program,TraceInputs::new(Vec::new(),advice,Vec::new(),memory(program.program_end-common::constants::RAM_START_ADDRESS)),1<<28).map_err(|e|anyhow!("count: {e:?}"))?;
        ensure!(!counted.device.panic,"guest panicked instead of typed rejection");
        let bytes:Vec<u8>=postcard::from_bytes(&counted.device.outputs)?;let result:Result<Journal,String>=serde_json::from_slice(&bytes)?;
        let failure=result.err().ok_or_else(||anyhow!("invalid witness accepted"))?;ensure!(failure==reason,"wrong guest rejection: {failure}");
        Ok(serde_json::json!({"guest_rejected":true,"reason":failure,"host_native_precheck":false,"trace_rows":counted.trace_len,"execute_ms":now()-start}).to_string())
    })().map_err(error)
}
