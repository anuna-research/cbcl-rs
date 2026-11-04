use bincode::Options;
use checkpoint_common::{compute, state_hash, Journal, MAX_INPUT};
use checkpoint_methods::{CHECKPOINT_GUEST_ELF, CHECKPOINT_GUEST_ID};
use risc0_zkvm::{
    default_executor, default_prover, ExecutorEnv, InnerReceipt, ProverOpts, Receipt,
};
use std::{env, fs, path::Path, time::Instant};
fn segment_po2() -> u32 {
    let value = std::env::var("CBCL_SEGMENT_PO2")
        .map(|x| x.parse::<u32>().expect("segment exponent"))
        .unwrap_or(18);
    assert!(
        (16..=20).contains(&value),
        "segment exponent must be 16..20"
    );
    value
}
fn bounded(path: &str, limit: u64) -> Vec<u8> {
    assert!(fs::metadata(path).unwrap().len() <= limit, "file too large");
    fs::read(path).unwrap()
}
fn verify(receipt: &Receipt, expected: &Journal, state: &str) {
    assert!(
        !matches!(receipt.inner, InnerReceipt::Fake(_)),
        "fake receipt forbidden"
    );
    receipt.verify(CHECKPOINT_GUEST_ID).unwrap();
    let actual: Journal = receipt.journal.decode().unwrap();
    assert_eq!(&actual, expected, "expected checkpoint differs");
    assert_eq!(actual.state_hash, state_hash(state), "snapshot differs");
}
fn main() {
    assert_ne!(
        env::var("RISC0_DEV_MODE").as_deref(),
        Ok("1"),
        "mock mode forbidden"
    );
    let args: Vec<_> = env::args().collect();
    match args.get(1).map(String::as_str) {
  Some("compress")=>{
   assert_eq!(args.len(),4,"compress receipt output-directory");
   let output=Path::new(&args[3]);fs::create_dir_all(output).unwrap();
   if let Ok(destination)=fs::canonicalize(output.join("receipt.bin")) {
    assert_ne!(fs::canonicalize(&args[2]).unwrap(),destination,"use a distinct receipt output path; in-place compression is refused before deletion");
   }
   for file in ["receipt.bin","compress-metrics.json"] {let _=fs::remove_file(output.join(file));}
   let bytes=bounded(&args[2],64*1024*1024);
   let receipt:Receipt=bincode::DefaultOptions::new().with_fixint_encoding().with_limit(64*1024*1024).reject_trailing_bytes().deserialize(&bytes).unwrap();
   assert!(!matches!(receipt.inner,InnerReceipt::Fake(_)),"fake receipt forbidden");
   receipt.verify(CHECKPOINT_GUEST_ID).unwrap();
   let start=Instant::now();let compressed=default_prover().compress(&ProverOpts::succinct(),&receipt).unwrap();
   let compress_ms=start.elapsed().as_millis();
   assert!(matches!(compressed.inner,InnerReceipt::Succinct(_)));compressed.verify(CHECKPOINT_GUEST_ID).unwrap();assert_eq!(compressed.journal.bytes,receipt.journal.bytes);
   let bytes=bincode::serialize(&compressed).unwrap();let dir=Path::new(&args[3]);fs::create_dir_all(dir).unwrap();fs::write(dir.join("receipt.bin"),&bytes).unwrap();
   let metrics=serde_json::json!({"compress_ms":compress_ms,"receipt_bytes":bytes.len(),"receipt_kind":"succinct","verified":true,"sdk":"3.0.6"});
   fs::write(dir.join("compress-metrics.json"),serde_json::to_vec_pretty(&metrics).unwrap()).unwrap();println!("{metrics}");
  },
  Some("verify")=>{
   assert_eq!(args.len(),5,"verify receipt expected-journal snapshot");
   let bytes=bounded(&args[2],64*1024*1024);
   let receipt:Receipt=bincode::DefaultOptions::new().with_fixint_encoding().with_limit(64*1024*1024).reject_trailing_bytes().deserialize(&bytes).unwrap();
   let expected:Journal=serde_json::from_slice(&bounded(&args[3],65536)).unwrap();
   let state=String::from_utf8(bounded(&args[4],8*1024*1024)).unwrap();
   let start=Instant::now();verify(&receipt,&expected,&state);
   println!("{}",serde_json::json!({"verified":true,"verify_ms":start.elapsed().as_millis(),"count":expected.count,"history_files_read":0}));
  },
  Some(mode @ ("native"|"execute"|"prove"))=>{
   assert_eq!(args.len(),4,"native|execute|prove input output-directory");
   let bytes=bounded(&args[2],MAX_INPUT as u64);let dir=Path::new(&args[3]);fs::create_dir_all(dir).unwrap();
   if mode=="prove" {for file in ["receipt.bin","prove-metrics.json"] {let _=fs::remove_file(dir.join(file));}}
   let native_start=Instant::now();let computed=compute(&bytes).unwrap();let native_ms=native_start.elapsed().as_millis();
   fs::write(dir.join("state.json"),&computed.state).unwrap();
   fs::write(dir.join("expected.json"),serde_json::to_vec_pretty(&computed.journal).unwrap()).unwrap();
   fs::write(dir.join("image-id.json"),serde_json::to_vec(&CHECKPOINT_GUEST_ID).unwrap()).unwrap();
   let mut metrics=serde_json::json!({"mode":mode,"native_ms":native_ms,"count":computed.journal.count,"state_bytes":computed.state.len(),"sdk":"3.0.6","proof_generated":false,"segment_po2":segment_po2()});
   if mode!="native" {
    let mut builder=ExecutorEnv::builder();
    builder.write(&(bytes.len() as u32)).unwrap().write_slice(&bytes).segment_limit_po2(segment_po2()).session_limit(Some(32*1024*1024));
    let environment=builder.build().unwrap();let start=Instant::now();
    if mode=="execute" {
     let session=default_executor().execute(environment,CHECKPOINT_GUEST_ELF).unwrap();
     let journal:Journal=session.journal.decode().unwrap();assert_eq!(journal,computed.journal);
     metrics["execute_ms"]=(start.elapsed().as_millis() as u64).into();
     metrics["segments"]=session.segments.len().into();
     metrics["cycles"]=session.cycles().into();
    } else {
     let info=default_prover().prove(environment,CHECKPOINT_GUEST_ELF).unwrap();
     metrics["prove_including_execute_ms"]=(start.elapsed().as_millis() as u64).into();
     let receipt=info.receipt;let check=Instant::now();verify(&receipt,&computed.journal,&computed.state);
     metrics["verify_ms"]=(check.elapsed().as_millis() as u64).into();
     metrics["receipt_kind"]=match &receipt.inner {InnerReceipt::Composite(_)=>"composite",InnerReceipt::Succinct(_)=>"succinct",InnerReceipt::Groth16(_)=>"groth16",_=>"other"}.into();
     let serialized=bincode::serialize(&receipt).unwrap();metrics["receipt_bytes"]=serialized.len().into();metrics["proof_generated"]=true.into();
     fs::write(dir.join("receipt.bin"),serialized).unwrap();
     assert!(receipt.verify([0u32;8]).is_err(),"wrong image accepted");
    }
   }
   fs::write(dir.join(format!("{mode}-metrics.json")),serde_json::to_vec_pretty(&metrics).unwrap()).unwrap();println!("{metrics}");
  },
  _=>panic!("usage: checkpoint-host native|execute|prove input output-directory; verify receipt expected snapshot"),
 }
}
