#!/usr/bin/env python3
"""Verify using only one copied final proof, a trusted key and native expected head."""
import json,os,shutil,subprocess,tempfile,time
from pathlib import Path
root=Path(__file__).resolve().parent; evidence=root/'evidence/recursive'
with tempfile.TemporaryDirectory(prefix='cbcl-recursive-receiver-') as temporary:
 folder=Path(temporary)
 files={'proof.json':'history-128.json','trusted-key.json':'verification-key.json','expected-head.json':'expected-head-128.json'}
 sizes={}
 for name,source in files.items():
  shutil.copyfile(evidence/source,folder/name);sizes[name]=(folder/name).stat().st_size
 command=['node','--import','tsx','recursive-one-proof.ts',str(folder/'proof.json'),str(folder/'trusted-key.json'),str(folder/'expected-head.json')]
 started=time.monotonic()
 result=subprocess.run(command,cwd=root,env={**os.environ,'CBCL_INCREMENTAL_ORACLE':'/nonexistent/no-native-oracle'},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
 elapsed=time.monotonic()-started
 (evidence/'isolated-receiver.log').write_text(result.stdout.rstrip()+'\n')
 assert result.returncode==0,result.stdout
 parsed=json.loads(result.stdout.strip());assert parsed['verified'] and parsed['completeWrites']=='128'
 record={'exit_code':result.returncode,'complete_writes':128,'input_files':list(files),'input_file_bytes':sizes,'total_input_file_bytes':sum(sizes.values()),'native_oracle_available':False,'predecessor_artifact_files_provided':0,'wall_seconds_including_process_and_backend_startup':round(elapsed,3),'cold_start_measurement_note':'concurrent isolated-mutant compilation may affect wall time'}
 (evidence/'isolated-receiver.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
