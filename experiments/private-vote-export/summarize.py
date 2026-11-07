"""Collect measured successful runs; never turn execution-only evidence into proofs."""
import hashlib,json,os,pathlib
exp=pathlib.Path(__file__).resolve().parent;root=exp.parents[1]
out=pathlib.Path(os.environ.get('CBCL_VOTE_OUTPUT',root/'outputs/private-vote-export')).resolve()
rows=[];images=set()
for mode in ('clear','zk'):
 p=out/(mode+'-proof');m=json.loads((p/'metrics.json').read_text());run=json.loads((out/(mode+'-proof-run.json')).read_text())
 assert m['proof_generated'] and run['exit_code']==0 and run['limit_reason'] is None
 assert m['zk']==(mode=='zk');images.add(bytes(m['guest_elf_sha256']).hex())
 cases=json.loads((out/(mode+'-receiver-cases/results.json')).read_text());assert all(c['accepted']==c['expected_accepted'] for c in cases)
 receiver=next(c for c in cases if c['case']=='honest');fresh=json.loads(receiver['output'])
 pins=out/'operator-pins'/mode
 warm=sum((p/n).stat().st_size for n in ('proof.bin','io.bin'))+(pins/'expected.json').stat().st_size
 cold=warm+(p/'setup.bin').stat().st_size+(pins/'trusted.json').stat().st_size
 rows.append({'mode':mode,'metrics':m,'managed_run':run,'fresh_receiver':fresh,'receiver_wall_seconds':receiver['wall_seconds'],'warm_public_bundle_bytes':warm,'cold_public_bundle_bytes':cold,'verifier_software_excluded':True})
assert len(images)==1,'guest images differ'
assert (out/'clear-proof/io.bin').read_bytes()==(out/'zk-proof/io.bin').read_bytes(), 'public IO differs'
result={'rows':rows,'guest_elf_sha256':next(iter(images)),'fixture_input_sha256':hashlib.sha256((out/'fixture/input.json').read_bytes()).hexdigest(),'fixture_expected_sha256':hashlib.sha256((out/'fixture/expected.json').read_bytes()).hexdigest(),'note':'single local observations; build, key acquisition and verifier software separately scoped'}
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
