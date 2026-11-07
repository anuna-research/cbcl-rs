"""Direct VM rejection evidence; deliberately does not run host native prechecks."""
import json,os,pathlib,subprocess,time
exp=pathlib.Path(__file__).resolve().parent;root=exp.parents[1]
out=pathlib.Path(os.environ.get('CBCL_VOTE_OUTPUT',root/'outputs/private-vote-export')).resolve()
fixture=out/'negative-fixtures';results=[]
positive=json.loads((out/'clear-count/execution.json').read_text())
assert positive['proof_generated'] is False and positive['within_trace_bound'] is True
assert positive['guest_elf_sha256'], 'positive VM control required'
for case in json.loads((fixture/'manifest.json').read_text()):
 name=case['name'];dest=out/('guest-negative-'+name)
 command=['python3',str(exp/'run-host.py'),'clear','guest-check',str(fixture/case['path']),case['error'],str(dest)]
 start=time.monotonic();run=subprocess.run(command,capture_output=True,text=True,timeout=180)
 log=out/(name+'-guest.log');log.write_text(run.stdout+run.stderr)
 record={'case':name,'exit_code':run.returncode,'seconds':time.monotonic()-start,'host_native_precheck':False,'guest_rejected':False}
 if run.returncode==0:
  metrics=json.loads((dest/'execution.json').read_text());assert metrics['guest_elf_sha256']==positive['guest_elf_sha256'];record['guest_rejected']=metrics.get('guest_rejected',False);record['trace_rows']=metrics['trace_rows'];record['reason']=metrics.get('reason')
 results.append(record)
 (out/'guest-negatives.json').write_text(json.dumps(results,indent=2)+'\n')
 assert record['guest_rejected'],record
print(json.dumps(results,indent=2))
