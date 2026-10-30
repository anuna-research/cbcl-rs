from pathlib import Path
import subprocess,json,sys,tempfile
root=Path(__file__).resolve().parents[2]
src=(root/'lean-cbcl/LeanCbcl/ConsensusFree/CollectiveProtocol.lean').read_text()
# Mutate executable declarations only; imported checks separately cover the complete proved module.
base=src[:src.index('@[simp] theorem pool_rejected')]
base+=src[src.index('structure State (K T P'):src.index('theorem execute_erases')]
base+=src[src.index('def run (c : Context'):src.index('theorem run_erases')]
base+='\nend CBCL.ConsensusFree.CollectiveActors\n'
tests=(root/'lean-cbcl/CollectiveActorAdversarialReview.lean').read_text().split('\n',1)[1]
mutants={
'baseline':None,
'checkpoint_receipt':('if w ∈ committee.core then checkpointReady s p w else true','true'),
'operation_receipt':('if w ∈ committee.core then opReady c s tx w else true','true'),
'cancel_receipt':('opReady c s tx w && cancelReady c s tx w','opReady c s tx w'),
'cancel_signer':('| .cancellation tx => decide (a = c.actor tx)','| .cancellation _ => true'),
'instance':('decide (packet.domain = c.domain) &&','true &&'),
'checkpoint_role':('p.cast a && (p.role a p.increment || p.role a p.decrement)','p.cast a'),
'genesis_cap':('&& genesisBounds c','&& true'),
'payload_signature':('c.authenticated a packet.domain packet.payload','c.authenticated a packet.domain (match packet.payload with | .cancellation tx => .operation tx | x => x)'),
}
results=[]
scratch=tempfile.TemporaryDirectory(prefix="collective-actor-review-")
for name,mutation in mutants.items():
    code=base
    if mutation:
        assert mutation[0] in code,name
        code=code.replace(*mutation,1)
    path=Path(scratch.name)/('collective_actor_review_'+name+'.lean')
    path.write_text(code+'\n'+tests)
    p=subprocess.run(['lake','env','lean',str(path)],cwd=root/'lean-cbcl',capture_output=True,text=True)
    (root/'outputs'/('collective-actor-review-'+name+'.log')).write_text(p.stdout+p.stderr)
    errors=[line for line in p.stdout.splitlines() if ': error:' in line]
    false_decide=bool(errors) and all('Tactic `decide` proved that the proposition' in line for line in errors) and p.stdout.count('is false') == len(errors)
    passed=(p.returncode == 0) if mutation is None else (p.returncode != 0 and false_decide)
    results.append({'case':name,'exit':p.returncode,'decide_rejections':p.stdout.count('is false'),'passed':passed})
    print(name,p.returncode,p.stdout[-400:])
(root/'outputs/collective-actor-review-mutations.json').write_text(json.dumps(results,indent=2)+'\n')

scratch.cleanup()
sys.exit(0 if all(result["passed"] for result in results) else 1)
