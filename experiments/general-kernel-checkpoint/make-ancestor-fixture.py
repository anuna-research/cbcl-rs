import json
from pathlib import Path
p=json.loads(Path('fixtures/status-1.json').read_text())
parent='(define checkpoint-parent (cbcl) @author (:resource-requirements ((max-depth 16) (max-expansion-size 4096) (verification-time 1000))) (extend parent-tell (to value) (tell to value)))'
leaf=p['dialect'].replace('(cbcl)','(checkpoint-parent)',1).replace('(tell to :title title)','(parent-tell to title)').replace('(tell to :value value)','(parent-tell to value)')
leaf=leaf.replace('(protocol ', '(protocol (then open parent-tell) ',1)
p['dialect']='(dialects '+parent+' '+leaf+')'
Path('fixtures/ancestor-status.json').write_text(json.dumps(p,indent=2)+'\n')
Path('fixtures/ancestor-status-state.json').write_text(Path('fixtures/status-1-state.json').read_text())
