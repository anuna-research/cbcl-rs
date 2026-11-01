#!/usr/bin/env python3
"""Local research integrity/claim checks; no semantic completeness claim."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
pins=json.loads((p/'source-pins.json').read_text())
for f in pins['files']:
 source=Path(pins['repositories'][f['repository']]['root'])/f['path']
 assert hashlib.sha256(source.read_bytes()).hexdigest()==f['sha256'],str(source)
b=json.loads((p/'bspl-probe-results.json').read_text())
assert b['quote_value_binding']=={'good_integrity':True,'changed_price_integrity':False,'good_emission':True,'changed_price_emission':False}
assert b['dependency_checker_early_return']['returned'] and not b['dependency_checker_early_return']['all_required_known']
assert b['nil_is_local']['right_enabled_after_left_sent_not_received']
assert b['static_purchase']['safety']['safe'] and b['static_purchase']['liveness']['live']
assert not b['static_conflicting_producers']['safe']
assert not b['static_circular_knowledge']['live']
assert b['refinement_ship_first']['ok']
assert b['handoff']=={'B_can_send_N_after_receiving_M':True,'C_observed_M':False}
r=(p/'cbcl-probe-results.txt').read_text()
assert 'changed_price_missing_quote=Unknown' in r
assert 'changed_price_with_quote=Valid' in r and 'changed_price_shape_ok=true' in r
assert 'NotCausallyLocal' in r
status=json.loads((p/'elephant-status.json').read_text())
assert any(c['literal']=='finding bspl-close-language-comparator' and c['positive'] and c['tag']=='+D' for c in status['conclusions'])
assert (p.parent/'cbcl-bspl-source-review.md').exists()
print(json.dumps({'passed':True,'scope':'Source hashes, focused observed distinctions, signed conclusion and review presence; not external semantic truth or full implementation verification.'},indent=2))
