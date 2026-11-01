#!/usr/bin/env python3
"""Verify frozen evidence and agreement between curated matrix and Elephant export.
No external network access or third-party packages; not a semantic truth checker.
"""
from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent; root=p.parent.parent
m=json.loads((p/'matrix.json').read_text()); catalog=json.loads((p/'source-catalog.json').read_text()); baseline=json.loads((p/'baseline.json').read_text())
allowed={'native','partial','external','unknown','excluded'}
def digest(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def symbol(s):return re.sub('[^a-z0-9-]','-',s.lower()).strip('-')
refs={s['id'] for s in catalog}|{s['id'] for s in baseline}
for s in catalog:assert digest(p/(s['id']+'.json'))==s['sha256'],s['id']
for b in baseline:assert digest(root/b['path'])==b['sha256'],b['path']
status=json.loads((p/'elephant-status.json').read_text())
positive={c['literal'] for c in status['conclusions'] if c.get('positive') and c.get('tag')=='+D'}
expected=set(); native=set()
for row in m['rows']:
 assert set(row['assessments'])==set(m['axes']),row['project']
 assert set(row['sources'])<=refs,row['project']
 for axis,rate in row['assessments'].items():
  assert rate in allowed
  expected.add(f"assessment {symbol(row['project'])} {axis} {rate} {row['sources'][0].lower()}")
  if rate=='native':native.add(f"documented-support {symbol(row['project'])} {axis}")
actual={s for s in positive if s.startswith('assessment ')}
assert expected==actual,{'missing':sorted(expected-actual),'extra':sorted(actual-expected)}
assert {s for s in positive if s.startswith('documented-support ')}==native
assert 'finding universal-uniqueness-unestablished' in positive
assert not any(s.startswith('full-bundle-demonstrated ') for s in positive)
report={'passed':True,'candidates':len(m['rows']),'axes':len(m['axes']),'active_assessments':len(actual),'derived_native_support':len(native),'captured_source_attempts':len(catalog),'usable_source_captures':sum(s['usable'] for s in catalog),'baseline_hashes':len(baseline),'limitations':'Checks integrity and consistency; does not prove curated assessments true or completeness of search.'}
print(json.dumps(report,indent=2))
