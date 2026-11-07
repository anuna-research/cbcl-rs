#!/usr/bin/env python3
"""Execute patched upstream partition/capacity expressions on wasm32, no prover.

Usage: python3 check-partitions.py JOLT_DIR OUTPUT_DIR
Requires rustc with wasm32-unknown-unknown and Node. Evidence stays in OUTPUT_DIR.
"""
import json
from pathlib import Path
import re
import subprocess
import sys

source = Path(sys.argv[1]) / 'crates/jolt-kernels/src/optimized/registers_read_write/sparse/ops.rs'
out = Path(sys.argv[2]).resolve()
out.mkdir(parents=True, exist_ok=False)
text = source.read_text()
expression = re.search(r'let mut index = (.+);', text).group(1)
assert expression == '((block as u128 * len as u128) / block_count as u128) as usize'
capacity = (source.parent.parent / 'sparse.rs').read_text()
capacity_expression = re.search(r'pub\(super\) fn saturated\(&self\) -> bool \{\s*(.*?)\s*\}', capacity, re.S).group(1)
assert capacity_expression == '(self.values.len() as u128) * (self.values.len() as u128) > Self::MAX_VALUES as u128'
capacity_expression = capacity_expression.replace('self.values.len()', 'n').replace('Self::MAX_VALUES', '65536usize')
code = '''#[no_mangle]
pub extern "C" fn boundary(block: usize, len: usize, block_count: usize) -> usize {
    EXPRESSION
}
#[no_mangle]
pub extern "C" fn original_overflows(block: usize, len: usize) -> bool {
    block.checked_mul(len).is_none()
}
'''.replace('EXPRESSION', expression) + '#[no_mangle]\npub extern "C" fn saturated(n: usize) -> bool { ' + capacity_expression + ' }\n'
(out / 'partition.rs').write_text(code)
subprocess.run(['rustc', '--edition=2021', '--crate-type=cdylib', '--target=wasm32-unknown-unknown', '-O', '-C', 'overflow-checks=yes', str(out/'partition.rs'), '-o', str(out/'partition.wasm')], check=True)
js = '''import fs from 'node:fs';
const {instance:{exports:e}} = await WebAssembly.instantiate(fs.readFileSync(process.argv[2]));
let checked=0, formerOverflows=0;
for (const len of [0,1,16383,16384,16385,8388608,16777216,33554432,0x7fffffff,0xffffffff]) {
 const count=Math.max(1,Math.ceil(len/16384));
 let previous=0;
 for(let block=1;block<count;block++) {
  const actual=e.boundary(block,len,count)>>>0;
  const expected=Number(BigInt(block)*BigInt(len)/BigInt(count));
  if(actual!==expected || actual<previous || actual>=len) throw Error(`wrong boundary ${block}/${len}/${count}`);
  previous=actual;checked++;
  formerOverflows+=Number(e.original_overflows(block,len));
 }
}
if(!formerOverflows) throw Error('regression did not exercise former overflow');
let capacityChecked=0;
for(const n of [...Array(65537).keys(),0x7fffffff,0xffffffff]) {
 const expected=BigInt(n)*BigInt(n)>65536n;
 if(Boolean(e.saturated(n))!==expected) throw Error(`wrong saturation ${n}`);
 capacityChecked++;
}
console.log(JSON.stringify({ok:true,target:'wasm32',checked,former_overflows:formerOverflows,capacity_checked:capacityChecked,prover_claim:false}));
'''
(out/'partition.mjs').write_text(js)
result = subprocess.check_output(['node', str(out/'partition.mjs'), str(out/'partition.wasm')], text=True)
(out/'result.json').write_text(result)
print(result,end='')
