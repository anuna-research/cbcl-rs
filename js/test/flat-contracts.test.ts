import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { verifyShape, describeDialect, compileContract } from '../src/index.ts';
import { verify_message_shape } from '../src/cbcl_wasm.js';

const cases = JSON.parse(await readFile(new URL('../../test-vectors/contracts/flat-contracts.json', import.meta.url), 'utf8')) as {id:string;frame:string;accept:boolean;errorContains?:string}[];
test('SPEC-040 shared vectors run in actual browser WASM', () => {
  for (const c of cases) {
    let error = '';
    try { assert.equal(verify_message_shape(c.frame), 'ok', c.id); }
    catch (e) { error = String(e); }
    assert.equal(error === '', c.accept, `${c.id}: ${error}`);
    if (c.errorContains) assert.ok(error.includes(c.errorContains), `${c.id}: ${error}`);
  }
});
test('SPEC-040 optional metadata and JSON authoring use the same checker', () => {
  const result = compileContract(JSON.stringify({version:3,kind:'contract',name:'prices',types:{price:'(decimal (>= 0))'},verbs:{open:{after:['begin'],fields:{price:'price'}}},state:{price:['initial','open','price']}}));
  const info = describeDialect(result.dialect);
  assert.deepEqual(info.types.price.representations, ['decimal']);
  const source = '(define optional (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (optional :value (one-of :AUD :USD) (default :AUD))))';
  const optional = describeDialect(source);
  assert.equal(optional.verbs.submit.contracts.value.required, false);
  assert.equal(optional.verbs.submit.contracts.value.default, ':AUD');
  assert.equal(verifyShape(source, 'submit', '(submit :value :USD)').ok, true);
  assert.equal(verifyShape(source, 'submit', '(submit :value :EUR)').ok, false);
});
test('SPEC-040 maximum-input adversarial regex remains bounded in WASM', () => {
  const source = '(define bounded (cbcl) @author (extend submit (to value) (tell to :value value)) (shape submit (require :value (string (matches "(a|aa)*b")))))';
  for (const suffix of ['b','a']) {
    const now=performance.now();
    const result=verifyShape(source,'submit',`(submit :value "${'a'.repeat(65534)}${suffix}")`);
    assert.equal(result.ok,suffix==='b');
    console.log(`SPEC040 WASM max-input suffix=${suffix}: ${(performance.now()-now).toFixed(3)}ms`);
  }
});
