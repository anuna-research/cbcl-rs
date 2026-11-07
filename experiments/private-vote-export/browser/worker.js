import init, { verify_export, prove_export, check_guest_rejection } from './pkg/cbcl_vote_browser.js';
let wasm;
self.cbclPhase = (name) => self.postMessage({ type: 'phase', name, linear_memory_bytes: wasm?.memory.buffer.byteLength ?? 0 });
const read = async (name) => {
  const response = await fetch(`/assets/${name}`);
  if (!response.ok) throw new Error(`asset unavailable: ${name}`);
  return new Uint8Array(await response.arrayBuffer());
};
const json = (bytes) => JSON.parse(new TextDecoder().decode(bytes));
const bytes = (value) => new TextEncoder().encode(JSON.stringify(value));
self.onmessage = async ({ data }) => {
  try {
    wasm = await init();
    const expected = await read('expected.json');
    const pin = await read('trusted.json');
    const setup = await read('setup.bin');
    const verify = (proof, io, statement = expected, selectedSetup = setup) => JSON.parse(verify_export(selectedSetup, proof, io, statement, pin));
    if (data.action === 'verify' || data.action === 'verify-cases') {
      const proof = data.proof ? new Uint8Array(data.proof) : await read('proof.bin');
      const io = data.io ? new Uint8Array(data.io) : await read('io.bin');
      self.cbclPhase('verify-native-artifact');
      const honest = verify(proof, io);
      if (data.action === 'verify') {
        self.postMessage({ type: 'result', result: { ok: true, verified: honest.verified, metrics: honest } }); return;
      }
      const cases = [{ name: 'honest', accepted: true, metrics: honest }];
      const reject = (name, run, reason) => {
        let failure;
        try { run(); } catch (error) { failure = String(error.message ?? error); }
        if (!failure || !failure.includes(reason)) throw new Error(`${name}: expected ${reason}, received ${failure}`);
        cases.push({ name, accepted: false, reason: failure });
      };
      const other = json(expected); other.thread = 'other-thread';
      reject('wrong-context', () => verify(proof, io, bytes(other)), 'expected statement differs');
      const alteredSetup = setup.slice(); alteredSetup[alteredSetup.length - 1] ^= 1;
      reject('wrong-setup', () => verify(proof, io, expected, alteredSetup), 'untrusted setup');
      const clear = await read('clear-proof.bin');
      reject('clear-proof', () => verify(clear, io), 'ZK required');
      const coherentIo = await read('coherent-io.bin');
      const coherentExpected = await read('coherent-expected.json');
      reject('coherent-outcome-tamper', () => verify(proof, coherentIo, coherentExpected), 'verification:');
      const adviceIo = await read('advice-io.bin');
      reject('populated-advice', () => verify(proof, adviceIo), 'advice leaked');
      self.postMessage({ type: 'result', result: { ok: true, verified: true, cases, linear_memory_bytes: wasm.memory.buffer.byteLength } }); return;
    }
    if (!['count', 'prove'].includes(data.action)) throw new Error('unknown worker request');
    const elf = await read('guest.elf');
    const proverSetup = await read('prover-setup.bin');
    const profile = await read('profile.json');
    const input = await read('witness.json');
    const result = prove_export(elf, input, expected, proverSetup, profile, data.action === 'count');
    const metrics = JSON.parse(result.metrics());
    const proof = result.proof_bytes(); const io = result.io_bytes(); result.free();
    if (data.action === 'count') {
      const cases = [];
      for (const [name, asset, reason] of [['missing-closure', 'missing-closure.json', 'missing closure signer'], ['bad-signature', 'bad-signature.json', 'invalid signature']]) {
        self.cbclPhase(`guest-negative-${name}`);
        const invalid = await read(asset);
        cases.push({ name, ...JSON.parse(check_guest_rejection(elf, invalid, proverSetup, profile, reason)) });
      }
      const overCap = await read('over-cap.json'); const overCapExpected = await read('over-cap-expected.json');
      self.cbclPhase('over-cap-control');
      let failure;
      try { prove_export(elf, overCap, overCapExpected, proverSetup, profile, true); }
      catch (error) { failure = String(error.message ?? error); }
      if (!failure?.includes('trace bound')) throw new Error(`expected trace bound, received ${failure}`);
      const recovery = verify(await read('proof.bin'), await read('io.bin'));
      if (!recovery.verified) throw new Error('resource-bound recovery failed');
      cases.push({ name: 'trace-budget', rejected: true, reason: failure, recovery });
      self.postMessage({ type: 'result', result: { ok: true, metrics, cases, linear_memory_bytes: wasm.memory.buffer.byteLength } });
    } else {
      if (!metrics.proof_generated || !metrics.zk || !proof.length || !io.length) throw new Error('proof missing');
      self.postMessage({ type: 'result', result: { ok: true, metrics, proof: proof.buffer, io: io.buffer, linear_memory_bytes: wasm.memory.buffer.byteLength } }, [proof.buffer, io.buffer]);
    }
  } catch (error) {
    self.postMessage({ type: 'result', result: { ok: false, error: String(error.message ?? error), stack: String(error.stack ?? '').slice(0, 16000), linear_memory_bytes: wasm?.memory.buffer.byteLength ?? 0 } });
  }
};
