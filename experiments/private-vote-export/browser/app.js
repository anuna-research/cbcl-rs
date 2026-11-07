const output = document.querySelector('#output');
const cancelButton = document.querySelector('#cancel');
cancelButton.disabled = true;
let active;
let activeCancel;
let busy = false;
let phaseWrites = [];
const log = (value) => { output.textContent += `${JSON.stringify(value)}\n`; };
const post = async (path, body, type) => {
  const response = await fetch(path, { method: 'POST', headers: { 'Content-Type': type }, body });
  if (!response.ok) throw new Error(`could not record ${path}`);
};
async function runWorker(action, cancelAt, proof, io) {
  return new Promise((resolve, reject) => {
    const worker = new Worker('/worker.js', { type: 'module' }); active = worker; cancelButton.disabled = false;
    let cancelled = false;
    activeCancel = () => { cancelled = true; worker.terminate(); active = undefined; activeCancel = undefined; resolve({ ok: true, cancelled: true, exported: false }); };
    worker.onerror = (event) => { worker.terminate(); active = undefined; activeCancel = undefined; reject(new Error(event.message)); };
    worker.onmessage = ({ data }) => {
      if (cancelled) return;
      if (data.type === 'phase') {
        log(data);
        const write = post('/phase', JSON.stringify(data), 'application/json');
        phaseWrites.push(write);
        write.catch((error) => { worker.terminate(); reject(error); });
        if (cancelAt === data.name) {
          cancelled = true; worker.terminate(); active = undefined; activeCancel = undefined;
          resolve({ ok: true, cancelled: true, at: cancelAt, linear_memory_bytes: data.linear_memory_bytes });
        }
      } else if (data.type === 'result' && !cancelled) {
        worker.terminate(); active = undefined; activeCancel = undefined;
        if (!data.result.ok) { const failure = new Error(data.result.error); failure.worker = data.result; reject(failure); } else resolve(data.result);
      }
    };
    worker.postMessage({ action, proof, io });
  });
}
window.runExperiment = async (mode) => {
  if (busy) return { ok: false, error: 'an export is already running' };
  busy = true; phaseWrites = []; output.textContent = ''; const started = performance.now();
  let result;
  try {
    if (mode === 'verify') result = await runWorker('verify-cases');
    else if (mode === 'count') result = await runWorker('count');
    else if (mode === 'cancel-trace' || mode === 'cancel-prove') {
      const cancelAt = mode === 'cancel-trace' ? 'trace' : 'prove';
      const cancelled = await runWorker('prove', cancelAt);
      if (!cancelled.cancelled) throw new Error('work finished without exercising cancellation');
      const recovery = await runWorker('verify');
      result = { ...cancelled, recovery };
    } else if (mode === 'prove') {
      const generated = await runWorker('prove');
      if (generated.cancelled) {
        result = { ...generated, mode, wall_ms: performance.now() - started };
        await Promise.all(phaseWrites); await post('/result', JSON.stringify(result), 'application/json'); log(result); return result;
      }
      const proof = generated.proof; const io = generated.io;
      const recovery = await runWorker('verify', undefined, proof, io);
      if (!recovery.verified) throw new Error('fresh browser verifier rejected proof');
      // Publication is the commit point after successful fresh verification.
      cancelButton.disabled = true;
      log({ phase: 'publishing-verified-proof', cancellable: false });
      await post('/artifact/proof', proof, 'application/octet-stream');
      await post('/artifact/io', io, 'application/octet-stream');
      delete generated.proof; delete generated.io;
      result = { ...generated, recovery, exported: true };
    } else throw new Error('unknown mode');
    result.mode = mode; result.wall_ms = performance.now() - started;
    log(result); await Promise.all(phaseWrites); await post('/result', JSON.stringify(result), 'application/json'); return result;
  } catch (error) {
    active?.terminate(); active = undefined;
    result = { ok: false, mode, error: String(error.message ?? error), worker: error.worker ?? null, wall_ms: performance.now() - started };
    log(result); await Promise.all(phaseWrites); await post('/result', JSON.stringify(result), 'application/json'); return result;
  } finally { busy = false; cancelButton.disabled = true; }
};
for (const button of document.querySelectorAll('[data-mode]')) button.onclick = () => window.runExperiment(button.dataset.mode);
document.querySelector('#cancel').onclick = () => { activeCancel?.(); };
