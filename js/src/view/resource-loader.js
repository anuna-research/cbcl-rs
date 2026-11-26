// Adapted from cbcl-bus, Apache-2.0.
// SPEC-097: resources are fixed host requests, never frame URL permissions.
import { viewResources } from './policy.js';

export async function loadViewResources(requested, approved, signal, fetcher = globalThis.fetch) {
  const wanted = viewResources(requested), grants = viewResources(approved);
  for (const kind of ['images', 'styles']) if (grants[kind].some(url => !wanted[kind].includes(url))) throw Error('Invalid resource grant');
  const images = new Map(), styles = new Map();
  const queue = ['images','styles'].flatMap(kind => grants[kind].map(url => ({ kind, url })));
  const failures = [];
  async function consume() {
    while (queue.length && !signal.aborted) {
      const { kind, url } = queue.shift();
      const controller = new AbortController();
      const abort = () => controller.abort(); signal.addEventListener('abort', abort, { once: true });
      const timeout = setTimeout(abort, 10000);
      try {
        const response = await fetcher(url, { method: 'GET', credentials: 'omit', redirect: 'error', referrerPolicy: 'no-referrer', cache: 'no-store', signal: controller.signal });
        if (!response.ok || response.redirected) throw Error('Resource failed');
        const type = (response.headers.get('content-type') || '').split(';')[0].trim().toLowerCase();
        if (kind === 'styles' ? type !== 'text/css' : !['image/png','image/jpeg','image/gif','image/webp','image/avif','image/svg+xml'].includes(type)) throw Error('Resource type');
        const reader = response.body.getReader(); const chunks = []; let size = 0;
        try {
          while (true) {
            const { done, value } = await reader.read(); if (done) break;
            size += value.byteLength; if (size > 1048576 || controller.signal.aborted) throw Error('Resource limit');
            chunks.push(value);
          }
        } finally { await reader.cancel().catch(() => {}); reader.releaseLock(); }
        if (signal.aborted || controller.signal.aborted) throw Error('Resource revoked');
        const bytes = new Uint8Array(size); let offset = 0;
        for (const chunk of chunks) { bytes.set(chunk, offset); offset += chunk.length; }
        if (kind === 'styles') styles.set(url, new TextDecoder('utf-8', { fatal: true }).decode(bytes));
        else {
          let binary = ''; for (let n = 0; n < bytes.length; n += 8192) binary += String.fromCharCode(...bytes.subarray(n, n + 8192));
          images.set(url, `data:${type};base64,${btoa(binary)}`);
        }
      } catch { if (!signal.aborted) failures.push('An approved resource could not be loaded.'); }
      finally { clearTimeout(timeout); controller.abort(); signal.removeEventListener('abort', abort); }
    }
  }
  await Promise.all([consume(), consume()]);
  return { images, styles: grants.styles.filter(url => styles.has(url)).map(url => styles.get(url)), failures };
}
