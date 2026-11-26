// Adapted from cbcl-bus, Apache-2.0.
// SPEC-097 CON-002. This host-owned closure is the authority, never a view message.
import { viewCapabilities, requestArguments } from './policy.js';

const failure = code => new Error('Request ' + code);

export function createRequestBroker(manifest, grants = [], { fetch: fetcher = globalThis.fetch, now = Date.now } = {}) {
  const operations = new Map(viewCapabilities(manifest).requests.map(operation => [operation.id, operation]));
  if (!Array.isArray(grants) || new Set(grants).size !== grants.length || grants.some(id => !operations.has(id))) throw new Error('Invalid capability grant');
  const allowed = new Set(grants), pending = new Set(), started = [];
  let active = true;

  async function request(id, args = {}) {
    if (!active) throw failure('revoked');
    if (!allowed.has(id)) throw failure('denied');
    const operation = operations.get(id);
    let values;
    try { values = requestArguments(operation, args); } catch { throw failure('invalid'); }
    const time = now();
    while (started.length && time - started[0] >= 60000) started.shift();
    if (pending.size >= 2 || started.length >= 30) throw failure('limited');
    const url = new URL(operation.url);
    for (const [name, value] of Object.entries(values)) url.searchParams.set(name, value);
    const controller = new AbortController();
    pending.add(controller); started.push(time);
    const timeout = setTimeout(() => controller.abort(), 10000);
    try {
      const response = await fetcher(url.href, {
        method: 'GET', credentials: 'omit', redirect: 'error',
        referrerPolicy: 'no-referrer', cache: 'no-store', signal: controller.signal,
      });
      if (!active) throw failure('revoked');
      if (controller.signal.aborted || !response.ok || response.redirected) throw failure('failed');
      const type = (response.headers.get('content-type') || '').split(';')[0].trim().toLowerCase();
      if (operation.response === 'json' && type !== 'application/json' && !/^application\/[a-z0-9!#$&^_.+-]+\+json$/.test(type)) throw failure('failed');
      const text = await boundedText(response, 262144, controller.signal);
      if (!active) throw failure('revoked');
      if (controller.signal.aborted) throw failure('failed');
      return operation.response === 'json' ? JSON.parse(text) : text;
    } catch {
      throw failure(active ? 'failed' : 'revoked');
    } finally {
      clearTimeout(timeout); controller.abort(); pending.delete(controller);
    }
  }

  function destroy() {
    active = false;
    allowed.clear();
    for (const controller of pending) controller.abort();
  }
  return Object.freeze({ request, destroy });
}

/** Count streamed bytes, rather than trusting a server's Content-Length. */
export async function boundedText(response, limit, signal) {
  const reader = response.body?.getReader();
  if (!reader) return '';
  const decoder = new TextDecoder('utf-8', { fatal: true });
  let size = 0, text = '';
  try {
    while (true) {
      if (signal.aborted) throw failure('failed');
      const { done, value } = await reader.read();
      if (done) break;
      size += value.byteLength;
      if (size > limit) throw failure('failed');
      text += decoder.decode(value, { stream: true });
    }
    return text + decoder.decode();
  } finally {
    await reader.cancel().catch(() => {});
    reader.releaseLock();
  }
}
