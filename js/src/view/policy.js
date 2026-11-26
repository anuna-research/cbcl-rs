// Adapted from cbcl-bus. Copyright 2026 Anuna Research Pty Ltd. Apache-2.0.
// SPEC-097 CON-001: pure recognition before granting or performing any effect.
import { validateLimits } from './operations.ts';
const identifier = /^[A-Za-z][A-Za-z0-9_-]{0,47}$/;
function invalid(message) { throw new Error('Invalid view capability: ' + message); }
function record(value, required, optional = []) {
  if (!value || typeof value !== 'object' || Array.isArray(value)
      || ![Object.prototype, null].includes(Object.getPrototypeOf(value))
      || required.some(key => !Object.hasOwn(value, key))
      || Object.keys(value).some(key => !required.includes(key) && !optional.includes(key))) invalid('record');
}
export function viewCapabilities(value = {}) {
  record(value, [], ['requests', 'operations', 'sound', 'media']);
  const operations = Object.hasOwn(value, 'operations') ? value.operations : [];
  if (!Array.isArray(operations)) invalid('operations');
  const ids = new Set();
  for (const declaration of operations) {
    if (typeof declaration !== 'string') {
      record(declaration, ['id'], ['limits']);
      if (Object.hasOwn(declaration, 'limits')) validateLimits(declaration.limits);
    }
    const id = typeof declaration === 'string' ? declaration : declaration.id;
    if (typeof id !== 'string' || !/^[a-zA-Z][a-zA-Z0-9_-]*(?:\.[a-zA-Z][a-zA-Z0-9_-]*)*$/.test(id) || ids.has(id)) invalid('operation name');
    ids.add(id);
  }
  if (Object.hasOwn(value, 'sound') && typeof value.sound !== 'boolean') invalid('sound');
  let media = null;
  if (Object.hasOwn(value, 'media')) {
    record(value.media, ['accept']);
    const accept = value.media.accept;
    if (!Array.isArray(accept) || !accept.length || accept.length > 2 || new Set(accept).size !== accept.length || accept.some(kind => !['image', 'audio'].includes(kind))) invalid('media');
    media = Object.freeze({ accept: Object.freeze([...accept]) });
  }
  const requests = value.requests ?? [];
  if (!Array.isArray(requests) || requests.length > 8 || (Object.hasOwn(value, 'requests') && value.requests === null)) invalid('operations');
  const names = new Set();
  return Object.freeze({ operations: Object.freeze([...operations]), sound: value.sound === true, ...(media ? {media} : {}), requests: Object.freeze(requests.map(operation => {
    record(operation, ['id', 'url', 'response'], ['parameters']);
    const { id, url, response } = operation;
    if (typeof id !== 'string' || !identifier.test(id) || names.has(id)) invalid('operation id');
    names.add(id);
    if (typeof url !== 'string' || url.length > 2048) invalid('URL');
    let parsed; try { parsed = new URL(url); } catch { invalid('URL'); }
    if (parsed.protocol !== 'https:' || parsed.username || parsed.password || parsed.hash || parsed.href !== url) invalid('URL');
    if (!['json', 'text'].includes(response)) invalid('operation response');
    const parameters = Object.hasOwn(operation, 'parameters') ? operation.parameters : [];
    if (!Array.isArray(parameters) || parameters.length > 8 || new Set(parameters).size !== parameters.length
        || parameters.some(name => typeof name !== 'string' || !identifier.test(name) || parsed.searchParams.has(name))) invalid('parameters');
    return Object.freeze({ id, url, response, parameters: Object.freeze([...parameters]) });
  })) });
}

// Author requests are data; only the trusted host grants resource permissions.
export function viewResources(value = {}) {
  if (!value || typeof value !== 'object' || Array.isArray(value)
      || Object.keys(value).some(key => !['images', 'styles'].includes(key))) throw new Error('Invalid image/style resource request');
  const result = {};
  for (const kind of ['images', 'styles']) {
    const list = Object.hasOwn(value, kind) ? value[kind] : [];
    if (!Array.isArray(list) || list.length > 8 || new Set(list).size !== list.length) throw new Error('Resource list must contain at most 8 unique URLs');
    result[kind] = Object.freeze(list.map(raw => {
      if (typeof raw !== 'string' || raw.length > 2048 || /[\s"'<>;,*]/.test(raw)) throw new Error('Invalid resource URL');
      let url; try { url = new URL(raw); } catch { throw new Error('Invalid resource URL'); }
      if (url.protocol !== 'https:' || url.username || url.password || url.search || url.hash
          || url.pathname.endsWith('/') || url.href !== raw) throw new Error('Resources require canonical HTTPS file URLs without credentials, queries or fragments');
      return raw;
    }));
  }
  return Object.freeze(result);
}

export function requestArguments(operation, value = {}) {
  record(value, [], operation.parameters || []);
  const copy = Object.create(null);
  for (const [key, text] of Object.entries(value)) {
    if (typeof text !== 'string' || text.length > 2048) invalid('parameter value');
    copy[key] = text;
  }
  return copy;
}
