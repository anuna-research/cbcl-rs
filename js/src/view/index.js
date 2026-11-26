// Adapted from cbcl-bus. Copyright 2026 Anuna Research Pty Ltd. Apache-2.0.
// cbcl/view — presentation for a cbcl/object contract (SPEC-085 REQ-003,
// SPEC-087 CON-002). A view is data bound to one dialect by its self-address:
// either declarative components the trusted host renders, or custom HTML/JS
// that runs in the capability sandbox with external access denied by default. Views are outside
// the state layer: nothing here reads or writes an act, and a dialect
// carries no view (SPEC-019 ADR-1907).
import { viewCapabilities, viewResources } from './policy.js';
import { readDialect, isSDKDialect, importObject, MAX_CONTRACT_BYTES, CORE_PERFORMATIVES } from '../object/index.ts';
import { ready, dialectHash, compileContract } from '../verifier.ts';

export const VIEW_VERSION = 3;
export const MAX_VIEW_BYTES = 65536;
export const MAX_CUSTOM_SOURCE_BYTES = 60000;
const bytes = text => new TextEncoder().encode(text).length;
function require(condition, message) { if (!condition) throw new Error(`Object view: ${message}`); }
function record(value, keys, optional = []) {
  require(value && typeof value === 'object' && !Array.isArray(value), 'expected a record');
  require(Object.keys(value).every(key => keys.includes(key) || optional.includes(key)), 'unknown record field');
  require(keys.every(key => Object.hasOwn(value, key)), 'missing record field');
}
function label(value) { require(typeof value === 'string' && bytes(value) <= 2048, 'invalid label'); }

/** Validate presentation against the dialect it is for. `info` is `readDialect(text)`. */
export function validateView(spec, info) {
  if (Object.hasOwn(spec, 'layout')) {
    const layout = spec.layout;
    require(layout && typeof layout === 'object' && !Array.isArray(layout), 'invalid layout');
    require(Object.keys(layout).every(k => ['width', 'minHeight', 'maxHeight', 'aspectRatio', 'overflow'].includes(k)), 'unknown layout field');
    if (Object.hasOwn(layout, 'width')) require(['compact', 'standard', 'wide'].includes(layout.width), 'invalid layout width');
    for (const key of ['minHeight', 'maxHeight']) if (Object.hasOwn(layout, key)) require(Number.isInteger(layout[key]) && layout[key] >= 80 && layout[key] <= 1200, 'invalid layout height');
    require((layout.minHeight ?? 80) <= (layout.maxHeight ?? 1200), 'inverted layout heights');
    if (Object.hasOwn(layout, 'aspectRatio')) require(Number.isFinite(layout.aspectRatio) && layout.aspectRatio >= 0.25 && layout.aspectRatio <= 4, 'invalid aspect ratio');
    if (Object.hasOwn(layout, 'overflow')) require(layout.overflow === 'scroll', 'invalid overflow');
  }
  if (Object.hasOwn(spec, 'capabilities')) {
    viewCapabilities(spec.capabilities);
    require(!Array.isArray(spec.view), 'capabilities require a custom view');
  }
  if (Object.hasOwn(spec, 'resources')) {
    viewResources(spec.resources);
    require(!Array.isArray(spec.view), 'resource requests require a custom view');
  }
  if (!Array.isArray(spec.view)) {
    require(spec.view && typeof spec.view === 'object', 'invalid custom view');
    const kind = Object.hasOwn(spec.view, 'html') ? 'html' : 'render';
    record(spec.view, [kind]);
    require(typeof spec.view[kind] === 'string' && bytes(spec.view[kind]) <= MAX_CUSTOM_SOURCE_BYTES, 'invalid custom view source');
    return;
  }
  require(spec.view.length > 0 && spec.view.length <= 32, 'invalid view');
  for (const component of spec.view) {
    if (component?.type === 'text') { record(component, ['type', 'text']); label(component.text); }
    else if (component?.type === 'value') {
      record(component, ['type', 'field', 'label']); label(component.label);
      require(Object.hasOwn(info.state, component.field), 'unknown view field');
    } else {
      record(component, ['type', 'verb', 'label', 'fields']); label(component.label);
      require(component.type === 'form' && Object.hasOwn(info.verbs, component.verb), 'unknown view component or action');
      require(component.verb !== info.opener, 'view cannot open another object');
      const fields = info.verbs[component.verb].fields;
      // An `hlc` field is the host's timestamp: a form neither lists nor sets it.
      record(component.fields, Object.keys(fields).filter(name => fields[name] !== 'hlc'));
      Object.values(component.fields).forEach(label);
      require(!Object.values(fields).includes('list'), 'forms accept scalar fields only');
    }
  }
}

/** The default presentation: every state field, read-only. */
export function defaultView(info) {
  return { view: Object.keys(info.state).map(field => ({ type: 'value', field, label: field })) };
}

/** Recognise view text: exactly the record a `defineView` writes. */
function viewRecord(text) {
  require(typeof text === 'string' && bytes(text) <= MAX_VIEW_BYTES, 'view exceeds 64 KiB');
  const view = JSON.parse(text);
  record(view, ['version', 'kind', 'contract', 'view'], ['layout', 'resources', 'capabilities', 'composer']);
  require(view.version === VIEW_VERSION && view.kind === 'view' && isSDKDialect(view.contract), 'invalid view record');
  return view;
}

export function recognizeView(text) {
  const { composer: _legacy, ...view } = viewRecord(text);
  return view;
}

function dialectOf(contract) {
  const text = typeof contract === 'string' ? contract : contract?.dialect;
  require(typeof text === 'string', 'expected a contract (from defineContract) or its dialect text');
  return text;
}

/** A presentation bound to a dialect: what a host mounts. */
const verifiedPresentations = new WeakMap();
function freezeRecord(node) {
  if (node && typeof node === 'object') {
    for (const child of Object.values(node)) freezeRecord(child);
    Object.freeze(node);
  }
  return node;
}

async function presentation(view, dialectText, contractText) {
  await ready();
  const info = readDialect(dialectText);
  const name = dialectHash(dialectText);
  require(view.contract === name, `view contract digest mismatch: view is for ${view.contract}, dialect is ${name}`);
  const spec = freezeRecord(view);
  validateView(spec, info);
  const serialized = JSON.stringify(view);
  const crypto = globalThis.crypto?.subtle ?? (await import('node:crypto')).webcrypto.subtle;
  const digest = await crypto.digest('SHA-256', new TextEncoder().encode(serialized));
  const id = 'view-' + Array.from(new Uint8Array(digest), byte => byte.toString(16).padStart(2, '0')).join('');
  const external = !Array.isArray(spec.view);
  const verified = Object.freeze({
    id, contract: name, serialized, view: spec.view, layout: spec.layout, resources: spec.resources, capabilities: spec.capabilities, external,
    /** Bind the sandbox emit callback to a host-selected thread and this verified dialect. */
    bindIntent(thread, broker, options = {}) {
      const { nextClock, signal } = typeof options === 'function' ? { nextClock: options } : options;
      let pending = 0;
      return async (verb, fields = {}) => {
        if (signal?.aborted) return { ok: false, reason: 'Intent binding revoked' };
        if (pending >= 8) return { ok: false, reason: 'Too many pending intents' };
        if (typeof verb !== 'string' || verb === info.opener || CORE_PERFORMATIVES.has(verb) || !Object.hasOwn(info.verbs, verb)) {
          return { ok: false, reason: 'Expected a declared non-opener verb' };
        }
        if (!fields || typeof fields !== 'object' || Array.isArray(fields)) return { ok: false, reason: 'Expected intent fields' };
        pending++;
        try {
          const data = structuredClone(fields);
          const clocks = Object.entries(info.verbs[verb].fields).filter(([, type]) => type === 'hlc');
          if (Object.keys(data).some(key => clocks.some(([field]) => field === key.toLowerCase()))) return { ok: false, reason: 'Clock fields are host-owned' };
          if (clocks.length && nextClock) {
            const stamp = nextClock();
            for (const [field] of clocks) data[field] = stamp;
          }
          return await broker.applyIntent(thread, name, verb, data, signal);
        } catch (error) { return { ok: false, reason: String(error?.message ?? error) }; }
        finally { pending--; }
      };
    },
    /** The document body the sandbox host wraps in its policy. */
    body: () => external ? customBody(spec.view) : componentBody({ view: spec.view, verbs: info.verbs, state: info.state }),
  });
  verifiedPresentations.set(verified, contractText);
  return verified;
}

/** Bind presentation to the exact verified contract; does not execute it. */
export async function defineView({ contract, view, ...rest }) {
  record(rest, [], ['layout', 'resources', 'capabilities']);
  const dialectText = dialectOf(contract);
  if (typeof view === 'function') view = { render: view.toString() };
  await ready();
  const serialized = JSON.stringify({ version: VIEW_VERSION, kind: 'view', contract: dialectHash(dialectText), view, ...rest });
  return presentation(recognizeView(serialized), dialectText, contract.serialized);
}

/** Import exact view bytes for a dialect. */
export async function importView(text, contract) {
  return presentation(viewRecord(text), dialectOf(contract), contract.serialized);
}

/**
 * A bundle: one record carrying a contract and a view bound to it, so a
 * person pastes one file. The two artifacts inside are unchanged: the
 * contract still compiles to a dialect that carries no presentation, and
 * the view still binds by that dialect's self-address.
 */
export const MAX_BUNDLE_BYTES = MAX_CONTRACT_BYTES + MAX_VIEW_BYTES + 256;
export function exportBundle(presentation, contract) {
  const contractText = contract === undefined ? verifiedPresentations.get(presentation) : contract.serialized;
  require(typeof contractText === 'string', 'exportBundle needs the cbcl/object contract for a view bound only to dialect text; use exportBundle(presentation, contract)');
  const record = viewRecord(presentation.serialized);
  require(compileContract(contractText).name === record.contract, 'view contract digest mismatch');
  return JSON.stringify({ version: VIEW_VERSION, kind: 'bundle', contract: JSON.parse(contractText), view: record });
}
export function recognizeBundle(text) {
  require(typeof text === 'string' && bytes(text) <= MAX_BUNDLE_BYTES, 'bundle exceeds 80 KiB');
  const bundle = JSON.parse(text);
  record(bundle, ['version', 'kind', 'contract', 'view']);
  require(bundle.version === VIEW_VERSION && bundle.kind === 'bundle', 'invalid bundle record');
  return bundle;
}
/** Import a bundle: the contract compiles first, then the view binds to it. */
export async function importBundle(text) {
  const bundle = recognizeBundle(text);
  const object = await importObject(JSON.stringify(bundle.contract));
  const presentation = await importView(JSON.stringify(bundle.view), object);
  return Object.freeze({ object, presentation });
}

/** The read-only presentation of a dialect, for a host with no view. */
export async function defaultPresentation(contract) {
  const dialectText = dialectOf(contract);
  await ready();
  const info = readDialect(dialectText);
  return presentation({ version: VIEW_VERSION, kind: 'view', contract: dialectHash(dialectText), ...defaultView(info) }, dialectText, contract.serialized);
}

// ---------------------------------------------------------------------------
// Declarative components: trusted renderer, author data as text only.
// ---------------------------------------------------------------------------

const COMPONENT_STYLES = `
:root{color-scheme:light;--paper:#fcfbf7;--ink:#28382f;--muted:#68736b;--line:#dce1d8;--accent:#365e44}
*{box-sizing:border-box}body{margin:0;padding:24px;background:var(--paper);color:var(--ink);font:14px/1.55 system-ui,-apple-system,sans-serif}
#object-root{display:grid;gap:22px;max-width:720px;margin:auto}section{min-width:0}h3{font-size:20px;line-height:1.3;letter-spacing:-.4px;margin:0;font-weight:650}
.value-label{display:block;color:var(--muted);font-size:11px;font-weight:650;letter-spacing:.09em;text-transform:uppercase;margin-bottom:8px}
.value-body{overflow-wrap:anywhere;white-space:pre-wrap}.value-body>.scalar{font-size:18px;line-height:1.45;font-weight:550}.empty{color:var(--muted);font-size:13px;font-style:italic}
.state-list{list-style:none;padding:0;margin:0;border:1px solid var(--line);border-radius:10px;overflow:hidden}.state-row{padding:10px 12px;display:flex;align-items:baseline;justify-content:space-between;gap:16px}.state-row+.state-row{border-top:1px solid var(--line)}.state-key{min-width:0;overflow-wrap:anywhere}.state-value{min-width:0;text-align:right}.state-row.done .state-key{text-decoration:line-through;color:var(--muted)}
.bool{display:inline-flex;align-items:center;justify-content:center;border:1px solid var(--line);border-radius:50%;width:21px;height:21px;font-size:13px;flex:none;color:var(--muted)}.bool.yes{background:#e5eee2;border-color:#b8cdb4;color:var(--accent)}
form{display:grid;gap:14px;padding-top:20px;border-top:1px solid var(--line)}label{display:grid;gap:6px;font-size:12px;font-weight:600;color:var(--muted)}input{width:100%;min-width:0;min-height:42px;padding:9px 11px;border:1px solid #c5cec2;border-radius:8px;background:#fff;color:var(--ink);font:inherit;line-height:1.4}input:hover{border-color:#97ab96}input:focus-visible,button:focus-visible{outline:2px solid var(--accent);outline-offset:3px}label.checkbox{display:flex;align-items:center;gap:9px;color:var(--ink);min-height:32px}.item-toggle{width:100%;cursor:pointer;font-size:14px;font-weight:400}.item-toggle input{flex:none}input[type=checkbox]{width:18px;height:18px;min-height:0;margin:0;accent-color:var(--accent)}button{justify-self:start;min-height:42px;padding:10px 18px;border:1px solid var(--accent);border-radius:8px;background:var(--accent);color:#fff;font:600 13px/1.4 system-ui;cursor:pointer}button:hover{background:#294a35}button:active{transform:translateY(1px)}
button.item-remove{flex:none;min-height:32px;padding:4px 10px;background:none;border-color:var(--line);color:var(--muted);font-weight:500}button.item-remove:hover{background:#f0f2ec;color:var(--ink)}
@media(max-width:400px){body{padding:18px}#object-root{gap:18px}button{width:100%;min-height:44px}button.item-remove{width:auto;min-height:36px}.state-row{gap:10px}}
`;

/** The renderer is trusted code. Author data is never inserted as HTML/code. */
function renderComponents(spec) {
  const root = document.getElementById('object-root');
  let currentState = {};
  // An editable boolean map is unambiguous only when its rule and an
  // explicitly offered form identify the same two-field action.
  const checklists = new Map();
  for (const component of spec.view) {
    if (component.type !== 'value') continue;
    // cbcl-rs v0.2.0: a keyed register is `lwwMap verb key value clock [delete]`.
    const [op, verb, key, flag, , drop] = spec.state[component.field] || [];
    const fields = spec.verbs[verb]?.fields;
    const own = Object.keys(fields || {}).filter(name => fields[name] !== 'hlc');
    if (op === 'lwwMap' && fields?.[key] === 'string' && fields?.[flag] === 'bool'
        && own.length === 2 && spec.view.some(c => c.type === 'form' && c.verb === verb)) {
      // Offering the delete verb's form turns it into a Remove button per item.
      const remove = drop !== undefined && spec.view.some(c => c.type === 'form' && c.verb === drop) ? drop : null;
      checklists.set(component.field, { verb, key, flag, remove, field: component.field });
    }
  }
  const removals = new Set([...checklists.values()].map(c => c.remove).filter(Boolean));
  for (const component of spec.view) {
    if (component.type === 'form' && removals.has(component.verb)) continue;
    const section = document.createElement('section'); root.appendChild(section);
    if (component.type === 'text') { const h = document.createElement('h3'); h.textContent = component.text; section.appendChild(h); }
    else if (component.type === 'value') {
      const label = document.createElement('strong'); label.textContent = component.label; label.className = 'value-label';
      const value = document.createElement('div'); value.className = 'value-body'; value.dataset.field = component.field;
      section.append(label, value);
    } else {
      const form = document.createElement('form'), inputs = {};
      const checklist = [...checklists.values()].find(c => c.verb === component.verb);
      for (const [name, text] of Object.entries(component.fields)) {
        if (checklist && name === checklist.flag) continue;
        const label = document.createElement('label'); label.textContent = text;
        const input = document.createElement('input'); input.name = name;
        const type = spec.verbs[component.verb].fields[name];
        const numeric = type === 'number' || type === 'integer';
        input.type = numeric ? 'number' : type === 'bool' ? 'checkbox' : 'text';
        if (numeric) { input.step = '1'; input.min = '-1000000000000'; input.max = '1000000000000'; }
        else if (type === 'string') input.maxLength = 2048;
        if (type === 'bool') { label.className = 'checkbox'; label.prepend(input); } else label.appendChild(input);
        input.required = type !== 'bool'; form.appendChild(label); inputs[name] = input;
      }
      const button = document.createElement('button'); button.textContent = checklist ? 'Add item' : component.label; button.type = 'button'; form.appendChild(button);
      const submit = event => {
        event.preventDefault(); if (!form.reportValidity()) return; const kw = {};
        for (const [name, input] of Object.entries(inputs)) kw[name] = input.type === 'checkbox' ? input.checked : input.type === 'number' ? Number(input.value) : input.value;
        if (checklist) {
          const items = currentState[checklist.field];
          kw[checklist.flag] = items && Object.hasOwn(items, kw[checklist.key]) ? items[kw[checklist.key]] : false;
        }
        window.emit(component.verb, kw);
      };
      button.addEventListener('click', submit);
      form.addEventListener('keydown', event => { if (event.key === 'Enter') submit(event); });
      section.appendChild(form);
    }
  }
  function display(value, depth = 0, checklist = null) {
    const node = document.createElement('span');
    if (value == null) { node.className = 'empty'; node.textContent = 'Nothing yet'; }
    else if (typeof value === 'boolean') {
      node.className = 'bool' + (value ? ' yes' : ''); node.textContent = value ? '✓' : '−';
      node.setAttribute('role', 'img'); node.setAttribute('aria-label', value ? 'Yes' : 'No');
    } else if (typeof value === 'object' && depth < 4) {
      const entries = Object.entries(value);
      if (!entries.length) { node.className = 'empty'; node.textContent = 'Nothing yet'; return node; }
      const list = document.createElement('ul'); list.className = 'state-list';
      for (const [key, item] of entries) {
        const row = document.createElement('li'); row.className = 'state-row' + (item === true ? ' done' : '');
        if (!Array.isArray(value)) { const label = document.createElement('span'); label.className = 'state-key'; label.textContent = key; row.append(label); }
        if (checklist && typeof item === 'boolean') {
          const label = document.createElement('label'); label.className = 'checkbox item-toggle';
          const input = document.createElement('input'); input.type = 'checkbox'; input.checked = item;
          input.setAttribute('aria-label', key);
          input.addEventListener('change', () => {
            window.emit(checklist.verb, { [checklist.key]: key, [checklist.flag]: input.checked });
            input.checked = item; // the accepted fold owns the visible state
          });
          label.append(input, row.firstChild); row.append(label);
          if (checklist.remove) {
            const remove = document.createElement('button'); remove.type = 'button'; remove.className = 'item-remove';
            remove.textContent = 'Remove'; remove.setAttribute('aria-label', 'Remove ' + key);
            remove.addEventListener('click', () => window.emit(checklist.remove, { [checklist.key]: key }));
            row.append(remove);
          }
        } else {
          const content = display(item, depth + 1); content.classList.add('state-value'); row.append(content);
        }
        list.append(row);
      }
      return list;
    } else { node.className = 'scalar'; node.textContent = typeof value === 'object' ? JSON.stringify(value) : String(value); }
    return node;
  }
  window.onProjection = state => {
    currentState = state;
    for (const node of root.querySelectorAll('[data-field]')) {
      const value = state[node.dataset.field];
      node.replaceChildren(display(value, 0, checklists.get(node.dataset.field)));
    }
  };
}

/** The document body of a declarative view. `spec` is {view, verbs, state}. */
export function componentBody(spec) {
  const data = { view: spec.view, verbs: Object.fromEntries(Object.entries(spec.verbs).map(([v, r]) => [v, { fields: r.fields }])), state: spec.state };
  return '<style>' + COMPONENT_STYLES + '</style><div id="object-root"></div><script>('
    + renderComponents.toString() + ')(' + JSON.stringify(data).replace(/</g, '\\u003c') + ');</script>';
}

// ---------------------------------------------------------------------------
// Custom views: interpreted author code; external capabilities require grants.
// ---------------------------------------------------------------------------

/** Runs only inside the confined interpreter. Escaped interpolations are text;
 *  event functions are attached through generated markers, never attributes. */
export function html(strings, ...values) { return { strings: Array.from(strings), values }; }
function customRuntime(render) {
  const root = document.getElementById('object-root');
  window.onProjection = state => {
    const handlers = [];
    const escape = value => String(value).replace(/[&<>"']/g, ch => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[ch]));
    function markup(value) {
      if (Array.isArray(value)) return value.map(markup).join('');
      if (value && Array.isArray(value.strings) && Array.isArray(value.values)) {
        return value.strings.reduce((out, part, i) => out + part + (i < value.values.length ? markup(value.values[i]) : ''), '');
      }
      if (typeof value === 'function') { const id = handlers.push(value) - 1; return '"object-handler-' + id + '"'; }
      return value == null ? '' : escape(value);
    }
    try {
      root.innerHTML = markup(render(state, { emit: window.emit, request: window.request, invoke: window.invoke }));
      for (const node of root.querySelectorAll('*')) for (const attr of Array.from(node.attributes)) {
        if (!attr.name.startsWith('data-cbcl-on')) continue;
        const match = /^object-handler-(\d+)$/.exec(attr.value);
        if (match) { node.removeAttribute(attr.name); node.addEventListener(attr.name.slice('data-cbcl-on'.length), handlers[Number(match[1])]); }
      }
    } catch (error) { root.textContent = 'View error: ' + error.message; }
  };
}
export function customBody(view) {
  if (Object.hasOwn(view, 'html')) return view.html;
  // Protect script end tags in author string literals at the HTML boundary.
  const source = '(' + view.render.replace(/<\/script/gi, '<\\/script') + ')';
  return '<div id="object-root"></div><script>const html=' + html.toString()
    + ';(' + customRuntime.toString() + ')(' + source + ');</script>';
}

export { createRequestBroker } from './request-broker.js';
export { loadViewResources } from './resource-loader.js';
import { mountView as mountVerified } from './mount.ts';
export { bindProjection } from './mount.ts';
export { defineOperation } from './operations.ts';

export async function mountView(presentation, options) {
  if (!verifiedPresentations.has(presentation)) throw Error('Mount requires an SDK-verified presentation');
  return mountVerified(presentation, options);
}

export const CONFINED_VIEW_CSP = "default-src 'none'; script-src 'none'; style-src 'unsafe-inline'; img-src data:; media-src blob:; connect-src 'none'; frame-src 'none'; object-src 'none'; worker-src 'none'; form-action 'none'; base-uri 'none'";
export { generateViewTypes } from './typegen.ts';
