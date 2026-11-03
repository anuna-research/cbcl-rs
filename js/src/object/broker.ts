// The intent broker: the ONE accept path every intent crosses (a sandboxed
// view's port and an agent's `act`). A view supplies ONLY {verb, fields};
// anything else it asserts about routing, identity, or bookkeeping is a
// forge and is refused. The binding itself is cbcl-rs's `intend` (SPEC-019
// R.5): it admits the verb for the signer, binds recipients, `:thread`,
// `:caused-by` and `:replaces` from the accepted set, builds the keyword-form
// act and verifies it. The broker adds only what a host owns: identity,
// signing, transport, and the optimistic union into the store.
import { CORE_PERFORMATIVES, ROUTING_KEYWORDS } from './compile.ts';
import { actRecord, type Runtime } from './runtime.ts';
import type { ThreadStore } from './store.ts';
import type { Plain } from '../read.ts';

export { CORE_PERFORMATIVES };

export interface BrokerHost {
  /** The authenticated signer handle. */
  me(): string;
  /** The dialect's runtime, or null when unknown to this host. */
  getRuntime(dialect: string): Runtime | null;
  store: ThreadStore;
  /** Canonicalise text (optional; the act cbcl-rs returns is already canonical). */
  canonicalize?(text: string): string;
  /** The text to sign, e.g. with an account proof appended (optional). */
  prepare?(canonical: string): Promise<string> | string;
  /** Sign and deliver. Return false to refuse. */
  send(text: string): Promise<boolean | void> | boolean | void;
  /** Re-fold and push to the view (optional). */
  onState?(thread: string): void;
  /** Wire-tap hook (optional). */
  report?(info: Record<string, unknown>): void;
}

export type IntentResult = { ok: true; cid: string; canonical: string } | { ok: false; reason: string };

export interface Broker {
  applyIntent(thread: string, dialect: string, verb: string, fields?: Record<string, unknown>): Promise<IntentResult>;
}

export function makeBroker(host: BrokerHost): Broker {
  async function runIntent(thread: string, dialectName: string, verb: string, rawKw: unknown): Promise<IntentResult> {
    const report = (info: Record<string, unknown>) => { host.report?.(info); };
    const reject = (reason: string, label?: string): IntentResult => {
      report({ ok: false, thread, dialect: dialectName, verb: label || verb, reason });
      return { ok: false, reason };
    };
    const runtime = host.getRuntime(dialectName);
    if (!runtime) return reject(`unknown dialect ${dialectName}`);
    if (CORE_PERFORMATIVES.has(verb)) return reject(`'${verb}' is a core performative — never view-causable`);
    if (!rawKw || typeof rawKw !== 'object' || Array.isArray(rawKw)) return reject('intent keywords must be a record');
    const kw: Record<string, Plain> = Object.create(null);
    const from = host.me();
    for (const [k, v] of Object.entries(rawKw as Record<string, unknown>)) {
      const key = String(k).toLowerCase();
      if (ROUTING_KEYWORDS.has(key)) {
        // A binding the view merely echoes is stripped; anything else it
        // asserts about routing, identity, or bookkeeping is a forge.
        if (key === 'from' && v === from) continue;
        if (key === 'thread' && v === thread) continue;
        if (key === 'dialect' && v === dialectName) continue;
        if (key === 'from') return reject(`view tried to set :from ${String(v)} — client binds :from ${from}`, `spoof ${verb}`);
        if (key === 'replaces') return reject('view tried to set :replaces — client binds replacements', `forge ${verb}`);
        return reject(`view tried to set :${key} — client binds routing`, `forge ${verb}`);
      }
      kw[k] = v as Plain;
    }
    const messages = host.store.messages(thread);
    let bound;
    try { bound = runtime.intend(thread, messages, from, verb, kw); }
    catch (error) { return reject(String((error as Error)?.message ?? error), `shape-violation ${verb}`); }
    if (!bound.ok) return reject(`${bound.reject}: ${bound.reason}`, `${bound.reject} ${verb}`);
    let text = host.canonicalize ? host.canonicalize(bound.canonical) : bound.canonical;
    if (host.prepare) text = await host.prepare(text);
    if (host.me() !== from) return reject('identity changed before send');
    const sent = await host.send(text);
    if (sent === false) return reject('wire send blocked');
    // Optimistic union: the hub fans the signed copy back; the store's dedup
    // by address makes that a no-op. State re-folds.
    const record = actRecord(text, from);
    host.store.append(record);
    host.onState?.(thread);
    report({ ok: true, thread, dialect: dialectName, verb, cid: record.cid, causedBy: record.causedBy, from, kw: record.kw });
    return { ok: true, cid: record.cid, canonical: text };
  }

  // Binding and signing yield. Serialise per thread so a rapid second act
  // sees the first in the accepted set (its :replaces names it).
  const queues = new Map<string, Promise<IntentResult>>();
  function applyIntent(thread: string, dialectName: string, verb: string, rawKw: Record<string, unknown> = {}): Promise<IntentResult> {
    const previous: Promise<unknown> = queues.get(thread) || Promise.resolve();
    const next = previous.then(() => runIntent(thread, dialectName, verb, rawKw)).catch((error: unknown) => {
      const result: IntentResult = { ok: false, reason: (error as Error)?.message || String(error) };
      host.report?.({ ...result, thread, dialect: dialectName, verb });
      return result;
    });
    queues.set(thread, next);
    void next.then(() => { if (queues.get(thread) === next) queues.delete(thread); });
    return next;
  }
  return { applyIntent };
}
