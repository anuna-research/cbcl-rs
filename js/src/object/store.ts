// The per-thread message store: a G-Set keyed by content address, mirroring
// cbcl-rs `ThreadedMessageStore`. Merge is set union with dedup by address;
// `:caused-by` links form the causal DAG. State is not stored here; it is
// the fold over the accepted acts, recomputed on demand. Addresses are the
// wire spelling `sha256-<hex>` (SPEC-019 R.6). Pure data, order-independent.
import type { FieldValue } from '../verifier.ts';

/** A stored act: its wire address, verb, authenticated signer, thread, predecessors, display fields, and full text. */
export interface Msg {
  cid: string;
  verb: string;
  signer: string;
  thread: string;
  causedBy: 'begin' | string | string[];
  kw: Record<string, FieldValue>;
  canonical: string;
}

export class ThreadStore {
  private threadsMap = new Map<string, Map<string, Msg>>();

  private thread(thread: string): Map<string, Msg> {
    let t = this.threadsMap.get(thread);
    if (!t) { t = new Map(); this.threadsMap.set(thread, t); }
    return t;
  }

  /** Union a message into its thread. True iff newly inserted: a re-delivery is the same act (SPEC-019 REQ-1920). */
  append(msg: Msg): boolean {
    if (!msg || !msg.cid || !msg.thread) return false;
    const t = this.thread(msg.thread);
    if (t.has(msg.cid)) return false;
    t.set(msg.cid, msg);
    return true;
  }

  contains(thread: string, cid: string): boolean { return !!this.threadsMap.get(thread)?.has(cid); }

  get(thread: string, cid: string): Msg | null { return this.threadsMap.get(thread)?.get(cid) ?? null; }

  /** All messages in a thread (insertion order; consumers must not rely on it). */
  messages(thread: string): Msg[] { const t = this.threadsMap.get(thread); return t ? [...t.values()] : []; }

  threads(): string[] { return [...this.threadsMap.keys()]; }

  /** G-set join: union another store's elements into this one. Idempotent and commutative. */
  merge(other: ThreadStore): this {
    for (const thread of other.threads()) for (const m of other.messages(thread)) this.append(m);
    return this;
  }

  /** The frontier: addresses no message's `:caused-by` names (the causal leaves). */
  frontier(thread: string): string[] {
    const msgs = this.messages(thread);
    const referenced = new Set<string>();
    for (const m of msgs) for (const cb of normaliseCausedBy(m.causedBy)) referenced.add(cb);
    return msgs.map(m => m.cid).filter(cid => !referenced.has(cid));
  }

  /** Causal closure (principal ideal): the target and its transitive predecessors present here. */
  causalClosure(thread: string, target: string): string[] {
    const t = this.threadsMap.get(thread);
    if (!t || !t.has(target)) return [];
    const out: string[] = [], seen = new Set<string>(), stack = [target];
    while (stack.length) {
      const cid = stack.pop()!;
      if (seen.has(cid)) continue;
      seen.add(cid);
      const m = t.get(cid);
      if (!m) continue;
      out.push(cid);
      for (const cb of normaliseCausedBy(m.causedBy)) if (!seen.has(cb)) stack.push(cb);
    }
    return out;
  }
}

/** A `:caused-by` value as an array of predecessor addresses (`begin` → []). */
export function normaliseCausedBy(causedBy: Msg['causedBy'] | null | undefined): string[] {
  if (causedBy === 'begin' || causedBy == null) return [];
  const hashes = Array.isArray(causedBy) ? causedBy : [causedBy];
  return hashes.filter(h => h && h !== 'begin').map(String);
}
