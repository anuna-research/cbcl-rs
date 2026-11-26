// SPEC-019 R.7 in the SDK: one dialect's runtime over a thread's messages.
//
// Every judgement is cbcl-rs's: which messages are accepted (`admit`, R.4 +
// R5 + R6 against the accepted set), what state they fold to (`fold`, R7),
// and what act an intent becomes (`intend`, R.5). This module keeps no
// semantics of its own: it turns the store's messages into the
// `(acts (<signer> <message>) …)` frame, retries pending admissions as the
// accepted set grows. Only a verified extension of the same store snapshot can
// reuse prior verdicts. Independent histories are always judged in full.
import { resourceCheck, type ResourceOutcome, admitAct, foldState, intendAct, maySend, frontierOf, stateSchema, readAct, installDialect, type InstalledDialect, describeDialect, type State, type IntendResult, type Admission, type DialectInfo } from '../verifier.ts';
import type { Plain } from '../read.ts';
import { literal, keywordText } from './compile.ts';
import { snapshotOrigins, type Msg } from './store.ts';

export { readAct };

/** A store record from an act's wire text and its authenticated signer. */
export function actRecord(canonical: string, signer: string): Msg {
  const act = readAct(canonical);
  return { cid: act.address, verb: act.verb, signer, thread: act.thread ?? '', causedBy: act.causedBy, kw: act.fields, canonical: String(canonical) };
}

/** A message the runtime can judge: at least its address, signer and text. */
export type ActEntry = Pick<Msg, 'cid' | 'signer' | 'canonical'> & Partial<Msg>;

function dedupe<T extends ActEntry>(messages: T[]): T[] {
  const seen = new Map<string, T>();
  for (const m of messages) if (m && m.cid && !seen.has(m.cid)) seen.set(m.cid, m);
  return [...seen.values()];
}

export type VerdictName = 'accepted' | 'pending' | 'rejected';

export interface Runtime {
  readonly text: string;
  readonly info: DialectInfo;
  schema(): ReturnType<typeof stateSchema>;
  admission(thread: string, messages: ActEntry[], options?: { fresh?: boolean }): { accepted: ActEntry[]; pending: ActEntry[] };
  accepted(thread: string, messages: ActEntry[], options?: { fresh?: boolean }): ActEntry[];
  admit(thread: string, messages: ActEntry[], message: ActEntry): Admission;
  verdicts(thread: string, messages: ActEntry[], options?: { fresh?: boolean }): Map<string, VerdictName>;
  read(thread: string, messages: ActEntry[], options?: { fresh?: boolean }): State;
  resourceCheck(thread: string, messages: ActEntry[], candidate: ActEntry): ResourceOutcome;
  intend(thread: string, messages: ActEntry[], signer: string, verb: string, fields?: Record<string, Plain>): IntendResult;
  maySend(thread: string, messages: ActEntry[], signer: string): string[];
  frontier(thread: string, messages: ActEntry[]): { instance: string | null; frontier: string[] };
}

/** Build a dialect's runtime from its `(define …)` text. The verifier must be initialised. */
export function createRuntime(dialectText: string | InstalledDialect): Runtime {
  const source = installDialect(dialectText).dialect;
  const info = describeDialect(source);
  type Cache = { thread: string; prefix: [string, string, string][]; decided: Map<string, VerdictName> };
  const histories = new WeakMap<object, Cache>();
  let schema: ReturnType<typeof stateSchema> | null = null;
  const entry = (m: ActEntry) => `(${literal(String(m.signer))} ${m.canonical})`;
  const actsFrame = (list: ActEntry[]) => `(acts ${list.map(entry).join(' ')})`;
  const instance = (thread: string, accepted: ActEntry[]) => `${source} ${literal(String(thread))} ${actsFrame(accepted)}`;

  function admitOne(thread: string, accepted: ActEntry[], message: ActEntry): Admission {
    return admitAct(`(admit ${instance(thread, accepted)} (${literal(String(message.signer))} ${message.canonical}))`);
  }

  function admission(thread: string, messages: ActEntry[], { fresh = false } = {}) {
    const unique = dedupe(messages);
    const origin = fresh ? undefined : snapshotOrigins.get(messages as Msg[]);
    let cache = origin && histories.get(origin);
    if (origin && (!cache || cache.thread !== thread || cache.prefix.length > unique.length ||
        !cache.prefix.every(([cid, signer, canonical], i) =>
          unique[i].cid === cid && unique[i].signer === signer && unique[i].canonical === canonical))) {
      cache = { thread, prefix: [], decided: new Map() };
      histories.set(origin, cache);
    }
    if (cache) for (const m of unique.slice(cache.prefix.length)) cache.prefix.push([m.cid, m.signer, m.canonical]);
    const accepted: ActEntry[] = [], pending: ActEntry[] = [];
    for (const m of unique) {
      const known = cache?.decided.get(m.cid);
      if (known === 'accepted') accepted.push(m);
      else if (known !== 'rejected') pending.push(m);
    }
    let progressed = true;
    while (progressed && pending.length) {
      progressed = false;
      for (const m of pending.slice()) {
        const { verdict } = admitOne(thread, accepted, m);
        if (verdict === 'pending') continue;
        pending.splice(pending.indexOf(m), 1);
        progressed = true;
        if (verdict === 'accepted') accepted.push(m);
        cache?.decided.set(m.cid, verdict);
      }
    }
    return { accepted, pending };
  }

  return Object.freeze({
    text: source, info,
    schema() { return schema ??= stateSchema(`(state-schema ${source})`); },
    admission,
    accepted: (thread, messages, options) => admission(thread, messages, options).accepted,
    admit: (thread, messages, message) => admitOne(thread, admission(thread, messages).accepted, message),
    verdicts(thread, messages, options) {
      const { accepted, pending } = admission(thread, messages, options);
      const out = new Map<string, VerdictName>();
      for (const m of dedupe(messages)) out.set(m.cid, accepted.includes(m) ? 'accepted' : pending.includes(m) ? 'pending' : 'rejected');
      return out;
    },
    read: (thread, messages, options) => foldState(`(fold ${instance(thread, admission(thread, messages, options).accepted)})`),
    resourceCheck: (thread, messages, candidate) => resourceCheck(`(resource-check ${instance(thread, admission(thread, messages).accepted)} ${entry(candidate)})`),
    intend: (thread, messages, signer, verb, fields) =>
      intendAct(`(intend ${instance(thread, admission(thread, messages).accepted)} ${literal(String(signer))} ${verb} (${keywordText(fields || {})}))`),
    maySend: (thread, messages, signer) => maySend(`(may-send ${instance(thread, admission(thread, messages).accepted)} ${literal(String(signer))})`),
    frontier: (thread, messages) => frontierOf(`(frontier ${instance(thread, admission(thread, messages).accepted)})`),
  } satisfies Runtime);
}
