// SPEC-019 R.7 in the SDK: one dialect's runtime over a thread's messages.
//
// Every judgement is cbcl-rs's: which messages are accepted (`admit`, R.4 +
// R5 + R6 against the accepted set), what state they fold to (`fold`, R7),
// and what act an intent becomes (`intend`, R.5). This module keeps no
// semantics of its own: it turns the store's messages into the
// `(acts (<signer> <message>) …)` frame, retries pending admissions as the
// accepted set grows, and remembers verdicts that cannot change (the store
// only grows, so an accepted act stays accepted and a rejected one rejected).
import { admitAct, foldState, intendAct, maySend, frontierOf, stateSchema, readAct, describeDialect, type State, type IntendResult, type Admission, type DialectInfo } from '../verifier.ts';
import type { Plain } from '../read.ts';
import { literal, keywordText } from './compile.ts';
import type { Msg } from './store.ts';

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
  intend(thread: string, messages: ActEntry[], signer: string, verb: string, fields?: Record<string, Plain>): IntendResult;
  maySend(thread: string, messages: ActEntry[], signer: string): string[];
  frontier(thread: string, messages: ActEntry[]): { instance: string | null; frontier: string[] };
}

/** Build a dialect's runtime from its `(define …)` text. The verifier must be initialised. */
export function createRuntime(dialectText: string): Runtime {
  const source = String(dialectText);
  const info = describeDialect(source);
  const decided = new Map<string, 'accepted' | 'rejected'>();
  let schema: ReturnType<typeof stateSchema> | null = null;
  const entry = (m: ActEntry) => `(${literal(String(m.signer))} ${m.canonical})`;
  const actsFrame = (list: ActEntry[]) => `(acts ${list.map(entry).join(' ')})`;
  const instance = (thread: string, accepted: ActEntry[]) => `${source} ${literal(String(thread))} ${actsFrame(accepted)}`;

  function admitOne(thread: string, accepted: ActEntry[], message: ActEntry): Admission {
    return admitAct(`(admit ${instance(thread, accepted)} (${literal(String(message.signer))} ${message.canonical}))`);
  }

  function admission(thread: string, messages: ActEntry[], { fresh = false } = {}) {
    const unique = dedupe(messages);
    const accepted: ActEntry[] = [], pending: ActEntry[] = [];
    for (const m of unique) {
      const known = fresh ? undefined : decided.get(m.cid);
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
        if (!fresh) decided.set(m.cid, verdict);
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
    intend: (thread, messages, signer, verb, fields) =>
      intendAct(`(intend ${instance(thread, admission(thread, messages).accepted)} ${literal(String(signer))} ${verb} (${keywordText(fields || {})}))`),
    maySend: (thread, messages, signer) => maySend(`(may-send ${instance(thread, admission(thread, messages).accepted)} ${literal(String(signer))})`),
    frontier: (thread, messages) => frontierOf(`(frontier ${instance(thread, admission(thread, messages).accepted)})`),
  } satisfies Runtime);
}
