// The CBCL verifier for JavaScript: typed wrappers over the cbcl-rs wasm
// build. Every judgement a host needs is made here by cbcl-rs and never
// re-derived in JavaScript: parsing, dialect well-formedness (R1–R7), message
// and state shape, the causal protocol, admission, the fold, the intent
// binder, a dialect's self-address, and the JSON contract compile (SPEC-087).
//
// The wasm must be initialised once before any call: `await ready()` in a
// browser or in node. Under node, importing this module initialises it
// synchronously from the bytes beside it, so scripts and tests need no
// ceremony; a browser awaits `ready()` (or its own `init` of the same module,
// which is idempotent) before its first frame.
import init, {
  initSync, parse as wasmParse, parse_message, message_hash, verify_dialect, verify_message_shape,
  verify_protocol, fold, intend, verify_state_shape, state_schema, may_send, frontier, dialect_hash,
  admit, read as wasmRead, compile_contract, define_text, describe_dialect, read_act,
} from './cbcl_wasm.js';

let loaded = false;
let pending: Promise<void> | undefined;

const underNode = typeof process !== 'undefined' && !!process.versions?.node && typeof window === 'undefined';
if (underNode) {
  const { readFileSync } = await import('node:fs');
  initSync({ module: readFileSync(new URL('./cbcl_wasm_bg.wasm', import.meta.url)) });
  loaded = true;
}

/** Initialise the verifier (idempotent). Resolves when every export may be called. */
export function ready(): Promise<void> {
  if (loaded) return Promise.resolve();
  pending ??= init({ module_or_path: new URL('./cbcl_wasm_bg.wasm', import.meta.url) }).then(() => { loaded = true; });
  return pending;
}

/** Whether the verifier is initialised. */
export function isReady(): boolean { return loaded; }

function guard(): void {
  if (!loaded) throw new Error('CBCL verifier is not initialised; await ready() first.');
}

// The wasm reports a refusal by throwing its reason (a blame S-expression, a
// JSON rejection, or plain text).
function reason(error: unknown): string { return String((error as Error)?.message ?? error); }
function outcome(call: () => string): { ok: true; result: string } | { ok: false; result: string } {
  try { return { ok: true, result: call() }; } catch (error) { return { ok: false, result: reason(error) }; }
}
// The wasm throws a bare string; callers get an Error whose message is the reason.
function refusal<T>(call: () => T): T {
  guard();
  try { return call(); } catch (error) { throw new Error(reason(error)); }
}

/** An S-expression tree as the parser reads it: lists as arrays, quoted strings as `{str}`, other atoms as their text. */
export type Tree = string | { str: string } | Tree[];

/** The parser's tree of one S-expression (comments allowed). Throws on a parse error. */
export function read(text: string): Tree { return refusal(() => JSON.parse(wasmRead(text)) as Tree); }

/** An S-expression's canonical serialisation. */
export function parse(text: string): string { return refusal(() => wasmParse(text)); }

/** A message's canonical form. Throws with the parser's reason. */
export function parseMessage(text: string): string { return refusal(() => parse_message(text)); }

/** CBCL's canonical content address of a message (`sha256:<hex>`). */
export function messageHash(message: string): string { return refusal(() => message_hash(message)); }

/** The same digest as the wire spells it in `:caused-by` and `:replaces` (`sha256-<hex>`). */
export function wireAddress(message: string): string { return messageHash(message).replace(/^sha256:/, 'sha256-'); }

/** A dialect's self-address `sha256-<hex>` (SPEC-019 R.6): the hash of its body, name excluded. */
export function dialectHash(define: string): string { return refusal(() => dialect_hash(define)); }

/** Install a dialect through R1–R7; throws with cbcl-rs's reason when it is refused. */
export function verifyDialect(define: string): void {
  guard();
  const result = verify_dialect(define);
  if (result !== 'ok') throw new Error(`CBCL dialect verification failed: ${result}`);
}

export type Verdict = { ok: true } | { ok: false; reason: string };

/** A message against a dialect's `(shape …)` clauses for a performative (R5). */
export function verifyShape(dialect: string, verb: string, message: string): Verdict {
  guard();
  const { ok, result } = outcome(() => verify_message_shape(`(verify-shape ${dialect} ${verb} ${message})`));
  return ok && result === 'ok' ? { ok: true } : { ok: false, reason: result };
}

/** A state-bearing act against its dialect's state shape (SPEC-019 R.4). */
export function verifyStateShape(dialect: string, message: string): Verdict {
  guard();
  const { ok, result } = outcome(() => verify_state_shape(`(verify-state-shape ${dialect} ${message})`));
  return ok && result === 'ok' ? { ok: true } : { ok: false, reason: result };
}

export type CausalVerdict = 'Valid' | 'Unknown' | 'Violation';

/**
 * A message's `:caused-by` against its dialect's `(protocol …)`. `history` is
 * `[address, message]` for the predecessors it names.
 */
export function verifyProtocol(dialect: string, thread: string, message: string, history: [string, string][] = []): CausalVerdict {
  guard();
  // History is keyed by the canonical `sha256:` hash, quoted: the lexer reads a bare colon as a keyword.
  const entries = history.map(([hash, text]) => `(${JSON.stringify(hash)} ${text})`).join(' ');
  const frame = `(verify-protocol ${dialect} ${JSON.stringify(thread)} ${message}${entries ? ` (history ${entries})` : ''})`;
  const { ok, result } = outcome(() => verify_protocol(frame));
  if (ok && result === 'ok') return 'Valid';
  if (result.startsWith('(pending')) return 'Unknown';
  return 'Violation';
}

/** A state value as the fold renders it (SPEC-019 R.3). */
export type StateValue = null | string | number | boolean | StateValue[] | { [key: string]: StateValue };
export type State = Record<string, StateValue>;

/** `(fold <dialect> <thread> (acts …))` → the state. */
export function foldState(frame: string): State { return refusal(() => JSON.parse(fold(frame)) as State); }

export type IntendResult = { ok: true; canonical: string } | { ok: false; reject: string; reason: string };

/** `(intend …)` → the canonical act to sign, or the binder's rejection (SPEC-019 R.5). */
export function intendAct(frame: string): IntendResult {
  guard();
  const { ok, result } = outcome(() => intend(frame));
  if (ok) return { ok: true, canonical: result };
  try {
    const r = JSON.parse(result) as { reject?: string; reason?: string };
    if (r && r.reject) return { ok: false, reject: r.reject, reason: r.reason ?? '' };
  } catch { /* not a JSON rejection */ }
  return { ok: false, reject: 'error', reason: result };
}

export type Admission = { verdict: 'accepted' } | { verdict: 'pending' } | { verdict: 'rejected'; reason: string };

/** `(admit <dialect> <thread> (acts …) (<signer> <message>))` → the consumer's admission of one message. */
export function admitAct(frame: string): Admission {
  guard();
  const { ok, result } = outcome(() => admit(frame));
  if (!ok) return { verdict: 'rejected', reason: result };
  return JSON.parse(result) as Admission;
}

/** `(state-schema <dialect>)` → each state field's type. */
export function stateSchema(frame: string): Record<string, { type: string; [k: string]: unknown }> {
  guard();
  return JSON.parse(state_schema(frame));
}

/** `(may-send <dialect> <thread> (acts …) <signer>)` → the verbs the signer may emit now. */
export function maySend(frame: string): string[] { return refusal(() => JSON.parse(may_send(frame)) as string[]); }

/** `(frontier <dialect> <thread> (acts …))` → the accepted opener's address and the frontier. */
export function frontierOf(frame: string): { instance: string | null; frontier: string[] } {
  guard();
  return JSON.parse(frontier(frame));
}

export interface CompiledContract { name: string; label: string; dialect: string }

/** The canonical `(define …)` a dialect text, `(meta (define …))`, or teach frame carries. Throws when there is none. */
export function defineText(input: string): string { return refusal(() => define_text(input)); }

/** A rule of the state clause as JSON spells it: `[op, arg…]`. */
export type Rule = [string, ...string[]];

/** What a host or a view needs to know about a dialect, read from cbcl-rs's installed structures. */
export interface DialectInfo {
  name: string;
  author: string | null;
  opener: string | null;
  verbs: Record<string, { params: string[]; fields: Record<string, string>; after: string[]; from?: string; to?: string[] }>;
  roles: Record<string, 'singleton' | 'indexed'>;
  state: Record<string, Rule>;
  domains: { verb: string; key: string; field: string }[];
  bounds: Record<string, number>;
  /** The canonical `(define …)` text. */
  text: string;
}

/** A dialect text, `(meta (define …))`, or teach frame → its description. Throws with the parser's reason. */
export function describeDialect(input: string): DialectInfo { return refusal(() => JSON.parse(describe_dialect(input)) as DialectInfo); }

/** A field value as an act carries it. */
export type FieldValue = string | number | boolean | FieldValue[];

/** An act as the parser and the state layer read it. */
export interface ActInfo {
  dialect: string | null;
  /** The wire address `sha256-<hex>`. */
  address: string;
  verb: string;
  recipients: string[];
  /** Data fields; routing keywords excluded. */
  fields: Record<string, FieldValue>;
  thread: string | null;
  from: string | null;
  causedBy: 'begin' | string | string[];
}

/** An act's wire text → its dialect, address, verb, recipients, fields, and routing. Throws with the parser's reason. */
export function readAct(text: string): ActInfo { return refusal(() => JSON.parse(read_act(text)) as ActInfo); }

/** SPEC-087: a JSON contract → its dialect, named by self-address and installed through R1–R7. Throws with the reason. */
export function compileContract(json: string): CompiledContract {
  return refusal(() => JSON.parse(compile_contract(json)) as CompiledContract);
}
