// `cbcl/object` — SPEC-087: data-only authoring of a state-bearing dialect,
// and the runtime an agent or a browser runs it with.
//
// An agent writes a JSON contract (verbs, fields, state rules); cbcl-rs
// compiles it to one CBCL dialect carrying the `(state …)` clause (SPEC-019),
// named by its self-address `sha256-<body hash>`, installed through R1–R7,
// and folds it with `fold`. Presentation is a separate concern of the host.
import { ready, verifyShape, verifyStateShape, type State } from '../verifier.ts';
import { compile, openerText, c, enumOf, isSDKDialect, readDialect, literal, keywordText, CONTRACT_VERSION, MAX_CONTRACT_BYTES, CORE_PERFORMATIVES, ROUTING_KEYWORDS, type Contract, type DialectInfo, type Rule, type VerbSpec, type FieldSpec } from './compile.ts';
import { createRuntime, readAct, actRecord, type Runtime, type ActEntry, type VerdictName } from './runtime.ts';
import type { ActInfo } from '../verifier.ts';
import { makeBroker, type BrokerHost, type IntentResult } from './broker.ts';
import { ThreadStore, normaliseCausedBy, type Msg } from './store.ts';
import type { Plain } from '../read.ts';

export { c, enumOf, isSDKDialect, openerText, readDialect, literal, keywordText, createRuntime, readAct, actRecord, makeBroker, ThreadStore, normaliseCausedBy, CONTRACT_VERSION, MAX_CONTRACT_BYTES, CORE_PERFORMATIVES, ROUTING_KEYWORDS };
export type { Contract, DialectInfo, Rule, VerbSpec, FieldSpec, Runtime, ActEntry, VerdictName, BrokerHost, IntentResult, Msg, Plain, ActInfo };

function require(condition: unknown, message: string): asserts condition { if (!condition) throw new Error(`Object contract: ${message}`); }

export interface OpenerArgs { room: string | string[]; thread: string; from: string; fields?: Record<string, Plain>; causedBy?: string }

export interface AgentHost extends Omit<BrokerHost, 'getRuntime'> {}

export interface Agent {
  read(thread: string): State;
  maySend(thread: string): string[];
  act(thread: string, verb: string, fields?: Record<string, unknown>): Promise<IntentResult>;
}

/** An imported object: its dialect, and the fold, opener and agent over it. */
export interface CbclObject {
  /** The dialect's self-address. */
  readonly name: string;
  /** The contract's label; no part of identity. */
  readonly label: string;
  /** The `(define …)` text every host installs and the room declares. */
  readonly dialect: string;
  /** The exact contract bytes. */
  readonly contract: string;
  readonly serialized: string;
  readonly info: DialectInfo;
  readonly runtime: Runtime;
  /** The fold over a thread's records; order-independent. */
  read(messages: ActEntry[], thread?: string): State;
  /** Which of a thread's records are accepted, pending, or rejected. */
  verdicts(messages: ActEntry[], thread?: string): Map<string, VerdictName>;
  /** The opener, keyword form, verified by cbcl-rs before it is returned. */
  open(args: OpenerArgs): string;
  /** A broker over a host's store and transport. */
  agent(host: AgentHost): Agent;
}

/** Import exact contract bytes: compile with cbcl-rs (R1–R7) and build the object. */
export async function importObject(serialized: string): Promise<CbclObject> {
  await ready();
  const { contractText, name, label, dialect, info } = compile(serialized);
  const runtime = createRuntime(dialect);
  return Object.freeze({
    name, label, dialect, contract: contractText, serialized: contractText, info, runtime,
    read: (messages, thread = messages[0]?.thread ?? 't') => runtime.read(thread, messages),
    verdicts: (messages, thread = messages[0]?.thread ?? 't') => runtime.verdicts(thread, messages),
    open({ room, thread, from, fields, causedBy }) {
      require(info.opener, 'the dialect declares no opener');
      const declared = Object.keys(info.verbs[info.opener].fields);
      const given = Object.keys(fields || {});
      require(given.every(f => declared.includes(f)) && declared.every(f => given.includes(f)), `opener fields are exactly ${declared.join(', ')}`);
      const text = openerText({ dialect: name, verb: info.opener, room, thread, from, fields, causedBy });
      const shape = verifyShape(dialect, info.opener, text.replace(/^\(lang \S+ /, '').replace(/\)$/, ''));
      require(shape.ok, `invalid opener fields: ${shape.ok ? '' : shape.reason}`);
      const state = verifyStateShape(dialect, text);
      require(state.ok, `invalid opener fields: ${state.ok ? '' : state.reason}`);
      return text;
    },
    agent(host) {
      const broker = makeBroker({ ...host, getRuntime: key => key === name ? runtime : null });
      return {
        read: thread => runtime.read(thread, host.store.messages(thread)),
        maySend: thread => runtime.maySend(thread, host.store.messages(thread), host.me()),
        act: (thread, verb, fields) => broker.applyIntent(thread, name, verb, fields),
      };
    },
  } satisfies CbclObject);
}

/** Authoring input: the contract record with sugar (`dialect` for `name`, `causedBy` for `after`, `['string']` for `list`, `project` for `state`). */
export interface Definition {
  name?: string; dialect?: string; version?: number; author?: string;
  requirements?: Contract['requirements']; bounds?: Contract['bounds']; roles?: Contract['roles'];
  verbs: Record<string, { after?: string[]; causedBy?: string | string[]; fields?: Record<string, FieldSpec | string | ['string']>; from?: string; to?: string[] }>;
  state?: Record<string, Rule>; project?: Record<string, Rule>;
  [key: string]: unknown;
}

function normalizeAuthoring(definition: Definition): Record<string, unknown> {
  const normalized: Record<string, unknown> = { ...definition };
  if (Object.hasOwn(normalized, 'dialect')) { normalized.name = normalized.dialect; delete normalized.dialect; }
  if (Object.hasOwn(normalized, 'project')) { normalized.state = normalized.project; delete normalized.project; }
  normalized.version ??= CONTRACT_VERSION;
  normalized.verbs = Object.fromEntries(Object.entries(definition.verbs || {}).map(([verb, rule]) => {
    const next: Record<string, unknown> = { ...rule };
    if (Object.hasOwn(next, 'causedBy')) { next.after = Array.isArray(rule.causedBy) ? rule.causedBy : [rule.causedBy]; delete next.causedBy; }
    next.fields = Object.fromEntries(Object.entries(rule.fields || {}).map(([key, value]) => [key, Array.isArray(value) && value.length === 1 && value[0] === 'string' ? 'list' : value]));
    return [verb, next];
  }));
  return normalized;
}

/** Author a contract. Presentation is deliberately absent: a view is the host's concern. */
export async function defineContract(definition: Definition): Promise<CbclObject> {
  const normalized = normalizeAuthoring(definition);
  for (const key of ['view', 'layout', 'resources']) require(!Object.hasOwn(normalized, key), `a contract carries no presentation (${key}); views are a host package`);
  require(normalized.version === CONTRACT_VERSION, `contracts require version ${CONTRACT_VERSION}`);
  const { version, name, verbs, state, author, requirements, bounds, roles, ...unknown } = normalized;
  require(Object.keys(unknown).length === 0, `unknown contract field ${Object.keys(unknown)[0]}`);
  const contract = { version, kind: 'contract', name, ...(author !== undefined ? { author } : {}), ...(requirements !== undefined ? { requirements } : {}), ...(bounds !== undefined ? { bounds } : {}), ...(roles !== undefined ? { roles } : {}), verbs, state };
  return importObject(JSON.stringify(contract));
}

/** `defineObject` names the contract-only form. */
export const defineObject = defineContract;
