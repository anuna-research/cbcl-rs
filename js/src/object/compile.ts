// SPEC-087: the JSON authoring contract. The compile itself is cbcl-rs's
// (`compileContract`); this module holds the authoring sugar, the types, the
// literal writer for the opener and the intent frame, and the reader that
// turns a dialect's text back into what a host or a view needs to know.
import { compileContract, describeDialect, type DialectInfo, type Rule } from '../verifier.ts';
import type { Plain } from '../read.ts';

export type { DialectInfo, Rule };

export const CONTRACT_VERSION = 3;
export const MAX_CONTRACT_BYTES = 16384;

/** A dialect named by its self-address (SPEC-019 R.6). */
export const isSDKDialect = (name: unknown): name is string => /^sha256-[0-9a-f]{64}$/.test(String(name));

/** The core control performatives a view may never cause, plus `lang`. */
export const CORE_PERFORMATIVES: ReadonlySet<string> = new Set(['tell', 'ask', 'reply', 'error', 'ok', 'cancel', 'hello', 'bye', 'lang']);
/** Keywords the binder owns: never a contract field, never set by a view. */
export const ROUTING_KEYWORDS: ReadonlySet<string> = new Set(['from', 'thread', 'dialect', 'caused-by', 'to', 'sender', 'replaces', 'audience', 'sig', 'key', 'signing-key']);

export type FieldType = 'string' | 'number' | 'bool' | 'list';
export type FieldSpec = FieldType | { enumOf: string };
export type RuleOp = 'last' | 'latestPerSigner' | 'latestPerKey' | 'exists' | 'count' | 'events' | 'setUnion'
  | 'values' | 'valuesPerKey' | 'registerPerKey' | 'observedSet' | 'counter' | 'histogram' | 'sum';

export interface VerbSpec { after: string[]; fields: Record<string, FieldSpec>; from?: string; to?: string[] }

/** The wire contract record (SPEC-087 CON-001). */
export interface Contract {
  version: 3;
  kind: 'contract';
  name: string;
  author?: string;
  requirements?: { maxDepth?: number; maxExpansionSize?: number; verificationTime?: number };
  bounds?: { maxString?: number; maxList?: number; maxNumber?: number; maxFields?: number };
  roles?: Record<string, 'singleton' | 'indexed'>;
  verbs: Record<string, VerbSpec>;
  state: Record<string, Rule>;
}

/** Authoring sugar: `c.last('open', 'title')` is `['last', 'open', 'title']`. */
export const c = Object.freeze({
  last: (verb: string, field: string): Rule => ['last', verb, field],
  latestPerSigner: (verb: string, field: string): Rule => ['latestPerSigner', verb, field],
  latestPerKey: (verb: string, key: string, field: string): Rule => ['latestPerKey', verb, key, field],
  exists: (verb: string): Rule => ['exists', verb],
  count: (verb: string): Rule => ['count', verb],
  events: (verb: string, field: string): Rule => ['events', verb, field],
  setUnion: (verb: string, field: string): Rule => ['setUnion', verb, field],
  values: (verb: string, field: string): Rule => ['values', verb, field],
  valuesPerKey: (verb: string, key: string, field: string, deleteVerb?: string): Rule =>
    ['valuesPerKey', verb, key, field, ...(deleteVerb === undefined ? [] : [deleteVerb])],
  registerPerKey: (verb: string, key: string, field: string, deleteVerb?: string): Rule =>
    ['registerPerKey', verb, key, field, ...(deleteVerb === undefined ? [] : [deleteVerb])],
  observedSet: (addVerb: string, removeVerb: string, field: string): Rule => ['observedSet', addVerb, removeVerb, field],
  counter: (incVerb: string, decVerb: string, field: string): Rule => ['counter', incVerb, decVerb, field],
  histogram: (stateField: string): Rule => ['histogram', stateField],
  sum: (stateField: string): Rule => ['sum', stateField],
});

/** A field whose value must be an element of the opener-drawn list in state field `field`. */
export const enumOf = (field: string): { enumOf: string } => ({ enumOf: field });

/** A plain JS value as a CBCL literal: strings quoted, integers, booleans, lists of those. */
export function literal(value: Plain): string {
  if (typeof value === 'string') return '"' + value.replace(/\\/g, '\\\\').replace(/"/g, '\\"').replace(/\n/g, '\\n') + '"';
  if (typeof value === 'number') { if (!Number.isInteger(value)) throw new Error('state-bearing numbers are integers'); return String(value); }
  if (typeof value === 'boolean') return value ? '#t' : '#f';
  if (Array.isArray(value)) return '(' + value.map(literal).join(' ') + ')';
  throw new Error('unsupported field value');
}

/** `:k v …` for a keyword record, in the record's key order. */
export function keywordText(kw: Record<string, Plain> | undefined): string {
  return Object.entries(kw || {}).map(([k, v]) => `:${k} ${literal(v)}`).join(' ');
}

const token = (value: string): string => /^[^\s()"\\;]+$/.test(value) ? value : literal(value);

/** The opener as the wire carries it: keyword form, every field declared. */
export function openerText(o: { dialect: string; verb: string; room: string | string[]; thread: string; from: string; fields?: Record<string, Plain>; causedBy?: string }): string {
  const recipient = Array.isArray(o.room) ? `(${o.room.map(token).join(' ')})` : token(o.room);
  const kw = Object.entries(o.fields || {}).map(([k, v]) => ` :${k} ${literal(v)}`).join('');
  const causedBy = o.causedBy === undefined || o.causedBy === 'begin' ? 'begin' : token(o.causedBy);
  return `(lang ${o.dialect} (${o.verb} ${recipient}${kw} :caused-by ${causedBy} :thread ${literal(String(o.thread))} :from ${token(o.from)}))`;
}

/** What a host or a view needs to know about a dialect: cbcl-rs's description of it. */
export const readDialect = describeDialect;

/** Compile contract text with cbcl-rs and read the result back. */
export function compile(contractText: string): { contract: Contract; contractText: string; name: string; label: string; dialect: string; info: DialectInfo } {
  const contract = JSON.parse(contractText) as Contract;
  const { name, label, dialect } = compileContract(contractText);
  return { contract, contractText, name, label, dialect, info: readDialect(dialect) };
}
