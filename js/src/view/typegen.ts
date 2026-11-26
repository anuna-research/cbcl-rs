// Emit declarations from the same installed metadata used by projection and intent binding.
import { describeDialect, installDialect, read, ready, stateSchema, type DialectInfo, type StateFieldSchema, type Tree } from '../verifier.ts';
import { CORE_PERFORMATIVES, ROUTING_KEYWORDS } from '../object/compile.ts';

const inputTypes = new Map(Object.entries({
  integer: 'number | bigint | { integer: string }', float: 'number | { float: number }',
  decimal: '{ decimal: string }', string: 'string', bool: 'boolean',
  symbol: '{ symbol: string }', keyword: '{ keyword: string }', list: 'Plain[]',
}));

function literalType(value: Tree): string | undefined {
  if (Array.isArray(value)) return undefined;
  if (typeof value === 'object') return JSON.stringify(value.str);
  if (value === '#t' || value === '#f') return value === '#t' ? 'true' : 'false';
  if (value.startsWith(':')) return '{ keyword: ' + JSON.stringify(value.slice(1)) + ' }';
  // Numeric literals have multiple valid JS encodings. Keep their representation type.
  if (/^[+.-]?\d/.test(value)) return undefined;
  return '{ symbol: ' + JSON.stringify(value) + ' }';
}

function fieldType(field: { source: string; representations: string[] }, info: DialectInfo): string {
  const fallback = [...new Set(field.representations.map(rep => inputTypes.get(rep) ?? 'Plain'))].join(' | ') || 'Plain';
  function expression(tree: Tree): string {
    const head = Array.isArray(tree) ? tree[0] : tree;
    if (typeof head !== 'string') return fallback;
    if (typeof tree === 'string' && Object.hasOwn(info.types, tree)) return 'DialectTypes[' + JSON.stringify(tree) + ']';
    if (Array.isArray(tree) && (head === 'and' || head === 'or')) {
      return '(' + tree.slice(1).map(part => '(' + expression(part) + ')').join(head === 'and' ? ' & ' : ' | ') + ')';
    }
    if (Array.isArray(tree) && head === 'one-of') {
      return tree.slice(1).map(value => literalType(value) ?? fallback).join(' | ');
    }
    return inputTypes.get(head) ?? fallback;
  }
  return field.source ? expression(read(field.source)) : fallback;
}

const projectedScalars = new Map(Object.entries({
  integer: 'number', float: 'number', decimal: '{ decimal: string }',
  number: 'number | { decimal: string }', hlc: 'string', string: 'string', bool: 'boolean', list: 'StateValue[]',
}));

function stateType(schema: StateFieldSchema, scalarHint?: string): string {
  const scalar = scalarHint ?? projectedScalars.get(schema.of ?? '') ?? 'StateValue';
  if (schema.freeze) {
    const value = stateType({ ...schema, freeze: undefined }, scalarHint);
    return value + ' | { frozen: string; superseded: string[]; value: ' + value + ' } | Fault';
  }
  switch (schema.type) {
    case 'bool': return 'boolean';
    case 'int': return 'number';
    case 'opt-scalar': return scalar + ' | null';
    case 'set': return 'Array<' + scalar + '>';
    case 'map': return 'Record<string, ' + (schema.value ? stateType(schema.value, scalarHint) : 'StateValue') + '>';
    case 'events': return 'Record<string, { by: string; value: ' + scalar + ' }>';
    case 'histogram': return 'Record<string, number>';
    case 'threshold': return '{ status: "pending" } | { status: "reached"; element: StateValue } | Fault';
    case 'bounded-counter': return '{ status: "ready"; value: number; rights: Record<string, number>; headroom?: Record<string, number> } | { status: "pending"; evidence: string[] } | Fault';
    case 'object': return '{ ' + Object.entries(schema.fields ?? {}).map(([k, v]) => JSON.stringify(k) + ': ' + stateType(v)).join('; ') + ' }';
    default: return 'StateValue';
  }
}

/** Generate a type-only TypeScript module from an SDK contract or CBCL dialect source. */
export async function generateViewTypes(contract: string | { dialect: string }): Promise<string> {
  await ready();
  const info = describeDialect(installDialect(contract).dialect);
  const schema = Object.keys(info.state).length || info.thresholds.length ? stateSchema('(state-schema ' + info.text + ')') : {};
  const state = Object.entries(schema).map(([key, value]) => {
    const [head, verb, field, third] = info.state[key] ?? [];
    const sourceKey = head === 'lwwMap' || head === 'valuesPerKey' || head === 'observedSet' ? third : field;
    const source = typeof verb === 'string' && typeof sourceKey === 'string' ? info.verbs[verb]?.contracts?.[sourceKey] : undefined;
    const representations = source?.representations.map(rep =>
      rep === 'keyword' || rep === 'symbol' ? 'string' : projectedScalars.get(rep) ?? 'StateValue');
    const hint = source ? [...new Set(representations)].join(' | ') || 'StateValue' : undefined;
    let type = stateType(value, hint);
    // A missing thread context can be absent, and a lift may display its element name.
    if (head === 'context') type += ' | null';
    if (head === 'lift') type += ' | string';
    if (head === 'initial' || head === 'context' || head === 'lift' || info.domains.length ||
        ((head === 'histogram' || head === 'sum') && info.freezes.length)) type += ' | Fault';
    return '  ' + JSON.stringify(key) + ': ' + type + ';';
  });
  const fields: string[] = [], calls: string[] = [];
  for (const [verb, spec] of Object.entries(info.verbs)) {
    if (verb === info.opener || CORE_PERFORMATIVES.has(verb)) continue;
    const visible = Object.entries(spec.contracts).filter(([key]) => !ROUTING_KEYWORDS.has(key) && spec.fields[key] !== 'hlc');
    const props = visible.map(([key, field]) => JSON.stringify(key) + (field.required ? ': ' : '?: ') + fieldType(field, info));
    const name = JSON.stringify(verb);
    fields.push('  ' + name + ': ' + (props.length ? '{ ' + props.join('; ') + ' }' : 'Record<string, never>') + ';');
    const optional = visible.some(([, f]) => f.required) ? '' : '?';
    calls.push('[verb: ' + name + ', fields' + optional + ': IntentFields[' + name + ']]');
  }
  const aliases = Object.entries(info.types).map(([name, field]) => '  ' + JSON.stringify(name) + ': ' + fieldType(field, info) + ';');
  const declarations = [
    'export type DialectTypes = {', ...aliases, '};', '',
    'export type ViewState = {', ...state, '};', '',
    'export type IntentFields = {', ...fields, '};', '',
    'export type EmitArgs = ' + (calls.join('\n  | ') || 'never') + ';',
    'export type ViewHost = Omit<RenderHost, "emit"> & { emit(...args: EmitArgs): void };',
    'export type Render = (state: ViewState, host: ViewHost) => unknown;', '',
  ].join('\n');
  const imports = ['Plain', 'StateValue'].filter(name => new RegExp('\\b' + name + '\\b').test(declarations));
  return [
    '// Generated by cbcl/view. Regenerate when the dialect changes.',
    ...(imports.length ? ['import type { ' + imports.join(', ') + ' } from "cbcl";'] : []),
    'import type { RenderHost } from "cbcl/view";', '',
    ...(declarations.includes(' | Fault') ? ['type Fault = { status: "fault"; reason: string; evidence: string[] };', ''] : []),
    declarations,
  ].join('\n');
}
