// Reading frames: the parser's tree and the small helpers a host needs to
// look inside one. Nothing here parses; `read` is cbcl-rs's parser (SPEC-013
// REQ-018: one reader, so a security check and a renderer cannot disagree
// about what a frame says).
import { read, type Tree } from './verifier.ts';

export type { Tree };

/** The tree of one S-expression, or null when the parser refuses it. */
export function parseSexpr(text: string): Tree | null {
  try { return read(String(text)); } catch { return null; }
}

/** Keyword arguments of a list: `{name: value}` for each `:name value` pair. */
export function kwargs(list: Tree | null): Record<string, Tree> {
  const out: Record<string, Tree> = {};
  if (!Array.isArray(list)) return out;
  for (let i = 0; i < list.length; i++) {
    const t = list[i];
    if (typeof t === 'string' && t.startsWith(':') && i + 1 < list.length) { out[t.slice(1)] = list[i + 1]; i++; }
  }
  return out;
}

/** The text of an atom: a quoted string's content, a symbol as itself, anything else as JSON. */
export function asText(v: Tree | undefined): string | undefined {
  if (v === undefined) return undefined;
  if (typeof v === 'object' && !Array.isArray(v) && 'str' in v) return v.str;
  return typeof v === 'string' ? v : JSON.stringify(v);
}

/** A plain field value: quoted strings unwrap, `#t`/`#f` are booleans, integer text is a number, lists map. */
export type Plain = string | number | boolean | Plain[];
export function readValue(v: Tree): Plain {
  if (typeof v === 'object' && !Array.isArray(v) && 'str' in v) return v.str;
  if (Array.isArray(v)) return v.map(readValue);
  if (v === '#t') return true;
  if (v === '#f') return false;
  if (/^-?\d+$/.test(v)) return parseInt(v, 10);
  return v;
}
