#!/usr/bin/env node
// Independent AST -> I-Regexp / ECMAScript renderers. Never imports Rust output.
// SPEC-040 TEST-4003: small finite cross-engine corpus; not an RFC completeness proof.
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import assert from 'node:assert/strict';
const destination = fileURLToPath(new URL('../test-vectors/contracts/iregexp/reference-cases.json', import.meta.url));
const lit = text => ({ kind: 'literal', text });
const dot = { kind: 'dot' };
const range = (lo, hi, negated = false) => ({ kind: 'range', lo, hi, negated });
const property = (name, negated = false) => ({ kind: 'property', name, negated });
const seq = (...children) => ({ kind: 'sequence', children });
const alt = (...children) => ({ kind: 'alternative', children });
const repeat = (child, suffix) => ({ kind: 'repeat', child, suffix });
const scalar = c => `\\u{${c.codePointAt(0).toString(16)}}`;
function iregexp(ast) {
  switch (ast.kind) {
    case 'literal': return [...ast.text].map(c => '\\() *+-.?[]{}|'.replaceAll(' ', '').includes(c) ? `\\${c}` : c).join('');
    case 'dot': return '.';
    case 'range': return `[${ast.negated ? '^' : ''}${ast.lo}-${ast.hi}]`;
    case 'property': return `\\${ast.negated ? 'P' : 'p'}{${ast.name}}`;
    case 'class': return `[${ast.negated ? '^' : ''}${ast.children.map(iregexp).join('')}]`;
    case 'sequence': return ast.children.map(child => `(${iregexp(child)})`).join('');
    case 'alternative': return `(${ast.children.map(iregexp).join('|')})`;
    case 'repeat': return `(${iregexp(ast.child)})${ast.suffix}`;
    default: throw Error('unknown AST');
  }
}
function ecma(ast) {
  switch (ast.kind) {
    case 'literal': return [...ast.text].map(scalar).join('');
    case 'dot': return '[^\\n\\r]';
    case 'range': return `[${ast.negated ? '^' : ''}${scalar(ast.lo)}-${scalar(ast.hi)}]`;
    case 'property': return `\\${ast.negated ? 'P' : 'p'}{General_Category=${ast.name}}`;
    case 'class': return `[${ast.negated ? '^' : ''}${ast.children.map(ecma).join('')}]`;
    case 'sequence': return ast.children.map(child => `(?:${ecma(child)})`).join('');
    case 'alternative': return `(?:${ast.children.map(ecma).join('|')})`;
    case 'repeat': return `(?:${ecma(ast.child)})${ast.suffix}`;
    default: throw Error('unknown AST');
  }
}
// The negative lookahead requires the actual end, including after final newlines.
const engine = ast => new RegExp(`^(?:${ecma(ast)})(?![\\s\\S])`, 'u');
assert(engine(lit('^$')).test('^$'));
assert(!engine(lit('^$')).test(''));
assert(!engine(lit('a')).test('a\n'));
assert(engine(dot).test('\u2028'));
assert(!engine(dot).test('\r'));
assert(engine(dot).test('😀'));
assert(!engine(lit('é')).test('e\u0301'));
const core = [lit(''), lit('a'), lit('b'), dot, range('a','c'), range('0','9',true),
  lit('😀'), lit('^$'), lit('\n'), lit('a|b'), lit('\\'), lit('[a]')];
const categories = ['L','Ll','Lm','Lo','Lt','Lu','M','Mc','Me','Mn','N','Nd','Nl','No',
  'P','Pc','Pd','Pe','Pf','Pi','Po','Ps','Z','Zl','Zp','Zs','S','Sc','Sk','Sm','So','C','Cc','Cf','Cn','Co'];
const asts = [...core, ...categories.flatMap(c => [property(c),property(c,true)])];
for (const child of core) for (const suffix of ['*','+','?','{0}','{2}','{0,2}','{2,}']) asts.push(repeat(child,suffix));
for (const left of core.slice(0,9)) for (const right of core.slice(0,9)) asts.push(seq(left,right),alt(left,right));
asts.push({kind:'class',children:[property('Nd')],negated:false},
  {kind:'class',children:[property('Nd',true)],negated:false},
  {kind:'class',children:[property('Nd'),property('Ll')],negated:true},
  seq(lit('^ab'),repeat(dot,'*')),
  repeat(alt(lit('a'),lit('b')),'{1,3}'), repeat(repeat(lit('a'),'{1,2}'),'{2,3}'),
  seq(repeat(dot,'*'),lit('$')),alt(lit(''),seq(lit('a'),repeat(lit('b'),'+'))));
let words = [''];
let layer = [''];
for (let depth = 0; depth < 3; depth++) {
  layer = layer.flatMap(prefix => ['a','b','0','\n','\r','😀'].map(c => prefix+c));
  words.push(...layer);
}
// Fixed samples assigned before Unicode 17, plus an unassigned scalar remaining Cn.
// This does not certify the entire pinned Unicode 16 table against newer engines.
words.push('^abc','abc$','^ab.*','.*bc$','^$','a|b','\\','[a]','a\n','a\r','é','e\u0301','Ж','ж','١','\u2028','\u2029',
  '\0','\t','\u02b0','中','ǅ','\u0903','\u20dd','\u0301','Ⅷ','²','_','-','(',')','“','”','!',
  ' ','\u00a0','$','^','+','😀','\u0378','\u200d','\ue000','\u{f0000}');
words = [...new Set(words)];
const unique = new Map(asts.map(ast => [iregexp(ast),ast]));
const cases = [...unique].map(([pattern,ast]) => ({ pattern, matches: words.map(text => engine(ast).test(text) ? '1' : '0').join('') }));
const result = { profile: 'rfc9485-ast-reference-v1', samples: words, cases };
if (process.argv.includes('--write')) {
  writeFileSync(destination, JSON.stringify({ ...result, generated_by: { node: process.version, v8: process.versions.v8, unicode: process.versions.unicode } }, null, 2)+'\n');
} else {
  const golden = JSON.parse(readFileSync(destination, 'utf8'));
  delete golden.generated_by;
  assert.deepEqual(result,golden,'independent engine disagrees with committed reference vectors');
}
console.log(`${cases.length} patterns × ${words.length} samples = ${cases.length * words.length} independent ECMAScript expectations (${process.version}, Unicode ${process.versions.unicode})`);
