// Builders emit the same type-expression strings accepted by the JSON contract.
import { literal } from './compile.ts';
import type { ExactScalar } from '../read.ts';

type NumericLiteral = number | bigint | { integer: string } | { decimal: string } | { float: number };
type Bounds<T> = { gt?: T; gte?: T; lt?: T; lte?: T };
type Comparison<T> = readonly ['>' | '>=' | '<' | '<=', T];
type Length = readonly ['length', Comparison<number | bigint>, ...Comparison<number | bigint>[]];
type StringClause = Length | readonly ['matches', string];

function orderedLength([, ...bounds]: Length): string {
  return form('length', bounds.map(([op, n]) => form(op, [literal(n)])));
}

function form(head: string, args: string[]): string {
  return args.length ? '(' + [head, ...args].join(' ') + ')' : head;
}

function comparisons(bounds: Bounds<NumericLiteral>): string[] {
  const operators = { gt: '>', gte: '>=', lt: '<', lte: '<=' } as const;
  const result: string[] = [];
  for (const key of ['gt', 'gte', 'lt', 'lte'] as const) {
    const value = bounds[key];
    if (value !== undefined) result.push(form(operators[key], [literal(value)]));
  }
  return result;
}

function lengthRule(bounds?: Bounds<number | bigint>): string[] {
  const rules = comparisons(bounds ?? {});
  return rules.length ? [form('length', rules)] : [];
}

function ordered<T>(rules: object | readonly T[]): rules is readonly T[] {
  return Array.isArray(rules);
}

function numericType(head: string, rules: NumericRules): string {
  if (ordered<Comparison<NumericLiteral>>(rules)) return form(head, rules.map(([op, n]) => form(op, [literal(n)])));
  return form(head, comparisons(rules));
}

type NumericRules = Bounds<NumericLiteral> | readonly Comparison<NumericLiteral>[];
type StringRules = { matches?: string; length?: Bounds<number | bigint> };
type ListRules = { length?: Bounds<number | bigint> };

/** JavaScript authoring expressions for CBCL flat contracts. */
export const t = Object.freeze({
  decimal: (rules: NumericRules = {}) => numericType('decimal', rules),
  float: (rules: NumericRules = {}) => numericType('float', rules),
  integer: (rules: NumericRules = {}) => numericType('integer', rules),
  number: (rules: NumericRules = {}) => numericType('number', rules),
  string: (rules: StringRules | readonly StringClause[] = {}) => {
    if (ordered<StringClause>(rules)) return form('string', rules.map(rule =>
      rule[0] === 'length' ? orderedLength(rule) : form('matches', [literal(rule[1])])));
    const parts = lengthRule(rules.length);
    if (rules.matches !== undefined) parts.push(form('matches', [literal(rules.matches)]));
    return form('string', parts);
  },
  list: (rules: ListRules | readonly Length[] = {}) => form('list',
    ordered<Length>(rules) ? rules.map(orderedLength) : lengthRule(rules.length)),
  oneOf: (first: ExactScalar | bigint, ...rest: (ExactScalar | bigint)[]) => form('one-of', [first, ...rest].map(literal)),
  and: (first: string, second: string, ...rest: string[]) => form('and', [first, second, ...rest]),
  or: (first: string, second: string, ...rest: string[]) => form('or', [first, second, ...rest]),
});
