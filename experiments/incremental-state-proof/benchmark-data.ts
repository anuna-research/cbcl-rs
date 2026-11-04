import assert from 'node:assert/strict';
import { native } from './helpers.js';
export const PROFILES = ['control', 'status', 'telemetry'] as const;
export type Profile = typeof PROFILES[number];
/** Deterministic representative simulations, never labelled production logs. */
export function workload(profile: Profile, length: number) {
  assert.ok(PROFILES.includes(profile));
  assert.ok(Number.isInteger(length) && length >= 0 && length <= 4096);
  const writers = profile === 'control' ? 4 : profile === 'status' ? 32 : 16;
  let random = 0x13579bdf;
  const records = Array.from({ length }, (_, i) => {
    random ^= random << 13; random ^= random >>> 17; random ^= random << 5;
    const seq = Math.floor(i / writers);
    const value = profile === 'control' ? i * 19 + 3 : profile === 'status' ? seq % 3 : 20_000 + ((random >>> 0) % 15_000);
    return { signer: i % writers, seq, value, replaces: i < writers ? null : '$head' };
  });
  return { oracle: native(records), records, writers };
}
