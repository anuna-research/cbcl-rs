import { makeHlc, readAct } from '../verifier.ts';
import type { Plain } from '../read.ts';
import type { Runtime, ActEntry } from './runtime.ts';

export interface HostClock { next(received?: string): string }

/** Use one issuer per signer and retain each stamp before releasing it. */
export function createHostClock({ now = Date.now, load, save }: {
  now?: () => number | bigint;
  load?: () => string | null;
  save?: (stamp: string) => void;
} = {}): HostClock {
  let previous = load?.() ?? undefined;
  return {
    next(received) {
      const stamp = makeHlc({ previous, received, nowMs: now() });
      save?.(stamp);
      previous = stamp;
      return stamp;
    },
  };
}

export function stampHostClock(clock: HostClock, runtime: Runtime, thread: string, messages: ActEntry[],
  verb: string, fields: Record<string, Plain>): void {
  const clockFields = (name: string) => Object.entries(runtime.info.verbs[name]?.fields ?? {})
    .filter(([, type]) => type === 'hlc').map(([key]) => key);
  const names = clockFields(verb);
  if (!names.length) return;
  let received: string | undefined;
  for (const record of runtime.accepted(thread, messages)) {
    const act = readAct(record.canonical);
    for (const key of clockFields(act.verb)) {
      const value = act.fields[key];
      // Canonical HLCs have fixed-width hexadecimal components in clock order.
      if (typeof value === 'string' && (!received || value > received)) received = value;
    }
  }
  const stamp = clock.next(received);
  for (const name of names) fields[name] = stamp;
}
