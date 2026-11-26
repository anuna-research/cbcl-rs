export type CapabilityData = null | boolean | number | string | CapabilityData[] | { [key: string]: CapabilityData };
export interface CapabilityScope {
  readonly contract: string;
  readonly view: string;
  readonly thread: string;
  readonly signal: AbortSignal;
  /** Register cleanup for this mount. Call the returned function to unregister. */
  onDispose(cleanup: () => void): () => void;
}
type Result = CapabilityData | Promise<CapabilityData>;
export type OperationHandler = (input: CapabilityData, scope: CapabilityScope) => Result;
export type InvokeOperation = (operation: string, input?: CapabilityData) => Result;
export interface OperationLimits {
  maxCalls?: number;
  maxConcurrent?: number;
  maxInputBytes?: number;
  maxResultBytes?: number;
}
export type OperationDeclaration = string | { id: string; limits?: OperationLimits };
export type OperationGrant = OperationHandler | { handle: OperationHandler; limits?: OperationLimits };

/** An entry in a host's typed operation catalog. Validation runs before the effect. */
export function defineOperation<T>(spec: {
  parse(input: CapabilityData): T;
  run(input: T, scope: CapabilityScope): Result;
  limits?: OperationLimits;
}): OperationGrant {
  const { parse, run, limits } = spec;
  return { limits, handle: (input, scope) => run(parse(input), scope) };
}

const defaults = { maxCalls: 1024, maxConcurrent: 8, maxInputBytes: 65536, maxResultBytes: 65536 };
export function validateLimits(value: OperationLimits) {
  if (!value || typeof value !== 'object' || Array.isArray(value) ||
      ![null, Object.prototype].includes(Object.getPrototypeOf(value))) throw Error('Invalid operation limits');
  for (const [key, limit] of Object.entries(value)) {
    if (!Object.hasOwn(defaults, key) || !Number.isSafeInteger(limit) || limit < 0) throw Error('Invalid operation limit: ' + key);
  }
}

// Count UTF-8 JSON bytes as we copy. Stop before expanding oversized or cyclic guest input.
function copyData(input: CapabilityData, remaining: number): CapabilityData {
  const ancestors = new Set<object>();
  const encoder = new TextEncoder();
  function charge(bytes: number) {
    remaining -= bytes;
    if (remaining < 0) throw Error('Capability data exceeds byte limit');
  }
  function scalar(value: string | number | boolean | null) {
    if (typeof value === 'string' && value.length > remaining) throw Error('Capability data exceeds byte limit');
    charge(encoder.encode(JSON.stringify(value)).length);
  }
  function visit(value: CapabilityData): CapabilityData {
    if (value === null || typeof value === 'string' || typeof value === 'boolean' ||
        (typeof value === 'number' && Number.isFinite(value))) { scalar(value); return value; }
    if (typeof value !== 'object' || ancestors.has(value) || ancestors.size >= 64) throw Error('Expected bounded JSON capability data');
    const array = Array.isArray(value);
    if (!array && ![null, Object.prototype].includes(Object.getPrototypeOf(value))) throw Error('Expected capability record');
    ancestors.add(value);
    charge(2);
    const copy: [string, CapabilityData][] = [];
    for (const key of Object.keys(value)) {
      const descriptor = Object.getOwnPropertyDescriptor(value, key)!;
      if (!('value' in descriptor)) throw Error('Expected capability data field');
      if (array && key !== String(copy.length)) throw Error('Expected dense capability array');
      if (copy.length) charge(1);
      if (!array) { scalar(key); charge(1); }
      copy.push([key, visit(descriptor.value)]);
    }
    ancestors.delete(value);
    if (array && copy.length !== value.length) throw Error('Expected dense capability array');
    return array ? copy.map(([, item]) => item) : Object.fromEntries(copy);
  }
  return visit(input);
}

export function bindOperations(declared: OperationDeclaration[], grants: Readonly<Record<string, OperationGrant>>,
  identity: Omit<CapabilityScope, 'onDispose'>): InvokeOperation {
  const { signal } = identity;
  const scope: CapabilityScope = Object.freeze({ ...identity,
    onDispose(cleanup: () => void) {
      if (signal.aborted) cleanup();
      else signal.addEventListener('abort', cleanup, { once: true });
      return () => signal.removeEventListener('abort', cleanup);
    },
  });
  const handlers = new Map<string, (input?: CapabilityData) => Result>();
  for (const [id, grant] of Object.entries(grants)) {
    const declaration = declared.find(entry => (typeof entry === 'string' ? entry : entry.id) === id);
    const handle = typeof grant === 'function' ? grant : grant?.handle;
    if (!declaration || typeof handle !== 'function') throw Error('Invalid capability grant: ' + id);
    const policy = typeof grant === 'function' ? undefined : grant.limits;
    if (policy !== undefined) validateLimits(policy);
    const requested = typeof declaration === 'string' ? undefined : declaration.limits;
    const limit = (key: keyof OperationLimits) => Math.min(policy?.[key] ?? defaults[key], requested?.[key] ?? Infinity);
    const inputBytes = limit('maxInputBytes'), resultBytes = limit('maxResultBytes'), concurrent = limit('maxConcurrent');
    let calls = limit('maxCalls'), pending = 0;
    function deliver(value: CapabilityData) {
      signal.throwIfAborted();
      return copyData(value, resultBytes);
    }
    handlers.set(id, (input = null) => {
      if (!calls || pending >= concurrent) throw Error('Capability call limit reached: ' + id);
      calls--;
      pending++;
      try {
        const result = handle(copyData(input, inputBytes), scope);
        if (result && typeof result === 'object' && 'then' in result && typeof result.then === 'function') {
          return Promise.resolve(result as Promise<CapabilityData>).then(deliver).finally(() => { pending--; });
        }
        const output = deliver(result as CapabilityData);
        pending--;
        return output;
      } catch (error) { pending--; throw error; }
    });
  }
  return (id, input) => {
    signal.throwIfAborted();
    const invoke = handlers.get(id);
    if (!invoke) throw Error('Capability denied: ' + id);
    return invoke(input);
  };
}
