import type { CbclObject, ThreadStore, IntentResult } from '../object/index.js';
import type { Broker } from '../object/broker.js';
import type { State } from '../verifier.js';
import type { Presentation, LoadedResources, Resources, RenderHost } from './index.js';
import { createRequestBroker } from './request-broker.js';
import { loadViewResources } from './resource-loader.js';
import { bindOperations } from './operations.ts';
import type { OperationGrant } from './operations.js';

export interface ViewPorts {
  emit(verb: string, fields?: Record<string, unknown>): Promise<IntentResult>;
  request: RenderHost['request'];
  invoke: RenderHost['invoke'];
}

export interface ViewExecution {
  project(state: State): void;
  dispose(): void;
}

/** Trusted adapter for a confined interpreter. Marshal data and calls across its guest boundary. */
export interface ViewExecutor {
  mount(input: { body: string; resources: LoadedResources; ports: ViewPorts; signal: AbortSignal }):
    ViewExecution | Promise<ViewExecution>;
}

export interface ViewGrants {
  requests?: string[];
  resources?: Resources;
  operations?: Readonly<Record<string, OperationGrant>>;
}
export interface MountOptions {
  thread: string;
  object: CbclObject;
  store: ThreadStore;
  broker: Broker;
  executor: ViewExecutor;
  signal?: AbortSignal;
  grants?: ViewGrants;
  fetch?: typeof fetch;
  onError(error: unknown): void;
}

/** Deliver the initial fold immediately and observe subsequent local and peer appends. */
export function bindProjection(object: CbclObject, thread: string, store: ThreadStore,
  project: (state: State) => void, onError: (error: unknown) => void): () => void {
  const update = () => project(object.read(store.messages(thread), thread));
  const unsubscribe = store.subscribe(thread, () => {
    try { update(); } catch (error) { onError(error); }
  });
  try { update(); } catch (error) { unsubscribe(); throw error; }
  return unsubscribe;
}

export async function mountView(presentation: Presentation, options: MountOptions): Promise<() => void> {
  const { object, store, thread, broker, executor, signal: parent, grants = {} } = options;
  if (object.name !== presentation.contract) throw new Error('View contract digest mismatch');
  parent?.throwIfAborted();
  const controller = new AbortController();
  const { signal } = controller;
  const manifest = presentation;
  const requests = createRequestBroker(manifest.capabilities, grants.requests, { fetch: options.fetch });
  let execution: ViewExecution | undefined;
  let unsubscribe: (() => void) | undefined;
  function dispose() {
    parent?.removeEventListener('abort', dispose);
    controller.abort();
    requests.destroy();
    unsubscribe?.();
    const mounted = execution;
    execution = undefined;
    mounted?.dispose();
  }
  parent?.addEventListener('abort', dispose, { once: true });
  try {
    const ports: ViewPorts = {
      emit: presentation.bindIntent(thread, broker, { signal }),
      request: requests.request,
      invoke: bindOperations(manifest.capabilities?.operations ?? [], grants.operations ?? {},
        { contract: object.name, view: presentation.id, thread, signal }),
    };
    const resources = await loadViewResources(manifest.resources, grants.resources, signal, options.fetch);
    signal.throwIfAborted();
    execution = await executor.mount({ body: presentation.body(), resources, ports, signal });
    signal.throwIfAborted();
    unsubscribe = bindProjection(object, thread, store, state => execution?.project(state), options.onError);
    signal.throwIfAborted();
    return dispose;
  } catch (error) {
    dispose();
    throw error;
  }
}
