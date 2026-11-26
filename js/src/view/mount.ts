import type { CbclObject, ThreadStore, IntentResult } from '../object/index.js';
import type { Broker } from '../object/broker.js';
import { installDialect } from '../verifier.ts';
import type { InstalledDialect, State } from '../verifier.js';
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
export interface ProjectionSource {
  read(thread: string): State;
  subscribe(thread: string, changed: () => void): () => void;
}
type ProjectionStore = Pick<ThreadStore, 'messages' | 'subscribe'>;
export type MountOptions = ({
  object: CbclObject; store: ProjectionStore;
} | {
  dialect: InstalledDialect; projection: ProjectionSource;
}) & {
  thread: string;
  broker: Broker;
  executor: ViewExecutor;
  signal?: AbortSignal;
  grants?: ViewGrants;
  fetch?: typeof fetch;
  onError(error: unknown): void;
}

/** Deliver the initial fold immediately and observe subsequent local and peer appends. */
export function bindProjection(object: CbclObject, thread: string, store: ProjectionStore,
  project: (state: State) => void, onError: (error: unknown) => void): () => void {
  return observeProjection(thread, { read: id => object.read(store.messages(id), id),
    subscribe: (id, changed) => store.subscribe(id, changed) }, project, onError);
}

function observeProjection(thread: string, source: ProjectionSource, project: (state: State) => void,
  onError: (error: unknown) => void): () => void {
  const update = () => project(source.read(thread));
  const unsubscribe = source.subscribe(thread, () => {
    try { update(); } catch (error) { onError(error); }
  });
  try { update(); } catch (error) { unsubscribe(); throw error; }
  return unsubscribe;
}

export async function mountView(presentation: Presentation, options: MountOptions): Promise<() => void> {
  const { thread, broker, executor, signal: parent, grants = {} } = options;
  const name = 'object' in options ? options.object.name : installDialect(options.dialect).name;
  if (name !== presentation.contract) throw new Error('View contract digest mismatch');
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
    const stop = unsubscribe;
    unsubscribe = undefined;
    const mounted = execution;
    execution = undefined;
    try { stop?.(); } finally { mounted?.dispose(); }
  }
  parent?.addEventListener('abort', dispose, { once: true });
  try {
    const ports: ViewPorts = {
      emit: presentation.bindIntent(thread, broker, { signal }),
      request: requests.request,
      invoke: bindOperations(manifest.capabilities?.operations ?? [], grants.operations ?? {},
        { contract: name, view: presentation.id, thread, signal }),
    };
    const resources = await loadViewResources(manifest.resources, grants.resources, signal, options.fetch);
    signal.throwIfAborted();
    execution = await executor.mount({ body: presentation.body(), resources, ports, signal });
    signal.throwIfAborted();
    const project = (state: State) => execution?.project(state);
    unsubscribe = 'object' in options
      ? bindProjection(options.object, thread, options.store, project, options.onError)
      : observeProjection(thread, options.projection, project, options.onError);
    signal.throwIfAborted();
    return dispose;
  } catch (error) {
    dispose();
    throw error;
  }
}
