import type { CbclObject, DialectInfo, IntentResult } from '../object/index.js';
import type { State } from '../verifier.js';

export const VIEW_VERSION: 3;
export const MAX_VIEW_BYTES: number;
export const MAX_CUSTOM_SOURCE_BYTES: number;
export const MAX_BUNDLE_BYTES: number;

export type Component =
  | { type: 'text'; text: string }
  | { type: 'value'; field: string; label: string }
  | { type: 'form'; verb: string; label: string; fields: Record<string, string> };
export type CustomView = { html: string } | { render: string };
export type View = readonly Component[] | CustomView;
export interface Layout {
  width?: 'compact' | 'standard' | 'wide';
  minHeight?: number;
  maxHeight?: number;
  aspectRatio?: number;
  overflow?: 'scroll';
}
export interface Capabilities {
  operations?: import('./operations.js').OperationDeclaration[];
  sound?: boolean;
  media?: { accept: ('image' | 'audio')[] };
  requests?: { id: string; url: string; response: 'text' | 'json'; parameters?: string[] }[];
}
export interface Resources { images?: string[]; styles?: string[] }
export interface ViewSpec { view: View; layout?: Layout; resources?: Resources; capabilities?: Capabilities }
export interface ViewRecord {
  version: 3; kind: 'view'; contract: string; view: unknown;
  layout?: unknown; resources?: unknown; capabilities?: unknown;
}
export interface Presentation extends Readonly<ViewSpec> {
  readonly id: string;
  readonly contract: string;
  readonly serialized: string;
  readonly external: boolean;
  bindIntent(thread: string, broker: Pick<import('../object/broker.js').Broker, 'applyIntent'>, options?: (() => string) | { nextClock?: () => string; signal?: AbortSignal }):
    (verb: string, fields?: Record<string, unknown>) => Promise<IntentResult>;
  body(): string;
}
export interface RenderHost {
  invoke: import('./operations.js').InvokeOperation;
  emit(verb: string, fields: Record<string, unknown>): void;
  request(id: string, parameters?: Record<string, string>): Promise<unknown>;
}
export interface HtmlTemplate { strings: string[]; values: unknown[] }
export function html(strings: TemplateStringsArray, ...values: unknown[]): HtmlTemplate;
type Dialect = string | Pick<CbclObject, 'dialect'>;
export function defineView(spec: Omit<ViewSpec, 'view'> & {
  contract: Dialect; view: View | ((state: State, host: RenderHost) => unknown);
}): Promise<Presentation>;
export function importView(text: string, contract: Dialect): Promise<Presentation>;
export function defaultPresentation(contract: Dialect): Promise<Presentation>;
export function defaultView(info: DialectInfo): { view: Component[] };
export function validateView(spec: ViewSpec, info: DialectInfo): void;
/** Checks the record envelope. importView also validates the presentation against its contract. */
export function recognizeView(text: string): ViewRecord;
export function exportBundle(object: Pick<CbclObject, 'serialized'>, presentation: Pick<Presentation, 'serialized'>): string;
export function recognizeBundle(text: string): { version: 3; kind: 'bundle'; contract: unknown; view: unknown };
export function importBundle(text: string): Promise<Readonly<{ object: CbclObject; presentation: Presentation }>>;
export function componentBody(spec: { view: readonly Component[]; verbs: DialectInfo['verbs']; state: DialectInfo['state'] }): string;
export function customBody(view: CustomView): string;

/** A per-mount request authority, restricted to host-granted operation IDs. */
export function createRequestBroker(manifest?: Capabilities, grants?: string[], options?: {
  fetch?: typeof fetch; now?: () => number;
}): { request: RenderHost['request']; destroy(): void };
export interface LoadedResources {
  images: Map<string, string>; styles: string[]; failures: string[];
}
export function loadViewResources(requested: Resources | undefined, approved: Resources | undefined,
  signal: AbortSignal, fetcher?: typeof fetch): Promise<LoadedResources>;
export { bindProjection, mountView } from './mount.js';
export type { ViewExecutor, ViewExecution, MountOptions, ViewPorts, ViewGrants } from './mount.js';

/** Browser frame policy for interpreter-backed views. */
export const CONFINED_VIEW_CSP: string;

export { defineOperation } from './operations.js';
export type { OperationLimits, OperationDeclaration, OperationGrant, CapabilityData, CapabilityScope, OperationHandler, InvokeOperation } from './operations.js';
