import type { CbclObject, DialectInfo } from '../object/index.js';
import type { State } from '../verifier.js';

export const VIEW_VERSION: 3;
export const MAX_VIEW_BYTES: number;
export const MAX_CUSTOM_SOURCE_BYTES: number;
export const MAX_BUNDLE_BYTES: number;
export const COMPOSER_ICONS: readonly ['box', 'layers', 'bar-chart', 'bookmark', 'pin', 'check', 'star', 'clock', 'pencil', 'activity', 'archive', 'hash', 'globe', 'link'];
export const COMPOSER_TINTS: readonly ['moss', 'stone', 'sage', 'olive', 'fern', 'ochre'];

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
  sound?: boolean;
  media?: { accept: ('image' | 'audio')[] };
  requests?: { id: string; url: string; response: 'text' | 'json'; parameters?: string[] }[];
}
export interface Resources { images?: string[]; styles?: string[] }
export interface FieldHint { label?: string; placeholder?: string; help?: string; multiline?: boolean }
export interface Composer {
  label?: string;
  send?: string;
  icon?: typeof COMPOSER_ICONS[number];
  tint?: typeof COMPOSER_TINTS[number];
  title?: string;
  order?: string[];
  fields?: Record<string, FieldHint>;
  then?: { verb: string; label?: string; fields?: Record<string, FieldHint> }[];
}
export interface ViewSpec { view: View; layout?: Layout; resources?: Resources; capabilities?: Capabilities }
export interface ViewRecord {
  version: 3; kind: 'view'; contract: string; view: unknown;
  layout?: unknown; resources?: unknown; capabilities?: unknown; composer?: unknown;
}
export interface Presentation extends Readonly<ViewSpec> {
  readonly id: string;
  readonly contract: string;
  readonly serialized: string;
  readonly external: boolean;
  readonly composer: Composer | null;
  readonly composerDiscarded?: string;
  readonly composerDropped: string[];
  body(): string;
}
export interface RenderHost {
  emit(verb: string, fields: Record<string, unknown>): void;
  request(id: string, parameters?: Record<string, string>): Promise<unknown>;
}
export interface HtmlTemplate { strings: string[]; values: unknown[] }
export function html(strings: TemplateStringsArray, ...values: unknown[]): HtmlTemplate;
type Dialect = string | Pick<CbclObject, 'dialect'>;
export function defineView(spec: Omit<ViewSpec, 'view'> & {
  contract: Dialect; view: View | ((state: State, host: RenderHost) => unknown); composer?: Composer;
}): Promise<Presentation>;
export function importView(text: string, contract: Dialect): Promise<Presentation>;
export function defaultPresentation(contract: Dialect): Promise<Presentation>;
export function defaultView(info: DialectInfo): { view: Component[] };
export function recognizeComposer(composer: unknown, info: DialectInfo): {
  block: Composer | null; discarded?: string; dropped: string[];
};
export function validateView(spec: ViewSpec, info: DialectInfo): void;
/** Checks the record envelope. importView also validates the presentation against its contract. */
export function recognizeView(text: string): ViewRecord;
export function bundleText(object: Pick<CbclObject, 'serialized'>, presentation: Pick<Presentation, 'serialized'>): string;
export function recognizeBundle(text: string): { version: 3; kind: 'bundle'; contract: unknown; view: unknown };
export function importBundle(text: string): Promise<Readonly<{ object: CbclObject; presentation: Presentation }>>;
export function componentBody(spec: { view: readonly Component[]; verbs: DialectInfo['verbs']; state: DialectInfo['state'] }): string;
export function customBody(view: CustomView): string;
