// Test adapter only. The SDK distributes the ViewExecutor interface; the consumer owns the VM.
import variant from '@jitl/quickjs-singlefile-browser-release-sync';
import { newQuickJSWASMModuleFromVariant } from 'quickjs-emscripten-core';
import { ready, installDialect } from 'cbcl';
import { defineView, mountView } from 'cbcl/view';

export async function checkBrowser(source) {
  let failed = false;
  try { await ready(); } catch { failed = true; }
  if (!failed) throw Error('Expected initial WASM request to fail');
  await Promise.all([ready(), ready()]);
  const dialect = installDialect(source);
  const presentation = await defineView({ contract: dialect,
    view: { html: '<script>function project(state) { invoke("display", state); }</script>' },
    capabilities: { operations: ['display', 'denied'] } });
  const quickjs = await newQuickJSWASMModuleFromVariant(variant);
  let changed, current = 1, ports, disposed = false, cleaned = false;
  const seen = [];
  const dispose = await mountView(presentation, {
    dialect, thread: 'poll',
    projection: {
      read: () => ({ count: current }),
      subscribe(_id, fn) { changed = fn; return () => { changed = undefined; }; },
    },
    broker: { applyIntent() { throw Error('Unexpected intent'); } },
    onError(error) { throw error; },
    grants: { operations: { display(input, scope) {
      seen.push(input.count);
      scope.onDispose(() => { cleaned = true; });
      return null;
    } } },
    executor: { mount(input) {
      ports = input.ports;
      const vm = quickjs.newContext();
      const invoke = vm.newFunction('invoke', (name, data) => {
        ports.invoke(vm.getString(name), vm.dump(data));
        return vm.undefined;
      });
      vm.setProp(vm.global, 'invoke', invoke);
      invoke.dispose();
      const run = code => vm.unwrapResult(vm.evalCode(code)).dispose();
      const doc = new DOMParser().parseFromString(input.body, 'text/html');
      run(doc.querySelector('script').textContent);
      run('if (typeof document !== "undefined" || typeof fetch !== "undefined") throw Error("Unexpected native browser API")');
      run('let denied = false; try { invoke("denied", null) } catch { denied = true } if (!denied) throw Error("Unapproved call")');
      return {
        project(state) { run('project(' + JSON.stringify(state) + ')'); },
        dispose() { vm.dispose(); disposed = true; },
      };
    } },
  });
  current = 2;
  changed();
  dispose();
  let revoked = false;
  try { ports.invoke('display', { count: 3 }); } catch { revoked = true; }
  return { seen, revoked, cleaned, disposed, subscribed: !!changed };
}
