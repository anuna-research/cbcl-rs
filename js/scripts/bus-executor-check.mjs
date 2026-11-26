// Executed in Chromium against a separately supplied cbcl-bus checkout.
export async function checkBusExecutor(source) {
  const { createViewEvaluator } = await import('/bus-runtime/evaluator.js');
  const { installDialect } = await import('cbcl');
  const { defineView, mountView } = await import('cbcl/view');
  const dialect = installDialect(source);
  const presentation = await defineView({ contract: dialect,
    view: { html: '<script>onProjection = async () => { try { await request("denied"); } catch { await request("echo"); } };</script>' },
    capabilities: { requests: ['echo', 'denied'].map(id => ({ id, url: 'https://example.org/' + id, response: 'text' })) } });
  const frame = document.createElement('iframe');
  frame.sandbox = 'allow-same-origin';
  document.body.append(frame);
  const received = Promise.withResolvers();
  let ports, evaluator;
  try {
    const dispose = await mountView(presentation, { dialect, thread: 't',
      broker: { applyIntent() { throw Error('Unexpected intent'); } },
      projection: { read: () => ({}), subscribe: () => () => {} }, onError: received.reject,
      grants: { requests: ['echo'] }, fetch: async url => { received.resolve(url); return new Response('ok'); },
      executor: { async mount(input) {
        ports = input.ports;
        evaluator = createViewEvaluator(frame.contentDocument, input.body, {
          emit: ports.emit, request: ports.request, resources: input.resources.images, onError: received.reject,
        });
        await evaluator.ready;
        if (!evaluator.active) throw Error('Bus evaluator failed to start');
        return { project: evaluator.pushState, dispose: evaluator.destroy };
      } },
    });
    let url;
    try {
      url = await Promise.race([received.promise, new Promise((_, reject) =>
        setTimeout(() => reject(Error('Bus projection timed out')), 5000))]);
    } finally { dispose(); }
    try { await ports.request('echo'); } catch { return { url, revoked: !evaluator.active }; }
    return { url, revoked: false };
  } finally { frame.remove(); }
}
