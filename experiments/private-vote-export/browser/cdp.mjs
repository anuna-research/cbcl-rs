#!/usr/bin/env node
// Node 25 native WebSocket only. Invoked by run-browser.py, not an npm package.
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';

const [endpoint, mode, output, origin] = process.argv.slice(2);
const modes = new Set(['verify', 'count', 'prove', 'cancel-trace', 'cancel-prove']);
if (!endpoint || !output || !modes.has(mode) || !/^http:\/\/127\.0\.0\.1:[0-9]+$/.test(origin ?? '') || !/^ws:\/\/127\.0\.0\.1:[0-9]+\/devtools\/browser\//.test(endpoint)) {
  process.stderr.write('usage: node cdp.mjs WS_ENDPOINT MODE OUTPUT_DIR LOOPBACK_ORIGIN\n');
  process.exit(2);
}
const started = performance.now();
const record = {mode, origin, ok: false, version: null, network: [], runtime: [], targets: [], capabilities: [], errors: [], metrics: null, result: null};
const pending = new Map();
const sessions = new Map();
const tasks = new Set();
let counter = 0;
let socket;
let closed = false;
let abortRun;
const abort = new Promise((_, reject) => { abortRun = reject; });
// Handled immediately, even before a command races it.
abort.catch(() => {});
function fail(message) {
  const error = String(message).slice(0, 4096);
  record.errors.push(error);
  abortRun(new Error(error));
}
function track(promise) {
  tasks.add(promise);
  promise.catch(error => fail(error.message)).finally(() => tasks.delete(promise));
}
function send(method, params = {}, sessionId, timeout = 30_000) {
  if (closed || socket.readyState !== WebSocket.OPEN) return Promise.reject(new Error('CDP socket closed'));
  const id = ++counter;
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      pending.delete(id);
      reject(new Error(`CDP timeout: ${method}`));
    }, timeout);
    pending.set(id, {resolve, reject, timer, method});
    socket.send(JSON.stringify({id, method, params, ...(sessionId ? {sessionId} : {})}));
  });
}
function local(url) {
  try { return new URL(url).origin === origin; } catch { return false; }
}
function display(value) {
  // Console output is diagnostic only; do not fetch objects/properties from the VM.
  return String(value.value ?? value.description ?? value.type).slice(0, 2048);
}
async function configure(sessionId, info) {
  if (!['page', 'worker', 'shared_worker'].includes(info.type)) {
    if (info.type === 'service_worker') throw new Error('service worker prohibited: ' + JSON.stringify(info));
    await send('Runtime.runIfWaitingForDebugger', {}, sessionId);
    return;
  }
  await send('Runtime.enable', {}, sessionId);
  await send('Network.enable', {}, sessionId);
  const pageInterception = info.type === 'page';
  if (pageInterception) {
    await send('Fetch.enable', {patterns: [{urlPattern: '*', requestStage: 'Request'}]}, sessionId);
  }
  record.capabilities.push({sessionId, targetId: info.targetId, type: info.type,
    runtimeMonitoring: true, networkMonitoring: true, fetchInterception: pageInterception,
    preEgressPolicy: pageInterception ? 'page Fetch interception and same-origin CSP' : 'worker response CSP connect-src self; Network events checked, no worker Fetch domain'});
  // Recursively attach workers before their first script can run.
  await send('Target.setAutoAttach', {autoAttach: true, waitForDebuggerOnStart: true, flatten: true}, sessionId);
  if (info.type === 'page') await send('Page.enable', {}, sessionId);
  await send('Runtime.runIfWaitingForDebugger', {}, sessionId);
}
function event(message) {
  const {method, params = {}, sessionId} = message;
  if (method === 'Target.attachedToTarget') {
    const info = params.targetInfo;
    // Preserve full target identity before classification, including a service
    // worker failure before the experiment page has ever navigated.
    record.targets.push({event: 'attached', sessionId: params.sessionId, parentSessionId: sessionId, info});
    const entry = {info, configured: null};
    sessions.set(params.sessionId, entry);
    entry.configured = configure(params.sessionId, info);
    track(entry.configured);
  } else if (method === 'Fetch.requestPaused') {
    const {requestId, request} = params;
    if (!local(request.url)) {
      record.network.push({event: 'blocked', sessionId, url: request.url, method: request.method});
      // Refuse non-loopback requests before they leave the renderer/worker.
      track(send('Fetch.failRequest', {requestId, errorReason: 'BlockedByClient'}, sessionId));
      fail('non-loopback request blocked: ' + request.url);
    } else {
      track(send('Fetch.continueRequest', {requestId}, sessionId));
    }
  } else if (method === 'Network.requestWillBeSent') {
    const {requestId, request, type, redirectResponse} = params;
    record.network.push({event: 'request', sessionId, requestId, url: request.url, method: request.method, type, redirectStatus: redirectResponse?.status});
    if (!local(request.url)) fail('non-loopback network request: ' + request.url);
  } else if (method === 'Network.webSocketCreated' || method === 'Network.webTransportCreated') {
    record.network.push({event: method, sessionId, url: params.url});
    fail('unexpected socket transport: ' + params.url);
  } else if (method === 'Network.responseReceived') {
    const {requestId, response, type} = params;
    record.network.push({event: 'response', sessionId, requestId, url: response.url, status: response.status, mimeType: response.mimeType, type});
    if (response.status >= 400) fail(`HTTP ${response.status}: ${response.url}`);
  } else if (method === 'Network.loadingFailed') {
    record.network.push({event: 'failed', sessionId, requestId: params.requestId, error: params.errorText, cancelled: params.canceled === true});
    // Worker termination can legitimately cancel an in-flight request only in a
    // cancellation mode. Other failures are never counted as negative tests.
    if (!(mode.startsWith('cancel-') && params.canceled === true)) fail('network load failed: ' + params.errorText);
  } else if (method === 'Runtime.consoleAPICalled') {
    const item = {event: 'console', sessionId, type: params.type, args: (params.args ?? []).map(display), timestamp: params.timestamp};
    record.runtime.push(item);
    process.stdout.write(JSON.stringify(item) + '\n');
    if (params.type === 'error' || params.type === 'assert') fail('unexpected browser console ' + params.type + ': ' + item.args.join(' '));
  } else if (method === 'Runtime.exceptionThrown') {
    const detail = params.exceptionDetails;
    const item = {event: 'exception', sessionId, text: detail?.text, description: detail?.exception?.description, url: detail?.url, line: detail?.lineNumber};
    record.runtime.push(item);
    fail('unexpected runtime exception: ' + (item.description ?? item.text));
  } else if (method === 'Inspector.targetCrashed' || method === 'Target.targetCrashed') {
    fail('browser target crashed');
  }
}
function message(raw) {
  let value;
  try { value = JSON.parse(raw.data); } catch { fail('malformed CDP response'); return; }
  if (value.id) {
    const command = pending.get(value.id);
    if (!command) return;
    clearTimeout(command.timer);
    pending.delete(value.id);
    if (value.error) command.reject(new Error(`${command.method}: ${JSON.stringify(value.error)}`));
    else command.resolve(value.result);
  } else {
    try { event(value); } catch (error) { fail(error.message); }
  }
}
async function run() {
  socket = new WebSocket(endpoint);
  socket.addEventListener('message', message);
  socket.addEventListener('close', () => {
    closed = true;
    for (const command of pending.values()) {
      clearTimeout(command.timer);
      command.reject(new Error(`CDP disconnected during ${command.method}`));
    }
    pending.clear();
    if (!record.ok) abortRun(new Error('CDP disconnected'));
  });
  socket.addEventListener('error', () => fail('CDP WebSocket error'));
  await Promise.race([new Promise(resolve => socket.addEventListener('open', resolve, {once: true})), abort]);
  record.version = await send('Browser.getVersion');
  await send('Target.setAutoAttach', {autoAttach: true, waitForDebuggerOnStart: true, flatten: true});
  const {targetId} = await send('Target.createTarget', {url: 'about:blank'});
  const attachDeadline = performance.now() + 15_000;
  let page;
  while (!page) {
    for (const [id, entry] of sessions) if (entry.info.targetId === targetId) page = {id, ...entry};
    if (performance.now() > attachDeadline) throw new Error('new page auto-attachment timed out');
    if (!page) await new Promise(resolve => setTimeout(resolve, 10));
  }
  await page.configured;
  await send('Performance.enable', {}, page.id);
  const navigation = await send('Page.navigate', {url: origin + '/'}, page.id);
  if (navigation.errorText) throw new Error('navigation failed: ' + navigation.errorText);
  const readyDeadline = performance.now() + 30_000;
  for (;;) {
    const ready = await send('Runtime.evaluate', {expression: 'typeof window.runExperiment === "function"', returnByValue: true}, page.id);
    if (ready.exceptionDetails) throw new Error('page readiness evaluation threw');
    if (ready.result?.value === true) break;
    if (performance.now() > readyDeadline) throw new Error('window.runExperiment was not installed');
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  const evaluation = await send('Runtime.evaluate', {
    expression: `window.runExperiment(${JSON.stringify(mode)})`,
    awaitPromise: true,
    returnByValue: true,
    userGesture: true,
  }, page.id, 25 * 60 * 1000);
  if (evaluation.exceptionDetails) throw new Error(evaluation.exceptionDetails.exception?.description ?? evaluation.exceptionDetails.text);
  record.result = evaluation.result?.value;
  if (record.result?.ok !== true) throw new Error('runExperiment returned ok:false or no result');
  if (mode.startsWith('cancel-') && !(record.result.cancelled === true && record.result.recovery?.ok === true && record.result.recovery?.verified === true)) {
    throw new Error('cancellation/recovery verification evidence missing');
  }
  record.metrics = await send('Performance.getMetrics', {}, page.id);
  await Promise.all([...tasks]);
  if (record.errors.length) throw new Error('runtime/network errors recorded');
  record.ok = true;
}
const deadline = setTimeout(() => fail('25 minute browser experiment timeout'), 25 * 60 * 1000);
let status = 1;
try {
  await Promise.race([run(), abort]);
  status = 0;
} catch (error) {
  const description = String(error?.stack ?? error);
  if (!record.errors.includes(error?.message)) record.errors.push(description);
  process.stderr.write(description + '\n');
} finally {
  clearTimeout(deadline);
  if (socket?.readyState === WebSocket.OPEN) {
    try { await send('Browser.close', {}, undefined, 2000); } catch { /* Python reaps the whole group. */ }
    socket.close();
  }
  for (const command of pending.values()) clearTimeout(command.timer);
  record.elapsed_seconds = (performance.now() - started) / 1000;
  writeFileSync(join(output, mode + '-cdp.json'), JSON.stringify(record, null, 2) + '\n');
}
process.exit(status);
