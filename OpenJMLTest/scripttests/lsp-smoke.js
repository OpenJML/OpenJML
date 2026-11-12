#!/usr/bin/env node
'use strict';

// Smoke test of an OpenJML LSP launcher (openjml-lsp, or openjml-lsp.bat on Windows; #1033):
// initialize, open a Java file with a JML error, expect its diagnostic, shut down, expect exit 0.
// Covers the launcher and the server's file-URI handling on the host OS.
//   Usage: node lsp-smoke.js <launcher> [<work folder>]
// The work folder (default: a new temporary one) receives the Java file; a name with a space tests quoting.
// Exits non-zero if a step fails.

const cp = require('child_process');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { pathToFileURL } = require('url');

const TIMEOUT_MS = 180000;
const launcher = process.argv[2];
if (!launcher) { console.error('Usage: node lsp-smoke.js <launcher> [<work folder>]'); process.exit(2); }
const work = process.argv[3] ? path.resolve(process.argv[3]) : fs.mkdtempSync(path.join(os.tmpdir(), 'lsp smoke '));
fs.mkdirSync(work, { recursive: true });
const file = path.join(work, 'T.java');
const text = 'public class T {\n    //@ requires zz;\n    void m() {}\n}\n';
fs.writeFileSync(file, text);
const uri = pathToFileURL(file).href;

// Node runs a .bat or .cmd file only through a shell, which splits an unquoted path at spaces
const viaShell = /\.(bat|cmd)$/i.test(launcher);
const proc = cp.spawn(viaShell ? `"${path.resolve(launcher)}"` : path.resolve(launcher), [],
    { shell: viaShell, stdio: ['pipe', 'pipe', 'inherit'] });
proc.on('error', e => fail('cannot start ' + launcher + ': ' + e.message));
proc.stdin.on('error', e => fail('cannot write to the server: ' + e.message + ' (exit code ' + proc.exitCode + ')'));

let nextId = 1;
const pending = new Map();   // request id -> resolve
let onNotification = () => {};

function send(msg) {
    const body = Buffer.from(JSON.stringify({ jsonrpc: '2.0', ...msg }), 'utf8');
    proc.stdin.write(`Content-Length: ${body.length}\r\n\r\n`);
    proc.stdin.write(body);
}
function request(method, params) {
    const id = nextId++;
    send({ id, method, params });
    return new Promise(resolve => pending.set(id, resolve));
}

let buf = Buffer.alloc(0);
proc.stdout.on('data', chunk => {
    buf = Buffer.concat([buf, chunk]);
    for (;;) {
        const sep = buf.indexOf('\r\n\r\n');
        if (sep < 0) return;
        const m = /Content-Length: *(\d+)/i.exec(buf.slice(0, sep).toString('ascii'));
        if (!m) { fail('bad message header: ' + buf.slice(0, sep).toString()); return; }
        const end = sep + 4 + Number(m[1]);
        if (buf.length < end) return;
        const msg = JSON.parse(buf.slice(sep + 4, end).toString('utf8'));
        buf = buf.slice(end);
        if (msg.method && msg.id !== undefined) send({ id: msg.id, result: null });   // server-to-client request
        else if (msg.method) onNotification(msg);
        else if (pending.has(msg.id)) { pending.get(msg.id)(msg); pending.delete(msg.id); }
    }
});

let exitCode = null;
const exited = new Promise(resolve => proc.on('exit', code => { exitCode = code; resolve(); }));

function fail(why) {
    console.log('FAIL lsp-smoke: ' + why);
    proc.kill();
    process.exit(1);
}
function within(promise, what) {
    let timer;
    return Promise.race([promise.finally(() => clearTimeout(timer)),
        new Promise((_, reject) => { timer = setTimeout(() => reject(new Error('timed out waiting for ' + what)), TIMEOUT_MS); })]);
}

async function main() {
    const init = await within(Promise.race([request('initialize',
        { processId: process.pid, rootUri: pathToFileURL(work).href, capabilities: {} }),
        exited.then(() => { throw new Error('server exited with ' + exitCode + ' before initialize'); })]),
        'initialize');
    if (init.error) fail('initialize: ' + JSON.stringify(init.error));
    console.log('PASS initialize');
    send({ method: 'initialized', params: {} });

    const diags = new Promise(resolve => {
        onNotification = msg => {
            if (msg.method === 'textDocument/publishDiagnostics' && msg.params.diagnostics.length > 0) resolve(msg.params);
        };
    });
    send({ method: 'textDocument/didOpen', params: { textDocument: { uri, languageId: 'java', version: 1, text } } });
    const p = await within(diags, 'diagnostics');
    const d = p.diagnostics[0];
    if (p.uri !== uri) fail(`diagnostics for ${p.uri}, expected ${uri}`);
    if (!/cannot find symbol/.test(d.message) || d.range.start.line !== 1) fail('unexpected diagnostic: ' + JSON.stringify(d));
    console.log('PASS diagnostics');

    await within(request('shutdown', null), 'shutdown');
    send({ method: 'exit', params: null });
    await within(exited, 'exit');
    if (exitCode !== 0) fail('server exit code ' + exitCode);
    console.log('PASS shutdown');
}

main().then(() => process.exit(0), e => fail(e.message));
