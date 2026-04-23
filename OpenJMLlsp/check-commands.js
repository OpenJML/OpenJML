#!/usr/bin/env node
'use strict';

/**
 * check-commands.js — verifies that the command-name constants in extension.js
 * match the string literals in OpenJMLCommands.java.
 *
 * Run directly:   node OpenJMLlsp/check-commands.js
 * Run via make:   make -C OpenJMLTest/lsp check-commands
 *
 * Exits 0 when the two sets are identical, 1 when they differ.
 */

const fs   = require('fs');
const path = require('path');

const JAVA_FILE    = path.join(__dirname, 'src', 'org', 'openjml', 'lsp', 'OpenJMLCommands.java');
const JS_FILE      = path.join(__dirname, 'vscode-extension', 'extension.js');
const ECLIPSE_FILE = path.join(__dirname, '..', 'OpenJMLUI', 'src', 'org', 'jmlspecs', 'openjml', 'eclipse', 'OpenJMLConstants.java');

// ---------------------------------------------------------------------------
// Extract from OpenJMLCommands.java
// Lines of the form:   public static final String FOO = "openjml.bar";
// ---------------------------------------------------------------------------
function extractJavaCommands(src) {
    const re = /public\s+static\s+final\s+String\s+\w+\s*=\s*"(openjml\.[^"]+)"\s*;/g;
    const found = new Set();
    let m;
    while ((m = re.exec(src)) !== null) found.add(m[1]);
    return found;
}

// ---------------------------------------------------------------------------
// Extract from extension.js
// Lines of the form:   const CMD_FOO = 'openjml.bar';
// ---------------------------------------------------------------------------
function extractJsCommands(src) {
    const re = /const\s+CMD_\w+\s*=\s*'(openjml\.[^']+)'\s*;/g;
    const found = new Set();
    let m;
    while ((m = re.exec(src)) !== null) found.add(m[1]);
    return found;
}

// ---------------------------------------------------------------------------
// Extract from OpenJMLConstants.java (Eclipse plugin)
// Only CMD_* fields are LSP workspace/executeCommand names; other openjml.*
// constants are Eclipse plugin IDs, preference keys, etc.
// ---------------------------------------------------------------------------
function extractEclipseCommands(src) {
    const re = /public\s+static\s+final\s+String\s+CMD_\w+\s*=\s*"(openjml\.[^"]+)"\s*;/g;
    const found = new Set();
    let m;
    while ((m = re.exec(src)) !== null) found.add(m[1]);
    return found;
}

// ---------------------------------------------------------------------------
// Server commands intentionally not used by the VS Code extension.
// Adding a command here silences the "MISSING in extension.js" warning for it.
// ---------------------------------------------------------------------------
const SERVER_ONLY = new Set([
    // VS Code uses the standard workspace/symbol LSP request for symbol lookup.
    // symbolsForProject exists for the Eclipse multi-project client, which needs
    // to filter symbols to one project by ID (IProject.getName()).  There is no
    // equivalent concept in the single-workspace VS Code client.
    'openjml.symbolsForProject',
]);

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------
let ok = true;

let javaSrc, jsSrc, eclipseSrc;
try { javaSrc = fs.readFileSync(JAVA_FILE, 'utf8'); }
catch (e) { console.error('ERROR: cannot read ' + JAVA_FILE + ': ' + e.message); process.exit(1); }
try { jsSrc = fs.readFileSync(JS_FILE, 'utf8'); }
catch (e) { console.error('ERROR: cannot read ' + JS_FILE + ': ' + e.message); process.exit(1); }
try { eclipseSrc = fs.readFileSync(ECLIPSE_FILE, 'utf8'); }
catch (e) { console.error('ERROR: cannot read ' + ECLIPSE_FILE + ': ' + e.message); process.exit(1); }

const javaCmds    = extractJavaCommands(javaSrc);
const jsCmds      = extractJsCommands(jsSrc);
const eclipseCmds = extractEclipseCommands(eclipseSrc);

// ---------------------------------------------------------------------------
// Check 1: VS Code extension vs server
// ---------------------------------------------------------------------------
console.log('--- VS Code extension vs OpenJMLCommands.java ---');
for (const cmd of javaCmds) {
    if (!jsCmds.has(cmd) && !SERVER_ONLY.has(cmd)) {
        console.error('MISSING in extension.js        : ' + cmd);
        ok = false;
    }
}
for (const cmd of jsCmds) {
    if (!javaCmds.has(cmd)) {
        console.error('MISSING in OpenJMLCommands.java: ' + cmd);
        ok = false;
    }
}
if (ok) console.log('OK — ' + jsCmds.size + ' command name(s) match');

// ---------------------------------------------------------------------------
// Check 2: Eclipse plugin vs server
// ---------------------------------------------------------------------------
console.log('--- Eclipse plugin vs OpenJMLCommands.java ---');
let eclipseOk = true;
for (const cmd of javaCmds) {
    if (!eclipseCmds.has(cmd) && !SERVER_ONLY.has(cmd)) {
        console.error('MISSING in OpenJMLConstants.java: ' + cmd);
        eclipseOk = false;
        ok = false;
    }
}
for (const cmd of eclipseCmds) {
    if (!javaCmds.has(cmd)) {
        console.error('MISSING in OpenJMLCommands.java : ' + cmd);
        eclipseOk = false;
        ok = false;
    }
}
if (eclipseOk) console.log('OK — ' + eclipseCmds.size + ' command name(s) match');

process.exit(ok ? 0 : 1);
