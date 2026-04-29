'use strict';
/**
 * ExTester runner for OpenJML VS Code extension UI tests.
 *
 * Uses the development extension and server rather than a packaged release.
 * Future: swap EXTENSION_DIR and SERVER_PATH for a pristine release installation.
 *
 * Version requirements:
 *   - Node.js >= 20  (@vscode/vsce and vscode-extension-tester both require Node 16+;
 *                     Node 20 LTS is the minimum recommended version)
 *   - vscode-extension-tester >= 8.23  (earlier versions target VS Code <= 1.110 and use
 *     @redhat-developer/locators, which does not support the xterm.js output panel
 *     introduced in VS Code 1.117; getText() on the output channel returns empty in 1.117+)
 *   - VS Code 1.118.0 (pinned; update the downloadCode call in this file when re-validating
 *     against a newer release; output-channel getText() unavailable in 1.117+)
 *
 * Usage:
 *   node runner.js                   # run all test suites
 *   node runner.js 02_commands       # run only the matching suite(s)
 */
const { ExTester } = require('vscode-extension-tester');
const path = require('path');
const fs   = require('fs');

const SCRIPT_DIR    = path.resolve(__dirname);

// Paths to the development build (relative to this file).
const EXTENSION_DIR = path.resolve(SCRIPT_DIR, '../../OpenJMLlsp/vscode-extension');
const SERVER_PATH   = path.resolve(SCRIPT_DIR, '../../OpenJMLlsp/openjml-lsp');
const RESOURCES_DIR = path.resolve(SCRIPT_DIR, 'resources');
const EXTRA_DIR     = path.resolve(SCRIPT_DIR, 'resources/extra');
const STORAGE_DIR   = path.resolve(SCRIPT_DIR, '.test-resources');
const SETTINGS_OUT  = path.resolve(STORAGE_DIR, 'test-settings.json');

// Test file glob (relative to cwd = this directory).
// A bare prefix like "05" is expanded to "05*.test.js".
const raw    = process.argv[2] || '*.test.js';
const filter = raw.includes('*') || raw.includes('.') ? raw : `${raw}*.test.js`;
const TEST_GLOB = `test/suite/${filter}`;

// Write a VS Code user-settings file pointing at the development server.
// checkTriggerOn / escTriggerOn = "manual" so the extension doesn't automatically
// run checks on every file open (which would spam errors in tests that only
// check command registration or menu structure).
function writeSettings() {
    fs.mkdirSync(STORAGE_DIR, { recursive: true });
    // Set OPENJML_SERVER_PATH so the extension finds the server immediately at
    // activation, without waiting for VS Code to apply the user settings file.
    // This avoids a ~4.5-minute delay caused by the "server not found" dialog
    // blocking until onDidChangeConfiguration fires with the loaded setting.
    process.env.OPENJML_SERVER_PATH = SERVER_PATH;
    // Direct the server log to a per-run path so helpers.js can poll it for startup.
    // Delete any stale copy first so we never read output from a previous run.
    process.env.OPENJML_LSP_LOG = path.join(STORAGE_DIR, 'server.log');
    try { fs.unlinkSync(process.env.OPENJML_LSP_LOG); } catch (_) {}
    const settings = {
        'openjml.serverPath':      SERVER_PATH,
        'openjml.checkTriggerOn':  'manual',
        'openjml.escTriggerOn':    'manual',
        // Suppress the java.format.enabled warning dialog in activate(), which
        // blocks startClient() for several minutes in a fresh test workspace.
        'java.format.enabled':     false,
    };
    fs.writeFileSync(SETTINGS_OUT, JSON.stringify(settings, null, 2));
}

async function main() {
    writeSettings();

    const tester = new ExTester(STORAGE_DIR);

    // Download VS Code and ChromeDriver (both are cached after the first run).
    // Version is pinned: 'latest' chases regressions with each VS Code release.
    // Update the pin when the test suite has been validated against a newer version.
    await tester.downloadCode('1.118.0');
    await tester.downloadChromeDriver('1.118.0');

    // Package and install the extension.
    // vscode-extension-tester's installVsix() uses vsce to package the extension
    // from the current working directory, so we temporarily chdir to EXTENSION_DIR.
    process.chdir(EXTENSION_DIR);
    await tester.installVsix({});
    process.chdir(SCRIPT_DIR);

    // Run tests — the extension was installed into ExTester's extensions folder
    // by installVsix above, so VS Code finds it without EXTENSION_DEV_PATH.
    // Disable third-party extensions that crash the test VS Code instance.
    const result = await tester.runTests(TEST_GLOB, {
        resources:  [RESOURCES_DIR, EXTRA_DIR],
        settings:   SETTINGS_OUT,
        config:     path.join(SCRIPT_DIR, '.mocharc.yml'),
        vscodeLaunchArgs: [
            '--disable-extension', 'visualstudioexptteam.intellicode-api-usage-examples',
        ],
    });
    process.exit(result);
}

main().catch(err => {
    console.error('Runner error:', err);
    process.exit(1);
});
