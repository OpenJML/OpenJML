'use strict';
/**
 * Shared helpers for OpenJML VS Code UI test suites.
 *
 * Import what you need:
 *   const { suiteTeardown, readOpenJMLOutput, waitForOutput,
 *           getExplorerSection, findExplorerItem,
 *           invokeContextMenuItem, runCommand } = require('./helpers');
 *
 * All functions are best-effort: transient DOM/Selenium failures are retried
 * internally and the caller receives null/false/'' rather than a thrown error,
 * so test code stays clean.
 */

const { VSBrowser, EditorView, SideBarView, BottomBarPanel, Workbench }
    = require('vscode-extension-tester');
const { Key } = require('selenium-webdriver');
const fs   = require('fs');
const path = require('path');

// Path to the server log file.  runner.js sets OPENJML_LSP_LOG and deletes any
// stale copy before launching VS Code.  The computed fallback covers the case
// where ExTester spawns the Mocha process without inheriting that env var.
const SERVER_LOG = process.env.OPENJML_LSP_LOG
    || path.resolve(__dirname, '../../.test-resources/server.log');

// ── Output channel ────────────────────────────────────────────────────────────

/**
 * Open (or focus) the OpenJML output channel and return its current text.
 * Returns null if the channel does not exist yet.
 * Leaves the bottom bar closed.
 */
async function readOpenJMLOutput() {
    // VS Code 1.118+ changed the bottom panel DOM; BottomBarPanel can hang
    // indefinitely waiting for elements.  Guard with a hard 8s timeout so
    // callers always get a result quickly and skip instead of timing out.
    try {
        return await Promise.race([
            _readOpenJMLOutputInner(),
            new Promise((_, rej) => setTimeout(() => rej(new Error('timeout')), 8_000)),
        ]);
    } catch (_) { return null; }
}

async function _readOpenJMLOutputInner() {
    const driver    = VSBrowser.instance.driver;
    const bottomBar = new BottomBarPanel();
    try {
        await bottomBar.toggle(true);
        const outputView = await bottomBar.openOutputView();

        let channels = [];
        for (let attempt = 0; attempt < 4; attempt++) {
            try { channels = await outputView.getChannelNames(); break; }
            catch (_) { await driver.sleep(500); }
        }

        const ch = channels.find(c => c.includes('OpenJML'));
        if (!ch) { await bottomBar.toggle(false); return null; }

        await outputView.selectChannel(ch);
        let text = '';
        try { text = await outputView.getText(); } catch (_) {}
        // Close the panel best-effort; a notification popup may intercept the
        // click, but we already have the text so don't let that lose it.
        try { await bottomBar.toggle(false); } catch (_) {}
        return text;
    } catch (_) {
        try { await bottomBar.toggle(false); } catch (__) {}
        return null;
    }
}

/**
 * Wrap readOpenJMLOutput() in a hard timeout so a hung bottom bar doesn't
 * stall the suite.  Returns '' on timeout or error.
 */
async function readOutputSafe() {
    try {
        return await Promise.race([
            readOpenJMLOutput(),
            new Promise((_, rej) =>
                setTimeout(() => rej(new Error('timeout')), 10_000)),
        ]) || '';
    } catch (_) { return ''; }
}

/**
 * Poll the OpenJML output channel until every string in requiredStrings
 * appears in the text, or until deadlineMs is reached.
 * Returns the last captured output text.
 */
async function waitForOutput(requiredStrings, deadlineMs) {
    const driver = VSBrowser.instance.driver;
    let outputText = '';
    while (Date.now() < deadlineMs) {
        await driver.sleep(3_000);
        const text = await readOutputSafe();
        outputText = text || outputText;
        if (requiredStrings.every(s => outputText.includes(s))) break;
    }
    return outputText;
}

/**
 * Return true if the OpenJML output channel exists (extension is active).
 */
async function hasOpenJMLChannel() {
    const text = await readOutputSafe();
    return text !== null;
}

/**
 * Open a file resource and retry openEditor() until the tab is visible.
 * Returns the editor, or throws if it never appears within the retry limit.
 */
async function openAndFocusFile(filePath) {
    const driver    = VSBrowser.instance.driver;
    const fileName  = require('path').basename(filePath);
    await VSBrowser.instance.openResources(filePath);
    for (let attempt = 0; attempt < 8; attempt++) {
        await driver.sleep(1_000);
        try {
            return await new EditorView().openEditor(fileName);
        } catch (_) {}
    }
    throw new Error(`Editor tab '${fileName}' did not appear after openResources`);
}

/**
 * Poll the server log file (OPENJML_LSP_LOG) for a required string.
 * Returns the log content when all strings are found, or the last content
 * seen when the deadline is reached.
 *
 * Use this instead of waitForOutput() for server-side log messages, since
 * getText() from the VS Code output panel no longer works in VS Code 1.117+.
 */
async function waitForServerLog(requiredStrings, deadlineMs) {
    const driver = VSBrowser.instance.driver;
    let text = '';
    while (Date.now() < deadlineMs) {
        try { text = fs.readFileSync(SERVER_LOG, 'utf8'); } catch (_) {}
        if (requiredStrings.every(s => text.includes(s))) return text;
        await driver.sleep(1_000);
    }
    return text;
}

// ── Explorer sidebar ──────────────────────────────────────────────────────────

/**
 * Open the Explorer sidebar and return the first DefaultTreeSection.
 * Returns null if the sidebar cannot be opened within the retry limit.
 */
async function getExplorerSection() {
    const driver    = VSBrowser.instance.driver;
    const workbench = new Workbench();
    try { await workbench.executeCommand('workbench.view.explorer'); } catch (_) {}
    await driver.sleep(1_000);

    const content = new SideBarView().getContent();
    for (let attempt = 0; attempt < 5; attempt++) {
        try {
            const sections = await content.getSections();
            if (sections.length > 0) return sections[0];
        } catch (_) {}
        await driver.sleep(800);
    }
    return null;
}

/**
 * Find a tree item by label inside section, retrying on stale DOM.
 * Returns null if not found after retries.
 */
async function findExplorerItem(section, label) {
    const driver = VSBrowser.instance.driver;
    for (let attempt = 0; attempt < 4; attempt++) {
        try {
            const item = await section.findItem(label);
            if (item) return item;
        } catch (_) {}
        await driver.sleep(500);
    }
    return null;
}

// ── Context menus ─────────────────────────────────────────────────────────────

/**
 * Right-click element and click the first menu item whose label includes
 * labelSubstring (and does not include any of the excludeSubstrings).
 * Returns true if the item was found and clicked, false otherwise.
 * Dismisses any open menu before returning false.
 */
async function invokeContextMenuItem(element, labelSubstring,
                                     excludeSubstrings = []) {
    const driver = VSBrowser.instance.driver;
    for (let attempt = 0; attempt < 3; attempt++) {
        try {
            await driver.actions().contextClick(element).perform();
            await driver.sleep(800);
            const items = await driver.findElements(
                { css: '.monaco-menu .action-label' });
            for (const item of items) {
                const label = await item.getText().catch(() => '');
                if (label.includes(labelSubstring)
                        && excludeSubstrings.every(ex => !label.includes(ex))) {
                    await item.click();
                    return true;
                }
            }
        } catch (_) {}
        try { await driver.actions().sendKeys(Key.ESCAPE).perform(); } catch (_) {}
        await driver.sleep(500);
    }
    return false;
}

// ── Command palette ───────────────────────────────────────────────────────────

/**
 * Execute a VS Code command by name via the command palette.
 * Returns true on success, false if the command throws or is not found.
 */
async function runCommand(name) {
    try {
        await new Workbench().executeCommand(name);
        return true;
    } catch (_) {
        return false;
    }
}

// ── Suite lifecycle ───────────────────────────────────────────────────────────

/**
 * Standard end-of-suite cleanup.  Call from an after() hook.
 *
 *   1. Close all open editor tabs.
 *   2. Clear the OpenJML output channel.
 *   3. Optionally run openjml.clearAndReindex to reset server-side state.
 *
 * All steps are best-effort; failures never mask real test failures.
 *
 * @param {boolean} [reindex=false]  Pass true for suites that ran ESC/check.
 */
async function suiteTeardown(reindex = false) {
    const driver = VSBrowser.instance.driver;

    // Wrap any promise with a hard timeout so a hung Selenium call doesn't
    // stall the whole suite teardown (and trigger a Mocha hook timeout).
    const withTimeout = (p, ms) =>
        Promise.race([p, new Promise(r => setTimeout(r, ms))]).catch(() => {});

    // 1. Close all editor tabs.
    await withTimeout(new EditorView().closeAllEditors(), 5_000);
    await driver.sleep(300);

    // 2. Clear the OpenJML output channel.
    try {
        const bottomBar  = new BottomBarPanel();
        await withTimeout(bottomBar.toggle(true), 3_000);
        await driver.sleep(300);
        const outputView = await withTimeout(bottomBar.openOutputView(), 3_000);

        if (outputView) {
            let channels = [];
            for (let attempt = 0; attempt < 3; attempt++) {
                try { channels = await withTimeout(outputView.getChannelNames(), 2_000) || []; break; }
                catch (_) { await driver.sleep(300); }
            }
            const ch = channels.find(c => c.includes('OpenJML'));
            if (ch) {
                await withTimeout(outputView.selectChannel(ch), 2_000);
                await driver.sleep(200);
                await withTimeout(runCommand('workbench.output.action.clearOutput'), 2_000);
                await driver.sleep(200);
            }
        }
        await withTimeout(bottomBar.toggle(false), 3_000);
    } catch (_) {}

    // 3. Optionally reset server-side diagnostics and caches.
    if (reindex) {
        await withTimeout(runCommand('openjml.clearAndReindex'), 5_000);
        await driver.sleep(500);
    }
}

// ── Server readiness ──────────────────────────────────────────────────────────

// Cached across all suites in the same test run (same Node.js process).
// Set to true once "server started" is seen; subsequent calls return immediately.
let _serverReady = false;

/**
 * Wait until the OpenJML LSP server has started, detected by the appearance of
 * "[configuration]" in the server log file.  Returns true when ready, false on
 * timeout.
 *
 * The log file path is set via openjml.serverLogFile (written by runner.js) and
 * passed to the server process as OPENJML_LSP_LOG.  runner.js deletes any stale
 * log before launching VS Code, so reading this file always reflects the current run.
 *
 * Result is cached: once the server is confirmed running, all subsequent calls
 * return true immediately.
 *
 * @param {number} [timeoutMs=120_000]
 * @returns {Promise<boolean>}
 */
async function waitForServer(timeoutMs = 120_000) {
    if (_serverReady) return true;

    const driver   = VSBrowser.instance.driver;
    const deadline = Date.now() + timeoutMs;

    // Poll the server log file (path from OPENJML_LSP_LOG, set by runner.js) for
    // the [configuration] marker the server writes after workspace/initialized.
    // This avoids relying on getText() from the VS Code output panel, which stopped
    // working in VS Code 1.117 when the renderer switched to xterm.js.
    while (Date.now() < deadline) {
        try {
            const text = fs.readFileSync(SERVER_LOG, 'utf8');
            if (text.includes('[configuration]')) {
                _serverReady = true;
                return true;
            }
        } catch (_) {
            // File not yet created — server hasn't started writing yet.
        }
        await driver.sleep(2_000);
    }
    return false;
}

// ── Skip helpers ──────────────────────────────────────────────────────────────

/**
 * Log a SKIP reason and immediately skip the current Mocha test.
 *
 * Because Mocha's this.skip() throws a Pending error, execution stops at the
 * throw — no 'return' statement is needed after calling noteSkip().
 *
 * Usage:
 *   if (!serverRunning) noteSkip(this, 'server not running');
 *   // code here is unreachable when skipping
 *
 * @param {Mocha.Context} ctx   The test context — pass `this` from the test.
 * @param {string}        reason  Human-readable reason shown in the test log.
 */
function noteSkip(ctx, reason) {
    console.log('    [SKIP] ' + reason);
    ctx.skip();
}

module.exports = {
    readOpenJMLOutput,
    readOutputSafe,
    waitForOutput,
    waitForServerLog,
    hasOpenJMLChannel,
    waitForServer,
    openAndFocusFile,
    getExplorerSection,
    findExplorerItem,
    invokeContextMenuItem,
    runCommand,
    suiteTeardown,
    noteSkip,
};
