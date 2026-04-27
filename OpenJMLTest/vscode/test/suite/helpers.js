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

// ── Output channel ────────────────────────────────────────────────────────────

/**
 * Open (or focus) the OpenJML output channel and return its current text.
 * Returns null if the channel does not exist yet.
 * Leaves the bottom bar closed.
 */
async function readOpenJMLOutput() {
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
        await bottomBar.toggle(false);
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

    // 1. Close all editor tabs.
    try { await new EditorView().closeAllEditors(); } catch (_) {}
    await driver.sleep(500);

    // 2. Clear the OpenJML output channel.
    try {
        const bottomBar  = new BottomBarPanel();
        await bottomBar.toggle(true);
        await driver.sleep(500);
        const outputView = await bottomBar.openOutputView();

        let channels = [];
        for (let attempt = 0; attempt < 4; attempt++) {
            try { channels = await outputView.getChannelNames(); break; }
            catch (_) { await driver.sleep(500); }
        }
        const ch = channels.find(c => c.includes('OpenJML'));
        if (ch) {
            await outputView.selectChannel(ch);
            await driver.sleep(300);
            await runCommand('workbench.output.action.clearOutput');
            await driver.sleep(300);
        }
        await bottomBar.toggle(false);
    } catch (_) {}

    // 3. Optionally reset server-side diagnostics and caches.
    if (reindex) {
        await runCommand('openjml.clearAndReindex');
        await driver.sleep(1_000);
    }
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
    hasOpenJMLChannel,
    getExplorerSection,
    findExplorerItem,
    invokeContextMenuItem,
    runCommand,
    suiteTeardown,
    noteSkip,
};
