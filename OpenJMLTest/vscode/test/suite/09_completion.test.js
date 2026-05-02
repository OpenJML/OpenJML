'use strict';
/**
 * Suite 09: Code Completion
 *
 * Verifies that the OpenJML language server provides completion items inside
 * JML annotation comments.  Completion is triggered via ContentAssist
 * (vscode-extension-tester's wrapper for Ctrl+Space) with the cursor
 * positioned inside a //@ annotation line.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, closeSecondarySidebar, dismissNotifications, openAndFocusFile } = require('./helpers');

const SAMPLE_JAVA     = path.resolve(__dirname, '../../resources/Sample.java');
// The visible slice of the completion list varies by run; include early-alphabet
// JML keywords that reliably appear regardless of which portion is rendered.
const JML_KEYWORDS    = ['requires', 'ensures', 'pure', 'assignable', 'modifies',
                         'after', 'always', 'applies'];
const JML_EXPRESSIONS = ['\\result', '\\old'];

/**
 * Position the cursor at (line, col) and trigger content assist.
 * Returns the list of item labels.  Throws on any failure.
 */
async function getCompletionItems(editor, line, col) {
    const driver = VSBrowser.instance.driver;
    // Re-obtain a fresh editor reference — the TextEditor DOM element can become
    // stale after Check JML rewrites code lenses, causing ElementNotInteractableError.
    try { editor = await new EditorView().openEditor('Sample.java'); } catch (_) {}
    try { await editor.click(); } catch (_) {}
    // Wait for the focusFile debounce + any server notification to fire and appear.
    // The extension sends focusFile on onDidChangeActiveTextEditor (debounced ~200 ms);
    // if the server responds with an error notification, we must dismiss it AFTER it
    // appears, not before.
    await driver.sleep(1_500);
    await dismissNotifications(driver);
    await driver.sleep(300);
    await editor.moveCursor(line, col);
    await VSBrowser.instance.driver.sleep(500);
    const assist = await editor.toggleContentAssist(true);
    assert.ok(assist, 'ContentAssist API returned null — not supported in this vscode-extension-tester version');
    await VSBrowser.instance.driver.sleep(2_000);
    const items  = await assist.getItems();
    const labels = await Promise.all(items.map(i => i.getLabel().catch(() => '')));
    await editor.toggleContentAssist(false).catch(() => {});
    return labels.filter(Boolean);
}

describe('Code Completion', function () {
    this.timeout(90_000);

    let editor;

    before(async function () {
        const driver = VSBrowser.instance.driver;
        await VSBrowser.instance.waitForWorkbench(20_000);
        await closeSecondarySidebar(driver);
        editor = await openAndFocusFile(SAMPLE_JAVA);
        await runCommand('OpenJML: Check JML');
        await driver.sleep(3_000);
        // Dismiss any notifications produced by Check JML (e.g. "no method found",
        // JML errors) — they can cover the editor and cause ElementNotInteractableError.
        await dismissNotifications(driver);
        await driver.sleep(300);
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

    // Sample.java line 7:  //@ requires x >= 0;
    // Sample.java line 8:  //@ ensures \result >= 0;
    // Sample.java line 9:  //@ ensures \result == x || \result == -x;

    it('content assist API is available in a Java editor', async function () {
        const driver = VSBrowser.instance.driver;
        // Re-obtain fresh reference in case Check JML rewrote the editor DOM.
        try { editor = await new EditorView().openEditor('Sample.java'); } catch (_) {}
        try { await editor.click(); } catch (_) {}
        // Wait for focusFile debounce + any server notification before dismissing.
        await driver.sleep(1_500);
        await dismissNotifications(driver);
        await driver.sleep(300);
        await editor.moveCursor(7, 9);
        await VSBrowser.instance.driver.sleep(500);
        const assist = await editor.toggleContentAssist(true);
        assert.ok(assist, 'ContentAssist API returned null — not supported in this vscode-extension-tester version');
        await VSBrowser.instance.driver.sleep(500);
        await editor.toggleContentAssist(false).catch(() => {});
    });

    it('JML keywords appear in completion inside a //@ comment', async function () {
        // Cursor at start of 'requires' on line 7 (col 9, 1-based, after '    //@ ')
        const items = await getCompletionItems(editor, 7, 9);
        assert.ok(items.length > 0,
            'No completion items returned — server may not implement textDocument/completion');
        const found = JML_KEYWORDS.filter(kw => items.some(l => l.includes(kw)));
        assert.ok(found.length > 0,
            `Expected JML keywords in completions but found none. Items: ${items.slice(0, 15).join(', ')}`);
    });

    it('\\result and \\old appear in completion inside a JML postcondition', async function () {
        // Cursor inside '//@ ensures \result >= 0;' on line 8.
        // Col 17 = '\', col 20 = inside 'result' — triggers \result completion.
        const items = await getCompletionItems(editor, 8, 20);
        assert.ok(items.length > 0,
            'No completion items returned — server may not implement textDocument/completion');
        const found = JML_EXPRESSIONS.filter(kw => items.some(l => l.includes(kw)));
        assert.ok(found.length > 0,
            `Expected \\result/\\old in completions but found none. Items: ${items.slice(0, 15).join(', ')}`);
    });
});
