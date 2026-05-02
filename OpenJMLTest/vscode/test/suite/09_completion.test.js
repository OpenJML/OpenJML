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
const { Key } = require('selenium-webdriver');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, closeSecondarySidebar, dismissNotifications, openAndFocusFile } = require('./helpers');

/**
 * Position the cursor at (line, col) using the VS Code Go-to-Line widget
 * (Ctrl+G → "line:col" → Enter).
 *
 * This bypasses TextEditor.moveCursor() which internally calls getNumberOfLines()
 * via a DOM click that fails with ElementNotInteractableError when a notification
 * is covering the editor.  Keyboard-driven navigation is not affected by overlays.
 */
async function gotoLineByKeyboard(driver, line, col) {
    await driver.actions().keyDown(Key.CONTROL).sendKeys('g').keyUp(Key.CONTROL).perform();
    await driver.sleep(400);
    await driver.actions().sendKeys(`${line}:${col}`).perform();
    await driver.sleep(200);
    await driver.actions().sendKeys(Key.RETURN).perform();
    await driver.sleep(300);
}

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
    // Focus the Monaco editor's raw textarea — more reliable than editor.click()
    // when the TextEditor reference is stale after code lenses rewrite the DOM.
    try {
        const textareas = await driver.findElements({ css: '.monaco-editor .inputarea' });
        if (textareas.length > 0) await textareas[0].click();
    } catch (_) { try { await editor.click(); } catch (__) {} }
    // Wait for focusFile debounce + server notification, then dismiss.
    await driver.sleep(1_500);
    await dismissNotifications(driver);
    await driver.sleep(300);
    await gotoLineByKeyboard(driver, line, col);
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
        try {
            const textareas = await driver.findElements({ css: '.monaco-editor .inputarea' });
            if (textareas.length > 0) await textareas[0].click();
        } catch (_) { try { await editor.click(); } catch (__) {} }
        await driver.sleep(1_500);
        await dismissNotifications(driver);
        await driver.sleep(300);
        await gotoLineByKeyboard(driver, 7, 9);
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
