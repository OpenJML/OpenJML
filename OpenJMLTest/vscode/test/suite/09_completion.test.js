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
const { suiteTeardown, runCommand } = require('./helpers');

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
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(2_000);
        editor = await new EditorView().openEditor('Sample.java');
        await runCommand('OpenJML: Check JML');
        await VSBrowser.instance.driver.sleep(3_000);
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

    // Sample.java line 7:  //@ requires x >= 0;
    // Sample.java line 8:  //@ ensures \result >= 0;
    // Sample.java line 9:  //@ ensures \result == x || \result == -x;

    it('content assist API is available in a Java editor', async function () {
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
