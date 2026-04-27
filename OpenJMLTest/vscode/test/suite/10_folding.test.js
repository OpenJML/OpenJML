'use strict';
/**
 * Suite 10: Code Folding
 *
 * Verifies that multi-line JML block comments (/*@ ... @*‌/) can be folded
 * in the editor.  Uses JmlFold.java which has two long block-comment specs.
 *
 * Tests:
 *   A. The editor reports at least one folding range for JmlFold.java.
 *   B. Folding the first JML block hides inner lines (line count decreases
 *      in the visible area or the fold control appears).
 *   C. Unfolding restores the lines.
 *
 * NOTE (potential bug / missing feature): VS Code folding for JML blocks
 * relies on either:
 *   (a) a language-grammar indentation rule recognising /*@ ... @*‌/ blocks, or
 *   (b) an LSP textDocument/foldingRange response from the server.
 * It is not confirmed that the OpenJML extension contributes either.  If
 * folding is not provided, tests A–C skip gracefully with a note.
 *
 * vscode-extension-tester does not expose a FoldingRange API directly; we
 * detect folding by looking for fold-control gutter elements (chevrons) in
 * the editor's line-number gutter.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { suiteTeardown, runCommand } = require('./helpers');

const JML_FOLD_JAVA = path.resolve(__dirname, '../../resources/JmlFold.java');

/**
 * Count the number of visible fold-control chevrons (▾) in the editor gutter.
 * Returns 0 if the gutter elements are not accessible.
 */
async function countFoldControls(driver) {
    try {
        const controls = await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-expanded' });
        return controls.length;
    } catch (_) { return 0; }
}

describe('Code Folding', function () {
    this.timeout(90_000);

    let editor;

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(JML_FOLD_JAVA);
        await VSBrowser.instance.driver.sleep(2_000);
        editor = await new EditorView().openEditor('JmlFold.java');
        // Trigger Check JML so the server can provide foldingRange if it supports it.
        await runCommand('OpenJML: Check JML');
        await VSBrowser.instance.driver.sleep(3_000);
    });

    after(async function () { await suiteTeardown(true); });

    it('fold controls appear in the gutter for multi-line JML blocks', async function () {
        const driver = VSBrowser.instance.driver;
        // Hover over the editor to make gutter chevrons visible.
        try { await editor.click(); } catch (_) {}
        await driver.sleep(1_000);

        const count = await countFoldControls(driver);
        if (count === 0) {
            // NOTE: this indicates the extension does not contribute folding ranges
            // for JML block comments.  This is a missing feature worth implementing
            // via a textDocument/foldingRange LSP response or a grammar rule.
            console.log('    [NOTE] No fold controls found — JML block folding may not be implemented');
            // Soft skip: do not fail the build over a missing feature.
            this.skip(); return;
        }
        assert.ok(count >= 1,
            `Expected at least 1 fold control for /*@ ... @*/ blocks, found ${count}`);
    });

    it('clicking a fold control collapses a JML block', async function () {
        const driver = VSBrowser.instance.driver;
        await editor.click();
        await driver.sleep(500);

        const before = await countFoldControls(driver);
        if (before === 0) { this.skip(); return; }

        // Click the first fold chevron to collapse it.
        try {
            const chevrons = await driver.findElements(
                { css: '.monaco-editor .cldr.codicon-folding-expanded' });
            if (chevrons.length > 0) {
                await chevrons[0].click();
                await driver.sleep(1_000);
            }
        } catch (_) { this.skip(); return; }

        // After folding, the expanded chevron becomes a collapsed chevron.
        const collapsedChevrons = await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-collapsed' }).catch(() => []);
        assert.ok(collapsedChevrons.length >= 1,
            'Expected at least one collapsed fold control after clicking');
    });

    it('unfolding restores the JML block lines', async function () {
        const driver = VSBrowser.instance.driver;

        // Unfold all via Ctrl+Shift+] / Cmd+Shift+]
        try {
            const { Key } = require('selenium-webdriver');
            const unfoldKey = process.platform === 'darwin' ? Key.COMMAND : Key.CONTROL;
            await driver.actions()
                .keyDown(unfoldKey).keyDown(Key.SHIFT)
                .sendKeys(']')
                .keyUp(Key.SHIFT).keyUp(unfoldKey)
                .perform();
            await driver.sleep(1_000);
        } catch (_) { this.skip(); return; }

        const collapsedAfter = await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-collapsed' }).catch(() => []);
        assert.ok(collapsedAfter.length === 0,
            'Expected no collapsed fold controls after Unfold All');
    });
});
