'use strict';
/**
 * Suite 10: Code Folding
 *
 * Verifies that foldable regions in JmlFold.java (JML block comments and Java
 * method bodies) can be collapsed and restored.
 *
 * In VS Code 1.118+ the fold gutter chevrons are no longer persistent DOM
 * elements — they are only rendered while the mouse hovers over the exact
 * line, making CSS-selector-based detection unreliable.  This suite therefore
 * tests folding BEHAVIOUR via the editor.foldAll / editor.unfoldAll commands
 * and the resulting change in the number of rendered view-lines.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, openAndFocusFile, closeSecondarySidebar } = require('./helpers');

const JML_FOLD_JAVA = path.resolve(__dirname, '../../resources/JmlFold.java');

/** Returns the number of currently rendered view-line elements in the active Monaco editor. */
async function visibleLineCount(driver) {
    const els = await driver.findElements({ css: '.monaco-editor .view-lines .view-line' })
        .catch(() => []);
    return els.length;
}

describe('Code Folding', function () {
    this.timeout(180_000);

    let editor;

    before(async function () {
        this.timeout(120_000);
        const driver = VSBrowser.instance.driver;
        await VSBrowser.instance.waitForWorkbench(20_000);
        await closeSecondarySidebar(driver);
        editor = await openAndFocusFile(JML_FOLD_JAVA);
        // Ensure all regions are expanded before tests start.
        await runCommand('editor.unfoldAll');
        await driver.sleep(1_000);
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

    it('fold controls appear in the gutter for multi-line JML blocks', async function () {
        const driver = VSBrowser.instance.driver;

        // Poll until Monaco has rendered view-lines (initial render can be slow
        // on a fresh VS Code install while JDT is starting in the background).
        const deadline = Date.now() + 8_000;
        let totalLines = 0;
        while (Date.now() < deadline) {
            try { await editor.click(); } catch (_) {}
            await driver.sleep(500);
            totalLines = await visibleLineCount(driver);
            if (totalLines > 0) break;
        }
        assert.ok(totalLines >= 5,
            `JmlFold.java must have at least 5 visible lines; got ${totalLines}`);

        // Fold all regions and verify that fewer lines are rendered — this proves
        // VS Code has at least one foldable region (method body or block comment).
        await runCommand('editor.foldAll');
        await driver.sleep(800);
        const afterFold = await visibleLineCount(driver);

        // Restore so the next test starts from a known state.
        await runCommand('editor.unfoldAll');
        await driver.sleep(500);

        assert.ok(afterFold < totalLines,
            `Expected fewer visible lines after Fold All `
            + `(before=${totalLines}, after=${afterFold}) — no foldable regions found`);
    });

    it('clicking a fold control collapses a JML block', async function () {
        const driver = VSBrowser.instance.driver;
        try { await editor.click(); } catch (_) {}
        await driver.sleep(300);

        const before = await visibleLineCount(driver);

        // Fold all regions.
        await runCommand('editor.foldAll');
        await driver.sleep(800);

        const afterFold = await visibleLineCount(driver);
        assert.ok(afterFold < before,
            `Expected fewer lines after folding (before=${before}, after=${afterFold})`);
    });

    it('unfolding restores the JML block lines', async function () {
        const driver = VSBrowser.instance.driver;

        // Start from fully folded state (previous test left it folded).
        const folded = await visibleLineCount(driver);

        await runCommand('editor.unfoldAll');

        // Poll until the line count stabilises above the folded count.
        const deadline = Date.now() + 5_000;
        let unfolded = folded;
        while (Date.now() < deadline) {
            await driver.sleep(400);
            unfolded = await visibleLineCount(driver);
            if (unfolded > folded) break;
        }

        assert.ok(unfolded > folded,
            `Expected more lines after Unfold All (folded=${folded}, unfolded=${unfolded})`);
    });
});
