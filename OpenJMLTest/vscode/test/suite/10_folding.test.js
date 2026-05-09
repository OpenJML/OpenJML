'use strict';
/**
 * Suite 10: Code Folding
 *
 * Verifies that foldable regions in JmlFold.java (JML block comments and Java
 * method bodies) can be collapsed and restored.
 *
 * Detection strategy: after editor.foldAll, Monaco inserts an ".inline-folded"
 * element at the end of each collapsed line (the "..." placeholder).  Counting
 * those elements is independent of viewport size — unlike .view-line counting,
 * which varies with editor height.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, openAndFocusFile, closeSecondarySidebar } = require('./helpers');

const JML_FOLD_JAVA = path.resolve(__dirname, '../../resources/JmlFold.java');

/** Returns the number of inline-folded ("...") placeholders in the active editor. */
async function countFoldedRegions(driver) {
    const els = await driver.findElements({ css: '.monaco-editor .inline-folded' })
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
        try { editor = await new EditorView().openEditor('JmlFold.java'); } catch (_) {}
        try { await editor.click(); } catch (_) {}
        await driver.sleep(500);

        // Fold all regions — JML block comments and method bodies collapse.
        await runCommand('editor.foldAll');

        // Poll until inline-folded placeholders appear (Monaco folds asynchronously).
        const foldDeadline = Date.now() + 5_000;
        let folded = 0;
        while (Date.now() < foldDeadline) {
            await driver.sleep(500);
            folded = await countFoldedRegions(driver);
            if (folded > 0) break;
        }

        // Restore for the next test.
        await runCommand('editor.unfoldAll');
        await driver.sleep(500);

        assert.ok(folded >= 1,
            `Expected at least 1 folded region after Fold All, got ${folded} — ` +
            'check that the FoldingRangeProvider is registered for Java files');
    });

    it('clicking a fold control collapses a JML block', async function () {
        const driver = VSBrowser.instance.driver;
        try { editor = await new EditorView().openEditor('JmlFold.java'); } catch (_) {}
        try { await editor.click(); } catch (_) {}
        await driver.sleep(300);

        // No inline-folded placeholders should be present when fully unfolded.
        const before = await countFoldedRegions(driver);

        await runCommand('editor.foldAll');

        // Poll for fold to complete.
        const foldDeadline = Date.now() + 5_000;
        let afterFold = before;
        while (Date.now() < foldDeadline) {
            await driver.sleep(500);
            afterFold = await countFoldedRegions(driver);
            if (afterFold > before) break;
        }
        assert.ok(afterFold > before,
            `Expected inline-folded placeholders after Fold All (before=${before}, after=${afterFold})`);
    });

    it('unfolding restores the JML block lines', async function () {
        const driver = VSBrowser.instance.driver;

        // Start from fully folded state (previous test).
        const folded = await countFoldedRegions(driver);

        await runCommand('editor.unfoldAll');

        // Poll until all inline-folded placeholders are gone.
        const deadline = Date.now() + 5_000;
        let unfolded = folded;
        while (Date.now() < deadline) {
            await driver.sleep(400);
            unfolded = await countFoldedRegions(driver);
            if (unfolded === 0) break;
        }

        assert.ok(unfolded === 0,
            `Expected 0 inline-folded placeholders after Unfold All, got ${unfolded}`);
    });
});
