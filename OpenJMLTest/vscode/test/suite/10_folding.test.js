'use strict';
/**
 * Suite 10: Code Folding
 *
 * Verifies that multi-line JML block comments (/*@ ... @*\/) can be folded.
 * Uses JmlFold.java which has two long /*@ @*\/ blocks.
 *
 * Fold controls are detected via Monaco gutter CSS classes rather than a
 * vscode-extension-tester FoldingRange API (which does not exist).
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, openAndFocusFile } = require('./helpers');

const JML_FOLD_JAVA = path.resolve(__dirname, '../../resources/JmlFold.java');

/** Returns count of expanded fold chevrons in the Monaco gutter. */
async function countFoldControls(driver) {
    const els = await driver.findElements(
        { css: '.monaco-editor .cldr.codicon-folding-expanded' });
    return els.length;
}

describe('Code Folding', function () {
    this.timeout(90_000);

    let editor;

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        editor = await openAndFocusFile(JML_FOLD_JAVA);
        await runCommand('OpenJML: Check JML');
        await VSBrowser.instance.driver.sleep(3_000);
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

    it('fold controls appear in the gutter for multi-line JML blocks', async function () {
        const driver = VSBrowser.instance.driver;
        try { await editor.click(); } catch (_) {}
        await driver.sleep(1_000);

        const count = await countFoldControls(driver);
        assert.ok(count >= 1,
            `Expected at least 1 fold control for /*@ ... @*/ blocks, found ${count}`);
    });

    it('clicking a fold control collapses a JML block', async function () {
        const driver = VSBrowser.instance.driver;
        await editor.click();
        await driver.sleep(500);

        const chevrons = await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-expanded' });
        assert.ok(chevrons.length >= 1,
            `Expected at least 1 fold control to click, found ${chevrons.length}`);

        await chevrons[0].click();
        await driver.sleep(1_000);

        const collapsed = await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-collapsed' }).catch(() => []);
        assert.ok(collapsed.length >= 1,
            'Expected at least one collapsed fold control after clicking — codicon-folding-collapsed class not found');
    });

    it('unfolding restores the JML block lines', async function () {
        await runCommand('editor.unfoldAll');

        const driver = VSBrowser.instance.driver;
        const deadline = Date.now() + 5_000;
        let collapsedAfter = [];
        while (Date.now() < deadline) {
            await driver.sleep(500);
            collapsedAfter = await driver.findElements(
                { css: '.monaco-editor .cldr.codicon-folding-collapsed' }).catch(() => []);
            if (collapsedAfter.length === 0) break;
        }
        assert.ok(collapsedAfter.length === 0,
            'Expected no collapsed fold controls after Unfold All');
    });
});
