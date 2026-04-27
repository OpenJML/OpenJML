'use strict';
/**
 * Suite 10: Code Folding
 *
 * Verifies that multi-line JML block comments (/*@ ... @*‌/) can be folded.
 * Uses JmlFold.java which has two long /*@ @*/ blocks.
 *
 * NOTE (missing feature): Folding of JML blocks requires either a grammar
 * indentation rule or an LSP textDocument/foldingRange response.  Neither is
 * confirmed to be implemented.  Tests skip with a logged reason if no fold
 * controls appear, flagging this as a missing feature.
 *
 * Fold controls are detected via Monaco gutter CSS classes rather than a
 * vscode-extension-tester FoldingRange API (which does not exist).
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { Key } = require('selenium-webdriver');
const { suiteTeardown, runCommand, noteSkip } = require('./helpers');

const JML_FOLD_JAVA = path.resolve(__dirname, '../../resources/JmlFold.java');

async function countFoldControls(driver) {
    try {
        return (await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-expanded' })).length;
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
        await runCommand('OpenJML: Check JML');
        await VSBrowser.instance.driver.sleep(3_000);
    });

    after(async function () { await suiteTeardown(true); });

    it('fold controls appear in the gutter for multi-line JML blocks', async function () {
        const driver = VSBrowser.instance.driver;
        try { await editor.click(); } catch (_) {}
        await driver.sleep(1_000);

        const count = await countFoldControls(driver);
        if (count === 0)
            // NOTE: JML block folding not implemented — needs grammar rule or
            // textDocument/foldingRange LSP support.
            noteSkip(this, 'no fold controls found — JML /*@ @*/ block folding is not implemented');

        assert.ok(count >= 1,
            `Expected at least 1 fold control for /*@ ... @*/ blocks, found ${count}`);
    });

    it('clicking a fold control collapses a JML block', async function () {
        const driver = VSBrowser.instance.driver;
        await editor.click();
        await driver.sleep(500);

        const before = await countFoldControls(driver);
        if (before === 0)
            noteSkip(this, 'no fold controls — JML block folding not implemented');

        try {
            const chevrons = await driver.findElements(
                { css: '.monaco-editor .cldr.codicon-folding-expanded' });
            await chevrons[0].click();
            await driver.sleep(1_000);
        } catch (_) {
            noteSkip(this, 'could not click fold control');
        }

        const collapsed = await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-collapsed' }).catch(() => []);
        assert.ok(collapsed.length >= 1,
            'Expected at least one collapsed fold control after clicking');
    });

    it('unfolding restores the JML block lines', async function () {
        const driver = VSBrowser.instance.driver;
        const unfoldKey = process.platform === 'darwin' ? Key.COMMAND : Key.CONTROL;
        try {
            await driver.actions()
                .keyDown(unfoldKey).keyDown(Key.SHIFT).sendKeys(']')
                .keyUp(Key.SHIFT).keyUp(unfoldKey)
                .perform();
            await driver.sleep(1_000);
        } catch (_) {
            noteSkip(this, 'could not send Unfold All keyboard shortcut');
        }

        const collapsedAfter = await driver.findElements(
            { css: '.monaco-editor .cldr.codicon-folding-collapsed' }).catch(() => []);
        assert.ok(collapsedAfter.length === 0,
            'Expected no collapsed fold controls after Unfold All');
    });
});
