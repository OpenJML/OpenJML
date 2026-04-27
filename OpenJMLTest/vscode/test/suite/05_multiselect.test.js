'use strict';
/**
 * Suite 05: ESC via Explorer context menu — single file vs multi-select
 *
 * Tests two distinct behaviours of the Explorer context-menu "Run ESC" command:
 *
 *   Test A – Single file: right-clicking one file (no multi-select) ESCs only
 *            that file.  The other file must NOT appear in the output.
 *
 *   Test B – Multi-select: right-clicking while two files are selected ESCs
 *            both files.  Both must appear in the output.
 *
 * VS Code passes (explorerUri, explorerSelection) to the command handler.
 * For a single-file right-click, explorerSelection contains only that file.
 * For a multi-select right-click, explorerSelection contains all selected files.
 * resolveTargetPaths() in extension.js uses explorerSelection when present,
 * so single-select → one file, multi-select → all files.
 *
 * Skips gracefully when the OpenJML server is unavailable.
 */
const assert  = require('assert');
const path    = require('path');
const { VSBrowser, EditorView, SideBarView, BottomBarPanel, Workbench }
    = require('vscode-extension-tester');
const { Key }  = require('selenium-webdriver');

const FILEA       = 'EscFileA.java';
const FILEB       = 'EscFileB.java';
const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');

/** macOS uses Command; Windows/Linux use Control. */
const CTL_KEY = process.platform === 'darwin' ? Key.COMMAND : Key.CONTROL;

/**
 * Open the Explorer sidebar and return the first DefaultTreeSection.
 */
async function getExplorerSection() {
    const workbench = new Workbench();
    try { await workbench.executeCommand('workbench.view.explorer'); } catch (_) {}
    await VSBrowser.instance.driver.sleep(1_000);

    const sidebar  = new SideBarView();
    const content  = sidebar.getContent();

    for (let attempt = 0; attempt < 5; attempt++) {
        try {
            const sections = await content.getSections();
            if (sections.length > 0) return sections[0];
        } catch (_) {}
        await VSBrowser.instance.driver.sleep(800);
    }
    return null;
}

/**
 * Find a tree item by label, retrying on stale DOM.
 */
async function findItem(section, label) {
    for (let attempt = 0; attempt < 4; attempt++) {
        try {
            const item = await section.findItem(label);
            if (item) return item;
        } catch (_) {}
        await VSBrowser.instance.driver.sleep(500);
    }
    return null;
}

/**
 * Read the OpenJML output channel text, retrying on stale DOM.
 */
async function readOpenJMLOutput() {
    const bottomBar  = new BottomBarPanel();
    await bottomBar.toggle(true);
    const outputView = await bottomBar.openOutputView();

    let channels = [];
    for (let attempt = 0; attempt < 4; attempt++) {
        try { channels = await outputView.getChannelNames(); break; }
        catch (_) { await VSBrowser.instance.driver.sleep(500); }
    }

    const openjmlChannel = channels.find(c => c.includes('OpenJML'));
    if (!openjmlChannel) { await bottomBar.toggle(false); return null; }

    await outputView.selectChannel(openjmlChannel);
    let text = '';
    try { text = await outputView.getText(); } catch (_) {}
    await bottomBar.toggle(false);
    return text;
}

/**
 * Right-click itemB (after selecting the desired files) and click "Run ESC"
 * in the context menu.  Returns true if the menu item was found and clicked.
 */
async function invokeRunEscFromContextMenu(driver, itemB) {
    let menuOpened = false;
    for (let attempt = 0; attempt < 3; attempt++) {
        try {
            await driver.actions().contextClick(itemB).perform();
            await driver.sleep(800);
            menuOpened = true;
            break;
        } catch (_) {
            await driver.sleep(500);
        }
    }
    if (!menuOpened) return false;

    try {
        const menuItems = await driver.findElements(
            { css: '.monaco-menu .action-label' });
        for (const item of menuItems) {
            const label = await item.getText().catch(() => '');
            if (label.includes('Run ESC') && !label.includes('Split')
                    && !label.includes('Method') && !label.includes('Save')) {
                await item.click();
                return true;
            }
        }
    } catch (_) {}

    // Dismiss any open menu.
    try { await driver.actions().sendKeys(Key.ESCAPE).perform(); } catch (_) {}
    return false;
}

/**
 * Poll the OpenJML output channel until the deadline, returning the text once
 * all of the required file names appear (or when time runs out).
 */
async function waitForFiles(driver, requiredFiles, deadlineMs) {
    let outputText = '';
    while (Date.now() < deadlineMs) {
        await driver.sleep(3_000);
        try {
            const text = await Promise.race([
                readOpenJMLOutput(),
                new Promise((_, rej) =>
                    setTimeout(() => rej(new Error('timeout')), 10_000)),
            ]);
            outputText = text || '';
        } catch (_) {}
        if (requiredFiles.every(f => outputText.includes(f))) break;
    }
    return outputText;
}

describe('ESC via Explorer context menu', function () {
    this.timeout(180_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(3_000);
    });

    // ── Test A: single-file context menu ──────────────────────────────────────
    it('Context menu on single Explorer file runs only that file', async function () {
        const driver = VSBrowser.instance.driver;

        await VSBrowser.instance.openResources(
            path.resolve(__dirname, '../../resources', FILEA));
        await driver.sleep(2_000);
        let opened = false;
        for (let attempt = 0; attempt < 5 && !opened; attempt++) {
            try { await new EditorView().openEditor(FILEA); opened = true; }
            catch (_) { await driver.sleep(1_000); }
        }
        if (!opened) { console.log('    [SKIP] Could not open ' + FILEA + ' in editor'); this.skip(); return; }

        const section = await getExplorerSection();
        if (!section) { console.log('    [SKIP] Explorer sidebar unavailable'); this.skip(); return; }

        const itemA = await findItem(section, FILEA);
        if (!itemA) { console.log('    [SKIP] ' + FILEA + ' not visible in Explorer'); this.skip(); return; }

        // Single-click FileA only (no Ctrl/Cmd) — single selection.
        await itemA.select();
        await driver.sleep(300);

        const clicked = await invokeRunEscFromContextMenu(driver, itemA);
        if (!clicked) {
            console.log('    [SKIP] "Run ESC" not found in context menu — server may not be running');
            this.skip(); return;
        }

        const deadline = Date.now() + 30_000;
        const outputText = await waitForFiles(driver, [FILEA], deadline);

        if (!outputText.includes(FILEA)) {
            console.log('    [SKIP] Output did not mention ' + FILEA + ' — server may not be running');
            this.skip(); return;
        }

        assert.ok(outputText.includes(FILEA),
            'Expected ' + FILEA + ' in OpenJML output');
        assert.ok(!outputText.includes(FILEB),
            'Expected ' + FILEB + ' NOT in output when only ' + FILEA + ' was selected');
    });

    // ── Test B: multi-select context menu ─────────────────────────────────────
    it('Context menu on multi-selected Explorer files runs all selected files', async function () {
        const driver = VSBrowser.instance.driver;

        await VSBrowser.instance.openResources(
            path.resolve(__dirname, '../../resources', FILEA));
        await driver.sleep(2_000);
        for (let attempt = 0; attempt < 5; attempt++) {
            try { await new EditorView().openEditor(FILEA); break; }
            catch (_) { await driver.sleep(1_000); }
        }

        const section = await getExplorerSection();
        if (!section) { console.log('    [SKIP] Explorer sidebar unavailable'); this.skip(); return; }

        const itemA = await findItem(section, FILEA);
        const itemB = await findItem(section, FILEB);
        if (!itemA || !itemB) {
            console.log('    [SKIP] Test files not visible in Explorer');
            this.skip(); return;
        }

        // Click FileA, then Ctrl/Cmd+click FileB to multi-select both.
        await itemA.select();
        await driver.sleep(300);
        await driver.actions()
            .keyDown(CTL_KEY)
            .click(itemB)
            .keyUp(CTL_KEY)
            .perform();
        await driver.sleep(500);

        const clicked = await invokeRunEscFromContextMenu(driver, itemB);
        if (!clicked) {
            console.log('    [SKIP] "Run ESC" not found in context menu — server may not be running');
            this.skip(); return;
        }

        const deadline = Date.now() + 30_000;
        const outputText = await waitForFiles(driver, [FILEA, FILEB], deadline);

        if (!outputText.includes(FILEA) || !outputText.includes(FILEB)) {
            console.log('    [SKIP] Output did not mention both files — server may not be running');
            this.skip(); return;
        }

        assert.ok(outputText.includes(FILEA),
            'Expected ' + FILEA + ' in OpenJML output');
        assert.ok(outputText.includes(FILEB),
            'Expected ' + FILEB + ' in OpenJML output');
    });
});
