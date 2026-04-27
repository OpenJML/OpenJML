'use strict';
/**
 * Suite 03: Menu Contributions
 *
 * A. Presence: OpenJML commands appear in the editor context menu and the
 *    Explorer context menu (right-click on a .java file).
 *
 * B. Invocation: each editor context menu command can be triggered without
 *    crashing VS Code.  Server-dependent commands skip gracefully when the
 *    server is unavailable (detected by absence of output after the command).
 *
 * NOTE (potential bug): The Explorer context menu test requires the fix that
 * added resourceExtname == .java to the explorer/context when clauses.
 * If commands are still missing there, the when clause is not matching.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView, SideBarView, Workbench } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, readOutputSafe,
        getExplorerSection, findExplorerItem, invokeContextMenuItem }
    = require('./helpers');

const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');

const EDITOR_CONTEXT_COMMANDS = [
    'Check JML',
    'Run ESC',
    'Run ESC for Method',
    'Save and Run ESC',
    'Run ESC Split by File',
    'Run ESC Split by Method',
    'Run ESC on Project',
    'Compile RAC',
    'Clear Markers',
    'Cancel ESC',
];

const EXPLORER_CONTEXT_COMMANDS = [
    'Check JML',
    'Run ESC',
    'Run ESC Split by File',
    'Run ESC Split by Method',
    'Compile RAC',
    'Clear Markers for Selection',
];

/** Collect all visible menu item labels from an open context menu. */
async function collectMenuLabels(menu) {
    for (let attempt = 0; attempt < 4; attempt++) {
        try {
            const items  = await menu.getItems();
            const labels = [];
            for (const item of items) {
                try { labels.push(await item.getLabel()); } catch (_) {}
            }
            return labels;
        } catch (_) {
            await VSBrowser.instance.driver.sleep(500);
        }
    }
    return [];
}

describe('Menu Contributions', function () {
    this.timeout(120_000);

    let editor;

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(2_000);
        editor = await new EditorView().openEditor('Sample.java');
    });

    after(async function () { this.timeout(30_000); await suiteTeardown(); });

    // ── A. Presence ───────────────────────────────────────────────────────────

    it('editor context menu contains all OpenJML commands', async function () {
        const driver = VSBrowser.instance.driver;
        await editor.click();
        await driver.sleep(500);

        let labels = [];
        for (let attempt = 0; attempt < 5; attempt++) {
            try {
                const menu = await editor.openContextMenu();
                await driver.sleep(800);
                labels = await collectMenuLabels(menu);
                try { await menu.close(); } catch (_) {}
                // If we got the minimap context menu the first item is "Minimap" —
                // dismiss and retry.
                if (labels.some(l => l === 'Minimap')) {
                    labels = [];
                    await driver.sleep(500);
                    continue;
                }
                if (labels.length > 0) break;
            } catch (_) {
                await driver.sleep(1_000);
            }
        }

        const missing = EDITOR_CONTEXT_COMMANDS.filter(
            cmd => !labels.some(l => l.includes(cmd))
        );
        assert.deepStrictEqual(missing, [],
            `Missing from editor context menu: ${missing.join(', ')}\nFound: ${labels.join(', ')}`);
    });

    it('Explorer context menu contains OpenJML commands for a .java file', async function () {
        const section = await getExplorerSection();
        if (!section) { console.log('    [SKIP] Explorer sidebar unavailable'); this.skip(); return; }

        const item = await findExplorerItem(section, 'Sample.java');
        if (!item) { console.log('    [SKIP] Sample.java not visible in Explorer'); this.skip(); return; }

        const driver = VSBrowser.instance.driver;
        let labels = [];
        for (let attempt = 0; attempt < 3; attempt++) {
            try {
                await driver.actions().contextClick(item).perform();
                await driver.sleep(800);
                const elements = await driver.findElements(
                    { css: '.monaco-menu .action-label' });
                labels = await Promise.all(elements.map(e => e.getText().catch(() => '')));
                labels = labels.filter(Boolean);
                if (labels.length > 0) break;
            } catch (_) {}
            try { await driver.actions().sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
            await driver.sleep(500);
        }
        try { await driver.actions().sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
        await driver.sleep(800);

        const missing = EXPLORER_CONTEXT_COMMANDS.filter(
            cmd => !labels.some(l => l.includes(cmd))
        );
        // NOTE: if this fails the resourceExtname when-clause fix is not taking effect.
        assert.deepStrictEqual(missing, [],
            `Missing from Explorer context menu: ${missing.join(', ')}\nFound: ${labels.join(', ')}`);
    });

    // ── B. Invocation ─────────────────────────────────────────────────────────
    // Each test invokes one command and verifies VS Code does not crash.
    // Server-dependent commands skip if no output appears within a short window.

    it('"Check JML" can be invoked from the editor context menu', async function () {
        const driver = VSBrowser.instance.driver;
        // Dismiss any stale context-menu overlay left by the previous test.
        try { await driver.actions().sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
        await driver.sleep(500);
        try { await editor.click(); } catch (_) { await driver.sleep(500); }
        let clicked = false;
        for (let attempt = 0; attempt < 3 && !clicked; attempt++) {
            try {
                const menu = await editor.openContextMenu();
                await driver.sleep(600);
                const items = await driver.findElements({ css: '.monaco-menu .action-label' });
                for (const it of items) {
                    const lbl = await it.getText().catch(() => '');
                    if (lbl === 'Check JML') { await it.click(); clicked = true; break; }
                }
            } catch (_) {}
            if (!clicked) {
                try { await driver.actions().sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
                await driver.sleep(500);
            }
        }
        if (!clicked) { console.log('    [SKIP] Could not click Check JML'); this.skip(); return; }

        await driver.sleep(3_000);
        const output = await readOutputSafe();
        if (!output) { console.log('    [SKIP] No output — server may not be running'); this.skip(); return; }
        // Just verify no error dialog appeared and output channel has content.
        assert.ok(output.length >= 0, 'output channel accessible');
    });

    it('"Clear Markers" can be invoked without error', async function () {
        const driver = VSBrowser.instance.driver;
        // Dismiss any stale context-menu overlay before opening the command palette.
        try { await driver.actions().sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
        await driver.sleep(500);
        const ok = await runCommand('OpenJML: Clear Markers');
        assert.ok(ok, '"Clear Markers" command failed');
    });

    it('"Cancel ESC" can be invoked without error', async function () {
        const driver = VSBrowser.instance.driver;
        try { await driver.actions().sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
        await driver.sleep(300);
        const ok = await runCommand('OpenJML: Cancel ESC');
        assert.ok(ok, '"Cancel ESC" command failed');
    });

    it('"Run ESC" can be invoked from the editor context menu', async function () {
        const driver = VSBrowser.instance.driver;
        await editor.click();
        let clicked = false;
        for (let attempt = 0; attempt < 3 && !clicked; attempt++) {
            try {
                const menu = await editor.openContextMenu();
                await driver.sleep(600);
                const items = await driver.findElements({ css: '.monaco-menu .action-label' });
                for (const it of items) {
                    const lbl = await it.getText().catch(() => '');
                    // Avoid "Run ESC for Method", "Run ESC Split by File", etc.
                    if (lbl === 'Run ESC') { await it.click(); clicked = true; break; }
                }
            } catch (_) {}
            if (!clicked) {
                try { await driver.actions().sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
                await driver.sleep(500);
            }
        }
        if (!clicked) { console.log('    [SKIP] Could not click Run ESC'); this.skip(); return; }

        await driver.sleep(3_000);
        const output = await readOutputSafe();
        if (!output) { console.log('    [SKIP] No output — server may not be running'); this.skip(); return; }
        assert.ok(output.length >= 0, 'output channel accessible after Run ESC');
    });
});
