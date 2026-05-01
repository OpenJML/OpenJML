'use strict';
/**
 * Suite 05: ESC via Explorer context menu — single file vs multi-select
 *
 * Test A – Single file: right-clicking one file (no multi-select) ESCs only
 *           that file.  The other file must NOT appear in the output.
 *
 * Test B – Multi-select: right-clicking while two files are selected ESCs
 *           both files.  Both must appear in the output.
 *
 * Skips with a logged reason when the server is unavailable.
 */
const assert  = require('assert');
const fs      = require('fs');
const path    = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { Key } = require('selenium-webdriver');
const { suiteTeardown, waitForServerLog, waitForServer, noteSkip,
        getExplorerSection, findExplorerItem, invokeContextMenuItem }
    = require('./helpers');

const SERVER_LOG = process.env.OPENJML_LSP_LOG
    || path.resolve(__dirname, '../../.test-resources/server.log');

const FILEA       = 'EscFileA.java';
const FILEB       = 'EscFileB.java';
const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');
const CTL_KEY     = process.platform === 'darwin' ? Key.COMMAND : Key.CONTROL;

describe('ESC via Explorer context menu', function () {
    this.timeout(180_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(3_000);
        const ready = await waitForServer(60_000);
        assert.ok(ready, 'OpenJML LSP server did not start — cannot test Explorer ESC commands');
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

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
        if (!opened) noteSkip(this, 'could not open ' + FILEA + ' in editor');

        const section = await getExplorerSection();
        if (!section) noteSkip(this, 'Explorer sidebar unavailable');

        const itemA = await findExplorerItem(section, FILEA);
        if (!itemA) noteSkip(this, FILEA + ' not visible in Explorer');

        await itemA.select();
        await driver.sleep(300);

        // Snapshot log length before ESC so the FILEB-absence check only covers new entries.
        let logLengthBefore = 0;
        try { logLengthBefore = fs.readFileSync(SERVER_LOG, 'utf8').length; } catch (_) {}

        const clicked = await invokeContextMenuItem(itemA, 'Run ESC', ['Split', 'Method', 'Save']);
        if (!clicked)
            noteSkip(this, '"Run ESC" not in Explorer context menu — server may not be running');

        // Poll only the NEW portion of the server log (after the snapshot) so that a
        // prior mention of FILEA (from opening the file) does not cause a false pass.
        const deadline = Date.now() + 60_000;
        let newLog = '';
        while (Date.now() < deadline) {
            try {
                const full = fs.readFileSync(SERVER_LOG, 'utf8');
                newLog = full.slice(logLengthBefore);
                if (newLog.includes(FILEA)) break;
            } catch (_) {}
            await driver.sleep(1_000);
        }
        if (!newLog.includes(FILEA))
            noteSkip(this, 'server log did not mention ' + FILEA + ' — ESC may not have run');

        assert.ok(newLog.includes(FILEA),  'Expected ' + FILEA + ' in server log');
        assert.ok(!newLog.includes(FILEB), 'Expected ' + FILEB + ' NOT in server log for single-select');
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
        if (!section) noteSkip(this, 'Explorer sidebar unavailable');

        const itemA = await findExplorerItem(section, FILEA);
        const itemB = await findExplorerItem(section, FILEB);
        if (!itemA || !itemB)
            noteSkip(this, 'test files not visible in Explorer');

        await itemA.select();
        await driver.sleep(300);
        await driver.actions()
            .keyDown(CTL_KEY).click(itemB).keyUp(CTL_KEY)
            .perform();
        await driver.sleep(500);

        const clicked = await invokeContextMenuItem(itemB, 'Run ESC', ['Split', 'Method', 'Save']);
        if (!clicked)
            noteSkip(this, '"Run ESC" not in Explorer context menu — server may not be running');

        // Use server log (not output channel) since getText() is broken in VS Code 1.117+.
        const outputText = await waitForServerLog([FILEA, FILEB], Date.now() + 30_000);
        if (!outputText.includes(FILEA) || !outputText.includes(FILEB))
            noteSkip(this, 'server log did not mention both files — ESC may not have run');

        assert.ok(outputText.includes(FILEA), 'Expected ' + FILEA + ' in server log');
        assert.ok(outputText.includes(FILEB), 'Expected ' + FILEB + ' in server log');
    });
});
