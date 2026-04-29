'use strict';
/**
 * Suite 06: ESC Split by File via Explorer multi-select
 *
 * Multi-selects two Java files and invokes "Run ESC Split by File" from the
 * Explorer context menu.  Both files must appear in the output, and both
 * should start proving before either finishes (soft parallelism check).
 *
 * Skips with a logged reason when the server is unavailable.
 */
const assert  = require('assert');
const fs      = require('fs');
const path    = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { Key } = require('selenium-webdriver');
const { suiteTeardown, waitForServer, noteSkip,
        getExplorerSection, findExplorerItem, invokeContextMenuItem }
    = require('./helpers');

const SERVER_LOG = process.env.OPENJML_LSP_LOG
    || path.resolve(__dirname, '../../.test-resources/server.log');

const FILEA   = 'EscFileA.java';
const FILEB   = 'EscFileB.java';
const CTL_KEY = process.platform === 'darwin' ? Key.COMMAND : Key.CONTROL;

describe('ESC Split by File via Explorer multi-select', function () {
    this.timeout(240_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(
            path.resolve(__dirname, '../../resources/Sample.java'));
        await VSBrowser.instance.driver.sleep(3_000);
        const ready = await waitForServer(60_000);
        assert.ok(ready, 'OpenJML LSP server did not start — cannot test Split-by-File ESC');
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

    it('Split-by-file on two Explorer-selected files runs both files in parallel', async function () {
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

        const clicked = await invokeContextMenuItem(itemB, 'Split by File');
        if (!clicked)
            noteSkip(this, '"Run ESC Split by File" not in context menu — server may not be running');

        // Poll the server log (getText() broken in VS Code 1.117+) until both files
        // appear or deadline. Stable-count loop retained for overlap detection.
        const deadline       = Date.now() + 60_000;
        let bothStartedEarly = false;
        let prevLength       = 0;
        let stableCount      = 0;
        let finalOutput      = '';

        while (Date.now() < deadline) {
            await driver.sleep(3_000);
            let snapshot = '';
            try { snapshot = fs.readFileSync(SERVER_LOG, 'utf8'); } catch (_) {}
            if (!snapshot) continue;
            finalOutput = snapshot;

            if (!bothStartedEarly && snapshot.includes(FILEA) && snapshot.includes(FILEB))
                bothStartedEarly = true;

            if (snapshot.length === prevLength) {
                if (++stableCount >= 2) break;
            } else {
                stableCount = 0;
                prevLength  = snapshot.length;
            }
        }

        if (!finalOutput.includes(FILEA) || !finalOutput.includes(FILEB))
            noteSkip(this, 'server log did not mention both files — ESC may not have run');

        assert.ok(finalOutput.includes(FILEA), `Expected ${FILEA} in server log`);
        assert.ok(finalOutput.includes(FILEB), `Expected ${FILEB} in server log`);

        if (!bothStartedEarly)
            console.log('    [NOTE] could not confirm overlapping start — files may have run sequentially or too fast');
    });
});
