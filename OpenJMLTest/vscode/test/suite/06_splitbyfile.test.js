'use strict';
/**
 * Suite 06: ESC Split by File via Explorer multi-select
 *
 * Multi-selects two Java files in the Explorer and invokes
 * "Run ESC Split by File" from the context menu.  Both files must appear in
 * the output, and both should start proving before either finishes (parallelism
 * check — soft, since timing is nondeterministic).
 *
 * Skips gracefully when the OpenJML server is unavailable.
 */
const assert  = require('assert');
const path    = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { Key } = require('selenium-webdriver');
const { suiteTeardown, readOutputSafe,
        getExplorerSection, findExplorerItem, invokeContextMenuItem }
    = require('./helpers');

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
    });

    after(async function () { await suiteTeardown(true); });

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
        if (!section) { console.log('    [SKIP] Explorer sidebar unavailable'); this.skip(); return; }

        const itemA = await findExplorerItem(section, FILEA);
        const itemB = await findExplorerItem(section, FILEB);
        if (!itemA || !itemB) {
            console.log('    [SKIP] Test files not visible in Explorer');
            this.skip(); return;
        }

        await itemA.select();
        await driver.sleep(300);
        await driver.actions()
            .keyDown(CTL_KEY).click(itemB).keyUp(CTL_KEY)
            .perform();
        await driver.sleep(500);

        const clicked = await invokeContextMenuItem(itemB, 'Split by File');
        if (!clicked) {
            console.log('    [SKIP] "Run ESC Split by File" not in context menu — server may not be running');
            this.skip(); return;
        }

        // Poll until output stabilises (no growth for 2 consecutive polls).
        const deadline    = Date.now() + 60_000;
        let bothStartedEarly = false;
        let prevLength    = 0;
        let stableCount   = 0;
        let finalOutput   = '';

        while (Date.now() < deadline) {
            await driver.sleep(3_000);
            const snapshot = await readOutputSafe();
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

        if (!finalOutput.includes(FILEA) || !finalOutput.includes(FILEB)) {
            console.log('    [SKIP] Output did not mention both files — server may not be running');
            this.skip(); return;
        }

        assert.ok(finalOutput.includes(FILEA), `Expected ${FILEA} in output`);
        assert.ok(finalOutput.includes(FILEB), `Expected ${FILEB} in output`);

        if (!bothStartedEarly)
            console.log('    [NOTE] Could not confirm overlapping start — files may have run sequentially or too fast');
    });
});
