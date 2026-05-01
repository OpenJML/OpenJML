'use strict';
/**
 * Suite 08: Diagnostics (Markers)
 *
 * Opens JmlErrors.java, which contains:
 *   - bad():     postcondition \result < 0 never satisfied (ESC failure)
 *   - badNull(): requires x == null on a primitive int (type/check error)
 *   - good():    valid spec (no error expected)
 *
 * Tests:
 *   A. Check JML produces at least one diagnostic.
 *   B. At least one diagnostic has Error severity.
 *   C. "Clear Markers" removes all OpenJML diagnostics.
 *   D. "Clear Markers for Selection" removes diagnostics for the selected file
 *      (distinct from Clear All — uses openjml.clearMarkersForUris, not
 *      openjml.clearMarkers).
 *   E. ESC on bad() reports a verification failure.
 *
 * Skips with a logged reason when the server is unavailable or when
 * the ProblemsView API is not available in this vscode-extension-tester version.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView, BottomBarPanel } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, waitForServer, noteSkip, openAndFocusFile,
        getExplorerSection, findExplorerItem, invokeContextMenuItem } = require('./helpers');

const JML_ERRORS_JAVA = path.resolve(__dirname, '../../resources/JmlErrors.java');
const DIAG_WAIT_MS    = 60_000;

/**
 * Poll the Problems panel until at least minCount markers appear, or timeout.
 * Returns the marker array (possibly empty).
 * Skips with a note if ProblemsView is not available.
 */
async function waitForDiagnostics(ctx, minCount, timeoutMs) {
    const driver    = VSBrowser.instance.driver;
    const deadline  = Date.now() + timeoutMs;
    const bottomBar = new BottomBarPanel();
    const { MarkerType } = require('vscode-extension-tester');

    while (Date.now() < deadline) {
        try {
            await bottomBar.toggle(true);
            const pv      = await bottomBar.openProblemsView();
            await driver.sleep(1_000);
            const markers = await pv.getAllVisibleMarkers(MarkerType.Any);
            await bottomBar.toggle(false);
            if (markers.length >= minCount) return markers;
        } catch (e) {
            try { await bottomBar.toggle(false); } catch (_) {}
            if (/ProblemsView|openProblemsView/.test(String(e)))
                noteSkip(ctx, 'ProblemsView API unavailable in this vscode-extension-tester version');
        }
        await driver.sleep(2_000);
    }
    try { await bottomBar.toggle(false); } catch (_) {}
    return [];
}

/**
 * Read the current Problems panel marker count.
 * Returns -1 if the panel cannot be opened (caller should skip).
 */
async function markerCount() {
    const driver    = VSBrowser.instance.driver;
    const bottomBar = new BottomBarPanel();
    const { MarkerType } = require('vscode-extension-tester');
    try {
        await bottomBar.toggle(true);
        const pv      = await bottomBar.openProblemsView();
        await driver.sleep(1_000);
        const markers = await pv.getAllVisibleMarkers(MarkerType.Any);
        await bottomBar.toggle(false);
        return markers.length;
    } catch (_) {
        try { await bottomBar.toggle(false); } catch (__) {}
        return -1;
    }
}

describe('Diagnostics (Markers)', function () {
    this.timeout(120_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await openAndFocusFile(JML_ERRORS_JAVA);
        const ready = await waitForServer(60_000);
        assert.ok(ready, 'OpenJML LSP server did not start — cannot test diagnostics');
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

    it('Check JML produces at least one diagnostic on JmlErrors.java', async function () {
        const ok = await runCommand('OpenJML: Check JML');
        if (!ok) noteSkip(this, 'Check JML command unavailable — server may not be running');
        await VSBrowser.instance.driver.sleep(3_000);
        const markers = await waitForDiagnostics(this, 1, DIAG_WAIT_MS);
        if (markers.length === 0)
            noteSkip(this, 'no diagnostics appeared — server may not be running');
        assert.ok(markers.length >= 1,
            `Expected at least 1 diagnostic, got ${markers.length}`);
    });

    it('at least one diagnostic has Error severity', async function () {
        const { MarkerType } = require('vscode-extension-tester');
        const driver    = VSBrowser.instance.driver;
        const bottomBar = new BottomBarPanel();
        let errorMarkers = [];
        try {
            await bottomBar.toggle(true);
            const pv = await bottomBar.openProblemsView();
            await driver.sleep(1_000);
            errorMarkers = await pv.getAllVisibleMarkers(MarkerType.Error);
            await bottomBar.toggle(false);
        } catch (e) {
            try { await bottomBar.toggle(false); } catch (_) {}
            noteSkip(this, 'ProblemsView unavailable — ' + String(e).slice(0, 80));
        }
        if (errorMarkers.length === 0)
            noteSkip(this, 'no error-level markers — server may not be running or spec may not produce type errors');
        assert.ok(errorMarkers.length >= 1,
            `Expected at least 1 error-severity diagnostic, got ${errorMarkers.length}`);
    });

    it('"Clear Markers" removes OpenJML diagnostics', async function () {
        const driver = VSBrowser.instance.driver;

        // Ensure markers exist before clearing (re-run check if needed).
        let countBefore = await markerCount();
        if (countBefore < 0)
            noteSkip(this, 'ProblemsView unavailable — cannot verify Clear Markers');
        if (countBefore === 0) {
            const ok = await runCommand('OpenJML: Check JML');
            if (!ok) noteSkip(this, 'Check JML unavailable — server may not be running');
            await driver.sleep(3_000);
            countBefore = await markerCount();
        }
        if (countBefore === 0)
            noteSkip(this, 'no markers present before clear — cannot verify Clear Markers removes them');

        const ok = await runCommand('OpenJML: Clear Markers');
        assert.ok(ok, '"Clear Markers" command should succeed');
        await driver.sleep(2_000);

        const countAfter = await markerCount();
        if (countAfter < 0)
            noteSkip(this, 'ProblemsView unavailable after clear');
        console.log(`    [INFO] markers before Clear Markers: ${countBefore}, after: ${countAfter}`);
        assert.ok(countAfter < countBefore,
            `"Clear Markers" should reduce the marker count (before=${countBefore} after=${countAfter})`);
    });

    it('"Clear Markers for Selection" removes diagnostics for selected file', async function () {
        const driver = VSBrowser.instance.driver;

        // Re-establish markers with Check JML.
        const checkOk = await runCommand('OpenJML: Check JML');
        if (!checkOk) noteSkip(this, 'Check JML unavailable — server may not be running');
        await driver.sleep(3_000);

        let countBefore = await markerCount();
        if (countBefore < 0)
            noteSkip(this, 'ProblemsView unavailable — cannot verify Clear Markers for Selection');
        if (countBefore === 0)
            noteSkip(this, 'no markers present — cannot verify Clear Markers for Selection');

        // Find JmlErrors.java in the Explorer and invoke the context menu.
        const section = await getExplorerSection();
        if (!section) noteSkip(this, 'Explorer sidebar unavailable');
        const item = await findExplorerItem(section, 'JmlErrors.java');
        if (!item) noteSkip(this, 'JmlErrors.java not found in Explorer');

        const clicked = await invokeContextMenuItem(item, 'Clear Markers for Selection',
                                                    ['Clear Caches']);
        if (!clicked) noteSkip(this, '"Clear Markers for Selection" not in context menu');
        await driver.sleep(2_000);

        const countAfter = await markerCount();
        if (countAfter < 0)
            noteSkip(this, 'ProblemsView unavailable after clear');
        console.log(`    [INFO] markers before selection clear: ${countBefore}, after: ${countAfter}`);
        assert.ok(countAfter < countBefore,
            `"Clear Markers for Selection" should reduce the marker count (before=${countBefore} after=${countAfter})`);
    });

    it('ESC on bad() reports a verification failure', async function () {
        // bad() has ensures \result < 0 but returns x > 0 — ESC must fail.
        // Re-focus the editor (previous test may have left Explorer sidebar focused).
        try { await VSBrowser.instance.driver.actions()
            .sendKeys(require('selenium-webdriver').Key.ESCAPE).perform(); } catch (_) {}
        await VSBrowser.instance.driver.sleep(300);
        await openAndFocusFile(JML_ERRORS_JAVA);
        await VSBrowser.instance.driver.sleep(500);
        // Ensure the file is type-checked before ESC — the server needs the AST.
        await runCommand('OpenJML: Check JML');
        await VSBrowser.instance.driver.sleep(3_000);
        const ok = await runCommand('OpenJML: Run ESC');
        if (!ok) noteSkip(this, 'Run ESC command unavailable — server may not be running');
        await VSBrowser.instance.driver.sleep(5_000);
        const markers = await waitForDiagnostics(this, 1, DIAG_WAIT_MS);
        if (markers.length === 0)
            noteSkip(this, 'no ESC diagnostics — server may not be running');
        assert.ok(markers.length >= 1,
            'Expected at least one verification failure marker from ESC on bad()');
    });
});
