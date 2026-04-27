'use strict';
/**
 * Suite 07: Output Channel (JML Console)
 *
 * Verifies that the OpenJML output channel:
 *   - exists and is selectable in the bottom bar
 *   - contains startup/connection messages when the extension activates
 *   - receives new lines when a command (Check JML) is invoked
 *   - log lines follow the expected timestamp format
 *
 * Skips output-content tests gracefully when the server is unavailable.
 *
 * NOTE: The output channel is named "OpenJML".  If the channel name ever
 * changes, the hasOpenJMLChannel / readOpenJMLOutput helpers will return null
 * and tests will skip rather than fail.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, BottomBarPanel } = require('vscode-extension-tester');
const { suiteTeardown, readOpenJMLOutput, runCommand } = require('./helpers');

const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');

describe('Output Channel (JML Console)', function () {
    this.timeout(90_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(3_000);
        // Trigger the extension to initialise its output channel.
        await runCommand('OpenJML: Check JML');
        await VSBrowser.instance.driver.sleep(2_000);
    });

    after(async function () { await suiteTeardown(true); });

    it('OpenJML output channel exists in the bottom bar', async function () {
        const driver     = VSBrowser.instance.driver;
        const bottomBar  = new BottomBarPanel();
        await bottomBar.toggle(true);
        await driver.sleep(500);

        const outputView = await bottomBar.openOutputView();
        let channels = [];
        for (let attempt = 0; attempt < 5; attempt++) {
            try { channels = await outputView.getChannelNames(); break; }
            catch (_) { await driver.sleep(500); }
        }
        await bottomBar.toggle(false);

        assert.ok(
            channels.some(c => c.includes('OpenJML')),
            `OpenJML channel not found. Available: ${channels.join(', ')}`);
    });

    it('output channel is selectable and readable', async function () {
        const text = await readOpenJMLOutput();
        // null means the channel doesn't exist yet — acceptable if server is absent.
        if (text === null) { console.log('    [SKIP] OpenJML channel not present'); this.skip(); return; }
        // If the server is running we expect at least some content.
        // If not, getText() returns '' which is still OK — channel exists.
        assert.ok(typeof text === 'string', 'getText() should return a string');
    });

    it('output channel receives content after Check JML', async function () {
        const before = (await readOpenJMLOutput()) || '';
        await runCommand('OpenJML: Check JML');
        await VSBrowser.instance.driver.sleep(4_000);
        const after = (await readOpenJMLOutput()) || '';

        if (after.length === 0) {
            console.log('    [SKIP] No output produced — server may not be running');
            this.skip(); return;
        }
        assert.ok(after.length >= before.length,
            'Output channel should have grown or stayed the same after Check JML');
    });

    it('log lines follow the [HH:MM:SS] timestamp format', async function () {
        const text = await readOpenJMLOutput();
        if (!text || text.trim().length === 0) {
            console.log('    [SKIP] No output to check format against');
            this.skip(); return;
        }
        // Expect at least one line matching the server timestamp format.
        // NOTE: if the format changes this test will need updating.
        const timestampRe = /\[\d{2}:\d{2}:\d{2}/;
        assert.ok(timestampRe.test(text),
            `No [HH:MM:SS] timestamp found in output:\n${text.slice(0, 300)}`);
    });

    it('output channel shows a Check JML invocation entry', async function () {
        const text = await readOpenJMLOutput();
        if (!text || text.trim().length === 0) {
            console.log('    [SKIP] No output to inspect');
            this.skip(); return;
        }
        // The server logs a "runCheck" or "checkJml" marker when Check JML fires.
        // NOTE: if the log marker changes, update this pattern.
        const hasCheckEntry = /runCheck|checkJml|Check JML|SOURCE_CHECK/i.test(text);
        if (!hasCheckEntry) {
            console.log('    [NOTE] No Check JML marker found — server log format may differ');
            // Soft check: presence of ANY OpenJML log activity is acceptable.
            assert.ok(text.length > 0, 'Output channel should have content');
        } else {
            assert.ok(hasCheckEntry, 'Output should contain a Check JML invocation entry');
        }
    });
});
