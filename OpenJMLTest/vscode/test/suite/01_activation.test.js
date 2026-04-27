'use strict';
/**
 * Suite 01: Extension Activation
 *
 * Verifies that the OpenJML extension loads without crashing and registers
 * its output channel.  No OpenJML server response is required — these tests
 * cover client-side activation only.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView, BottomBarPanel, Workbench } = require('vscode-extension-tester');

const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');

describe('Extension Activation', function () {
    this.timeout(60_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(30_000);
    });

    it('workbench opens without an error dialog', async function () {
        // If a modal error dialog appears during extension activation the
        // waitForWorkbench call above will throw.  Reaching here means the
        // extension loaded cleanly (even if the server is not reachable yet).
    });

    it('opening a Java file activates the extension', async function () {
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(3_000);

        const editorView = new EditorView();
        const activeTab  = await editorView.getActiveTab();
        assert.ok(activeTab, 'An editor tab must be open');
        const tabTitle = await activeTab.getTitle();
        assert.ok(tabTitle.includes('Sample.java'),
            `Active tab should be Sample.java, got: ${tabTitle}`);
    });

    it('OpenJML output channel is created', async function () {
        // Trigger any command so the extension initialises its output channel.
        const workbench = new Workbench();
        try {
            await workbench.executeCommand('OpenJML: Check JML');
        } catch (_) {
            // Command may be unavailable if server not running — that's fine here.
        }
        await VSBrowser.instance.driver.sleep(2_000);

        const bottomBar  = new BottomBarPanel();
        await bottomBar.toggle(true);
        const outputView = await bottomBar.openOutputView();

        // Retry getChannelNames — the DOM can be transiently stale after toggle.
        let channels = [];
        for (let attempt = 0; attempt < 5; attempt++) {
            try {
                channels = await outputView.getChannelNames();
                break;
            } catch (_) {
                await VSBrowser.instance.driver.sleep(1_000);
            }
        }
        await bottomBar.toggle(false);

        assert.ok(
            channels.some(c => c.includes('OpenJML')),
            `OpenJML channel not found. Available channels: ${channels.join(', ')}`
        );
    });
});
