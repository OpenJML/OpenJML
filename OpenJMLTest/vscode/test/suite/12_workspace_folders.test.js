'use strict';
/**
 * Suite 12: Workspace Folder Changes
 *
 * Verifies that the OpenJML extension correctly notifies the server when VS Code
 * workspace folders are added or removed.
 *
 * The test runner opens VS Code with two workspace folders (resources/ and
 * resources/extra/).  This suite removes the extra/ folder via the VS Code
 * quickpick and verifies that the server logs a
 * "[workspace/didChangeWorkspaceFolders] rootPaths now:" message that no longer
 * includes the removed folder.
 *
 * The server logs this message to stderr, which the extension routes to the
 * OpenJML output channel, making it observable from tests.
 *
 * NOTE: This suite intentionally runs last (12_) because it removes a workspace
 * folder from the running VS Code instance, changing the workspace structure for
 * any subsequently running suites.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, Workbench, InputBox } = require('vscode-extension-tester');
const { suiteTeardown, waitForServerLog, waitForServer, noteSkip } = require('./helpers');

const EXTRA_DIR = path.resolve(__dirname, '../../resources/extra');

describe('Workspace Folder Changes', function () {
    this.timeout(120_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(30_000);
        const ready = await waitForServer(60_000);
        if (!ready) { noteSkip(this, 'Server not ready — skipping workspace folder test'); return; }
    });

    it('removing a workspace folder triggers didChangeWorkspaceFolders and server log', async function () {
        const driver = VSBrowser.instance.driver;

        // Execute "Remove Folder from Workspace..." — shows a quickpick with folder names.
        try {
            await new Workbench().executeCommand('workbench.action.removeRootFolder');
        } catch (err) {
            noteSkip(this, `removeRootFolder command unavailable (single-folder workspace?): ${err}`);
            return;
        }

        // Select the 'extra' folder from the quickpick.
        let input;
        try {
            input = await InputBox.create(5_000);
            await input.selectQuickPick('extra');
        } catch (err) {
            // Dismiss if anything goes wrong to avoid leaving a stale dialog.
            try { if (input) await input.cancel(); } catch (_) {}
            noteSkip(this, `Could not interact with remove-folder quickpick: ${err}`);
            return;
        }

        // The server logs "[workspace/didChangeWorkspaceFolders] rootPaths now: [...]"
        // to stderr (captured in the server log file).  Poll the log file directly
        // since getText() from the VS Code output panel is unreliable in VS Code 1.117+.
        const logText = await waitForServerLog(
            ['[workspace/didChangeWorkspaceFolders] rootPaths now:'],
            Date.now() + 20_000
        );

        assert.ok(
            logText.includes('[workspace/didChangeWorkspaceFolders] rootPaths now:'),
            'Server must log didChangeWorkspaceFolders with new rootPaths.\n'
            + 'Captured log:\n' + logText
        );
        assert.ok(
            !logText.includes(EXTRA_DIR),
            'Server rootPaths must not include the removed extra/ folder.\n'
            + 'Captured log:\n' + logText
        );
    });

    after(async function () { this.timeout(30_000); await suiteTeardown(); });
});
