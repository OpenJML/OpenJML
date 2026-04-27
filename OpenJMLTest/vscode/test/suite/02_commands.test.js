'use strict';
/**
 * Suite 02: Command Registration
 *
 * Verifies that every OpenJML command declared in package.json is present
 * in the command palette.  No server required.
 */
const assert = require('assert');
const { VSBrowser, Workbench } = require('vscode-extension-tester');
const { suiteTeardown } = require('./helpers');

// All commands that must appear in the palette (category + title form).
const EXPECTED_COMMANDS = [
    'OpenJML: Check JML',
    'OpenJML: Run ESC',
    'OpenJML: Run ESC for Method',
    'OpenJML: Save and Run ESC',
    'OpenJML: Run ESC Split by File',
    'OpenJML: Run ESC Split by Method',
    'OpenJML: Run ESC on Project',
    'OpenJML: Compile RAC',
    'OpenJML: Index Project',
    'OpenJML: Clear Markers',
    'OpenJML: Clear Markers for Selection',
    'OpenJML: Clear Caches and Reindex',
    'OpenJML: Cancel ESC',
    'OpenJML: Abort Method Proof',
];

describe('Command Registration', function () {
    this.timeout(120_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(15_000);
    });

    it('all OpenJML commands appear in the command palette', async function () {
        const workbench = new Workbench();

        // Poll until the palette returns OpenJML results — extension activation
        // may lag slightly after the workbench is ready.
        // Prefix with '>' so VS Code stays in command-search mode (not file-search).
        let labels = [];
        for (let attempt = 0; attempt < 6; attempt++) {
            const input = await workbench.openCommandPrompt();
            await input.setText('>OpenJML');
            await VSBrowser.instance.driver.sleep(2_000);
            try {
                const picks = await input.getQuickPicks();
                labels = await Promise.all(picks.map(p => p.getLabel()));
            } catch (_) { /* stale element — retry */ }
            await input.cancel();
            if (labels.some(l => l.includes('OpenJML'))) break;
            await VSBrowser.instance.driver.sleep(1_000);
        }

        const missing = EXPECTED_COMMANDS.filter(
            cmd => !labels.some(l => l === cmd)
        );
        assert.deepStrictEqual(
            missing, [],
            `Missing from palette: ${missing.join(', ')}\nFound: ${labels.join(', ')}`
        );
    });

    after(async function () { await suiteTeardown(); });
});
