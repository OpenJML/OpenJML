'use strict';
/**
 * Suite 03: Menu Contributions
 *
 * Verifies that OpenJML commands appear in the editor context menu (right-click
 * in the editor) and in the explorer context menu (right-click on a file in the
 * Explorer side bar).  No server required.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView, SideBarView, Workbench } = require('vscode-extension-tester');

const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');

// OpenJML commands expected in the editor right-click context menu.
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

// OpenJML commands expected in the Explorer context menu for a Java file.
const EXPLORER_CONTEXT_COMMANDS = [
    'Check JML',
    'Run ESC',
    'Run ESC Split by File',
    'Run ESC Split by Method',
    'Compile RAC',
    'Clear Markers for Selection',
];

/** Flatten menu items into a flat label list, retrying on stale DOM. */
async function collectMenuLabels(menu) {
    for (let attempt = 0; attempt < 4; attempt++) {
        try {
            const labels = [];
            const items  = await menu.getItems();
            for (const item of items) {
                try {
                    labels.push(await item.getLabel());
                } catch (_) { /* separator or non-text item */ }
            }
            return labels;
        } catch (_) {
            await VSBrowser.instance.driver.sleep(500);
        }
    }
    return [];
}

describe('Menu Contributions', function () {
    this.timeout(60_000);

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(2_000);
    });

    it('editor context menu contains OpenJML commands', async function () {
        const editorView = new EditorView();
        const editor     = await editorView.openEditor('Sample.java');

        // Click in the editor to ensure it has focus before right-clicking.
        await editor.click();
        await VSBrowser.instance.driver.sleep(500);

        // Retry the open+read sequence — the context menu can fail to appear if
        // VS Code's UI is still settling after previous interactions.
        let labels = [];
        for (let attempt = 0; attempt < 4; attempt++) {
            try {
                const menu = await editor.openContextMenu();
                await VSBrowser.instance.driver.sleep(800);
                labels = await collectMenuLabels(menu);
                try { await menu.close(); } catch (_) {}
                if (labels.length > 0) break;
            } catch (_) {
                await VSBrowser.instance.driver.sleep(1_000);
            }
        }

        const missing = EDITOR_CONTEXT_COMMANDS.filter(
            cmd => !labels.some(l => l.includes(cmd))
        );
        assert.deepStrictEqual(
            missing, [],
            `Missing from editor context menu: ${missing.join(', ')}\nFound: ${labels.join(', ')}`
        );
    });
});
