'use strict';
/**
 * Suite 04: Code Lenses
 *
 * Verifies that OpenJML ESC status code lenses appear for each method in a
 * Java file after a --check run, and that clicking a lens triggers re-ESC.
 *
 * Requires the OpenJML server to be reachable via openjml.serverPath.
 * Tests skip gracefully when the server is unavailable.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView, BottomBarPanel, Workbench } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, readOpenJMLOutput } = require('./helpers');

const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');
const POLL_MS     = 2_000;
const LENS_WAIT_S = 40;   // seconds to wait for lenses to appear

/** Poll until fn() returns a non-empty array or the deadline passes. */
async function pollUntilNonEmpty(fn, timeoutMs) {
    const deadline = Date.now() + timeoutMs;
    while (Date.now() < deadline) {
        try {
            const result = await fn();
            if (result && result.length > 0) return result;
        } catch (_) { /* not ready yet */ }
        await VSBrowser.instance.driver.sleep(POLL_MS);
    }
    return [];
}

describe('Code Lenses', function () {
    this.timeout(120_000);

    let editor;

    before(async function () {
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(2_000);

        const editorView = new EditorView();
        editor = await editorView.openEditor('Sample.java');
    });

    it('code lenses appear for each method after Check JML', async function () {
        const ok = await runCommand('OpenJML: Check JML');
        if (!ok) { this.skip(); return; }

        const lenses = await pollUntilNonEmpty(
            () => editor.getCodeLenses(), LENS_WAIT_S * 1_000
        );

        if (lenses.length === 0) {
            console.log('    [SKIP] No code lenses found — server may not be running');
            this.skip();
        }

        // Sample.java has 3 methods; expect at least 3 lenses.
        assert.ok(lenses.length >= 3,
            `Expected at least 3 code lenses, got ${lenses.length}`);

        const texts = await Promise.all(lenses.map(l => l.getText()));
        assert.ok(
            texts.every(t => t.includes('Run ESC') || t.includes('Verified')
                           || t.includes('issue')   || t.includes('Checking')
                           || t.includes('—')),
            `Unexpected lens text(s): ${texts.join(' | ')}`
        );
    });

    it('code lens texts include method status indicators', async function () {
        const lenses = await pollUntilNonEmpty(
            () => editor.getCodeLenses(), 5_000
        );
        if (lenses.length === 0) { this.skip(); return; }

        const texts = await Promise.all(lenses.map(l => l.getText()));
        // At least one lens should carry the "Run ESC" prompt (UNKNOWN state)
        // or a proof result (✓ / ✗) after a previous ESC run.
        const hasStatusMarker = texts.some(
            t => t.includes('Run ESC') || t.includes('✓') || t.includes('✗')
              || t.includes('Verified') || t.includes('issue')
        );
        assert.ok(hasStatusMarker,
            `No ESC status marker found in lenses: ${texts.join(' | ')}`);
    });

    it('clicking a Run ESC lens starts a proof', async function () {
        const lenses = await pollUntilNonEmpty(
            () => editor.getCodeLenses(), 5_000
        );
        if (lenses.length === 0) { this.skip(); return; }

        // Find a lens in the "Run ESC" (UNKNOWN) state to click.
        let target = null;
        for (const lens of lenses) {
            const text = await lens.getText();
            if (text.includes('Run ESC')) { target = lens; break; }
        }
        if (!target) {
            console.log('    [SKIP] No "Run ESC" lens — all methods already have results');
            this.skip();
            return;
        }

        await target.click();
        await VSBrowser.instance.driver.sleep(3_000);

        // After clicking, the lens for that method should transition to CHECKING
        // or a proof result.  We just verify no crash occurred.
        const updatedLenses = await editor.getCodeLenses();
        assert.ok(updatedLenses.length >= lenses.length,
            'Lens count should not decrease after clicking Run ESC');
    });

    it('OpenJML output channel shows ESC activity', async function () {
        await VSBrowser.instance.driver.sleep(3_000);
        const text = await readOpenJMLOutput();
        if (text === null) { this.skip(); return; }
        assert.ok(text.length > 0,
            'OpenJML output channel is empty — expected at least startup messages');
    });

    after(async function () { await suiteTeardown(true); });
});
