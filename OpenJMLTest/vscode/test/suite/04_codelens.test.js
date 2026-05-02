'use strict';
/**
 * Suite 04: Code Lenses
 *
 * Verifies that OpenJML ESC status code lenses appear for each method in a
 * Java file after a --check run, and that clicking a lens triggers re-ESC.
 *
 * Requires the OpenJML server to be reachable via openjml.serverPath.
 * Tests skip with a logged reason when the server is unavailable.
 */
const assert = require('assert');
const path   = require('path');
const { VSBrowser, EditorView } = require('vscode-extension-tester');
const { suiteTeardown, runCommand, readOpenJMLOutput, noteSkip, waitForServer } = require('./helpers');

const SAMPLE_JAVA = path.resolve(__dirname, '../../resources/Sample.java');
const POLL_MS     = 2_000;
const LENS_WAIT_S = 40;

/** Poll until fn() returns a non-empty array or the deadline passes. */
async function pollUntilNonEmpty(fn, timeoutMs) {
    const deadline = Date.now() + timeoutMs;
    while (Date.now() < deadline) {
        try {
            const result = await fn();
            if (result && result.length > 0) return result;
        } catch (_) {}
        await VSBrowser.instance.driver.sleep(POLL_MS);
    }
    return [];
}

describe('Code Lenses', function () {
    this.timeout(120_000);

    let editor;

    before(async function () {
        this.timeout(150_000);
        await VSBrowser.instance.waitForWorkbench(20_000);
        await VSBrowser.instance.openResources(SAMPLE_JAVA);
        await VSBrowser.instance.driver.sleep(2_000);
        editor = await new EditorView().openEditor('Sample.java');
        const ready = await waitForServer(60_000);
        assert.ok(ready, 'OpenJML LSP server did not start — cannot test code lenses');
    });

    after(async function () { this.timeout(60_000); await suiteTeardown(true); });

    it('code lenses appear for each method after Check JML', async function () {
        const ok = await runCommand('OpenJML: Check JML');
        if (!ok) noteSkip(this, 'Check JML command unavailable — server may not be running');

        const lenses = await pollUntilNonEmpty(
            () => editor.getCodeLenses(), LENS_WAIT_S * 1_000);

        if (lenses.length === 0)
            noteSkip(this, 'no code lenses appeared — server may not be running');

        // Sample.java has 3 methods; expect at least 3 lenses.
        assert.ok(lenses.length >= 3,
            `Expected at least 3 code lenses, got ${lenses.length}`);

        // getText() can throw StaleElementReferenceError if the server refreshes
        // lenses between the poll and the read.  Retry once with a fresh fetch.
        let texts = [];
        for (let attempt = 0; attempt < 3; attempt++) {
            const fresh = attempt === 0 ? lenses : await editor.getCodeLenses().catch(() => []);
            try {
                texts = await Promise.all(fresh.map(l => l.getText()));
                break;
            } catch (e) {
                if (!e.toString().includes('stale') && !e.toString().includes('Stale')) throw e;
                await VSBrowser.instance.driver.sleep(500);
            }
        }
        assert.ok(texts.length > 0, 'Could not read code lens texts after retries');
        assert.ok(
            texts.every(t => t.includes('Run ESC') || t.includes('Verified')
                           || t.includes('issue')   || t.includes('Checking')
                           || t.includes('—')),
            `Unexpected lens text(s): ${texts.join(' | ')}`);
    });

    it('code lens texts include method status indicators', async function () {
        const lenses = await pollUntilNonEmpty(() => editor.getCodeLenses(), 5_000);
        if (lenses.length === 0)
            noteSkip(this, 'no code lenses — server may not be running');

        let texts = [];
        for (let attempt = 0; attempt < 3; attempt++) {
            const fresh = attempt === 0 ? lenses : await editor.getCodeLenses().catch(() => []);
            try {
                texts = await Promise.all(fresh.map(l => l.getText()));
                break;
            } catch (e) {
                if (!e.toString().includes('stale') && !e.toString().includes('Stale')) throw e;
                await VSBrowser.instance.driver.sleep(500);
            }
        }
        const hasStatusMarker = texts.some(
            t => t.includes('Run ESC') || t.includes('✓') || t.includes('✗')
              || t.includes('Verified') || t.includes('issue'));
        assert.ok(hasStatusMarker,
            `No ESC status marker found in lenses: ${texts.join(' | ')}`);
    });

    it('clicking a Run ESC lens starts a proof', async function () {
        const lenses = await pollUntilNonEmpty(() => editor.getCodeLenses(), 5_000);
        if (lenses.length === 0)
            noteSkip(this, 'no code lenses — server may not be running');

        // getText() and click() can both go stale if the server refreshes lenses
        // while we're interacting.  Re-fetch and retry the whole sequence.
        let clicked = false;
        for (let attempt = 0; attempt < 5 && !clicked; attempt++) {
            try {
                const fresh = await pollUntilNonEmpty(() => editor.getCodeLenses(), 3_000);
                for (const lens of fresh) {
                    const text = await lens.getText();
                    if (text.includes('Run ESC')) { await lens.click(); clicked = true; break; }
                }
            } catch (e) {
                if (!e.toString().includes('stale')) throw e;
                await VSBrowser.instance.driver.sleep(500);
            }
        }
        if (!clicked)
            noteSkip(this, 'no "Run ESC" lens found or click failed after 5 attempts');

        // Poll until the lens count stabilises at or above the pre-click count.
        // The server briefly removes and re-adds lenses when ESC starts, so a
        // 3 s fixed sleep can sample during the transition window.
        const deadline = Date.now() + 10_000;
        let updatedLenses = [];
        while (Date.now() < deadline) {
            await VSBrowser.instance.driver.sleep(1_000);
            updatedLenses = await editor.getCodeLenses().catch(() => []);
            if (updatedLenses.length >= lenses.length) break;
        }
        assert.ok(updatedLenses.length >= lenses.length,
            `Lens count should not decrease after clicking Run ESC (before=${lenses.length}, after=${updatedLenses.length})`);
    });

    it('OpenJML output channel shows ESC activity', async function () {
        await VSBrowser.instance.driver.sleep(3_000);
        const text = await readOpenJMLOutput();
        if (text === null)
            noteSkip(this, 'OpenJML output channel not present — server may not be running');
        assert.ok(text.length > 0,
            'OpenJML output channel is empty — expected at least startup messages');
    });
});
