'use strict';

/**
 * OpenJML VS Code extension.
 *
 * Starts the OpenJML LSP server (openjml-lsp) as a child process connected
 * via stdio.  Two independent checks are supported:
 *
 *   --check (JML type-check): triggered on edit or save (openjml.checkTriggerOn)
 *   --esc   (extended static check): triggered on edit, save, or manually
 *           (openjml.escTriggerOn).  The command "OpenJML: Run ESC" sends an
 *           explicit workspace/executeCommand to the server.
 *
 * Settings are in VS Code's settings.json under the "openjml" key.
 */

const path   = require('path');
const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function getSettings() {
    const cfg = vscode.workspace.getConfiguration('openjml');
    return {
        checkTriggerOn: cfg.get('checkTriggerOn', 'edit'),
        escTriggerOn:   cfg.get('escTriggerOn',   'manual'),
        specsPath:      cfg.get('specsPath',       ''),
        solversPath:    cfg.get('solversPath',     ''),
        sourcePath:     cfg.get('sourcePath',      ''),
        classPath:      cfg.get('classPath',       ''),
    };
}

function activate(context) {
    const cfg = vscode.workspace.getConfiguration('openjml');
    const serverScript = cfg.get('serverPath', '') || path.join(__dirname, '..', 'openjml-lsp');
    console.log('OpenJML: activating, server script =', serverScript);

    const serverOptions = {
        command:   serverScript,
        transport: TransportKind.stdio,
    };

    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'java' }],
        initializationOptions: getSettings(),
        synchronize: {
            configurationSection: 'openjml',
        },
    };

    client = new LanguageClient(
        'openjml',
        'OpenJML Language Server',
        serverOptions,
        clientOptions
    );

    client.start().then(() => {
        console.log('OpenJML: server started successfully');
    }).catch(err => {
        console.error('OpenJML: server failed to start:', err?.message ?? err);
    });
    context.subscriptions.push(client);

    // Track which Java file URIs are about to be saved manually (not by auto-save).
    // onWillSaveTextDocument fires before the save and carries the reason; we use it
    // to mark URIs so that onDidSaveTextDocument can decide whether to trigger ESC.
    const pendingManualSave = new Set();
    context.subscriptions.push(
        vscode.workspace.onWillSaveTextDocument(e => {
            if (e.document.languageId === 'java'
                    && e.reason === vscode.TextDocumentSaveReason.Manual) {
                pendingManualSave.add(e.document.uri.toString());
            }
        })
    );
    context.subscriptions.push(
        vscode.workspace.onDidSaveTextDocument(async doc => {
            if (doc.languageId !== 'java') return;
            const uri = doc.uri.toString();
            const wasManual = pendingManualSave.delete(uri); // always clear, even on auto-save
            if (!wasManual) return;
            const escTriggerOn = vscode.workspace.getConfiguration('openjml')
                                                 .get('escTriggerOn', 'manual');
            if (escTriggerOn !== 'save') return;
            try {
                await client.sendRequest('workspace/executeCommand', {
                    command:   'openjml.runEsc',
                    arguments: [uri],
                });
            } catch (err) {
                // ESC errors are surfaced by the server via diagnostics; ignore here.
            }
        })
    );

    // Register the Run ESC command manually so we can inject the active file's URI.
    // The server does NOT advertise openjml.runEsc in executeCommandProvider; if it did,
    // vscode-languageclient's ExecuteCommandFeature would auto-register the command and
    // invoke it with no arguments, so the URI would never reach the server.
    const escCmd = vscode.commands.registerCommand('openjml.runEsc', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || editor.document.languageId !== 'java') {
            vscode.window.showWarningMessage('OpenJML: open a Java file to run ESC.');
            return;
        }

        // Warn if the file has unsaved changes — ESC runs on the disk file,
        // so results may not reflect what is currently in the editor.
        if (editor.document.isDirty) {
            const warnSetting = vscode.workspace.getConfiguration('openjml')
                                               .get('warnEscOnDirtyFile', true);
            if (warnSetting) {
                const choice = await vscode.window.showWarningMessage(
                    'OpenJML: the file has unsaved changes. ESC runs on the saved file on disk and may not reflect your edits.',
                    'Run anyway', 'Cancel', "Don't warn again"
                );
                if (choice === 'Cancel' || choice === undefined) return;
                if (choice === "Don't warn again") {
                    await vscode.workspace.getConfiguration('openjml')
                        .update('warnEscOnDirtyFile', false,
                                vscode.ConfigurationTarget.Global);
                }
                // 'Run anyway' or "Don't warn again" both fall through to run ESC.
            }
        }

        const uri = editor.document.uri.toString();
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEsc',
                arguments: [uri],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC failed: ' + err);
        }
    });
    context.subscriptions.push(escCmd);

    // "Save and Run ESC" — saves the active file first, then runs ESC.
    // Useful as a keyboard shortcut so a single key gesture persists changes
    // and immediately verifies them.  The dirty-file warning is skipped because
    // the save happens before ESC starts.
    const saveAndEscCmd = vscode.commands.registerCommand('openjml.saveAndRunEsc', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || editor.document.languageId !== 'java') {
            vscode.window.showWarningMessage('OpenJML: open a Java file to run ESC.');
            return;
        }
        await vscode.commands.executeCommand('workbench.action.files.save');
        const uri = editor.document.uri.toString();
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEsc',
                arguments: [uri],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC failed: ' + err);
        }
    });
    context.subscriptions.push(saveAndEscCmd);
}

function deactivate() {
    if (!client) return undefined;
    return client.stop();
}

module.exports = { activate, deactivate };
