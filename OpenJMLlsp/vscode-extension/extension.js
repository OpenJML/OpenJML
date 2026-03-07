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
}

function deactivate() {
    if (!client) return undefined;
    return client.stop();
}

module.exports = { activate, deactivate };
