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

    // Note: vscode-languageclient's ExecuteCommandFeature automatically registers
    // 'openjml.runEsc' as a VS Code command when the server declares it in
    // executeCommandProvider.  That handler forwards clicks to the server via
    // workspace/executeCommand.  We must NOT call registerCommand here — doing so
    // causes "command already exists" which crashes activate() and kills the connection.
}

function deactivate() {
    if (!client) return undefined;
    return client.stop();
}

module.exports = { activate, deactivate };
