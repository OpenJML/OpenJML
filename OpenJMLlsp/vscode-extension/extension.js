'use strict';

/**
 * OpenJML VS Code extension.
 *
 * Starts the OpenJML LSP server (openjml-lsp) as a child process connected
 * via stdio, and passes user settings (triggerOn, mode, specsPath,
 * solversPath) to the server both at startup (initializationOptions) and
 * whenever they change (workspace/didChangeConfiguration).
 *
 * Settings are in VS Code's settings.json under the "openjml" key, e.g.:
 *   "openjml.triggerOn": "save"
 *   "openjml.mode": "check"
 */

const path   = require('path');
const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function getSettings() {
    const cfg = vscode.workspace.getConfiguration('openjml');
    return {
        triggerOn:   cfg.get('triggerOn',   'edit'),
        mode:        cfg.get('mode',        'check'),
        specsPath:   cfg.get('specsPath',   ''),
        solversPath: cfg.get('solversPath', ''),
    };
}

function activate(context) {
    const serverScript = path.join(__dirname, '..', 'openjml-lsp');
    console.log('OpenJML: activating, server script =', serverScript);

    const serverOptions = {
        command:   serverScript,
        transport: TransportKind.stdio,
    };

    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'java' }],
        // Send current settings to the server on startup.
        initializationOptions: getSettings(),
        // Re-send settings whenever the openjml configuration section changes.
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

    try {
        client.start();
    } catch (err) {
        console.error('OpenJML: failed to start language client:', err);
    }
    context.subscriptions.push(client);
}

function deactivate() {
    if (!client) return undefined;
    return client.stop();
}

module.exports = { activate, deactivate };
