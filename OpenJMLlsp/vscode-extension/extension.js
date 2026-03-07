'use strict';

/**
 * OpenJML VS Code extension.
 *
 * Starts the OpenJML LSP server (openjml-lsp) as a child process and
 * connects to it via stdio.  The server performs JML type-checking
 * (--check) on every Java file that is opened or edited.
 *
 * The server script is resolved relative to this extension file so that
 * the extension works from any working directory.
 */

const path   = require('path');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function activate(context) {
    // openjml-lsp lives one directory up from the extension folder.
    const serverScript = path.join(__dirname, '..', 'openjml-lsp');

    const serverOptions = {
        command:   serverScript,
        transport: TransportKind.stdio,
    };

    const clientOptions = {
        // Attach to all Java files in any workspace folder.
        documentSelector: [{ scheme: 'file', language: 'java' }],
    };

    client = new LanguageClient(
        'openjml',
        'OpenJML Language Server',
        serverOptions,
        clientOptions
    );

    client.start();
    context.subscriptions.push(client);
}

function deactivate() {
    if (!client) return undefined;
    return client.stop();
}

module.exports = { activate, deactivate };
