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

const fs     = require('fs');
const path   = require('path');
const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

/**
 * Given Java source content and a 0-based cursor line, return the
 * fully-qualified method name (pkg.Class.method) of the method that
 * contains that line, or null if not found.
 *
 * Uses the same heuristic regex as JavaSourceScanner on the server side.
 */
function findMethodFqnAtLine(content, cursorLine) {
    const lines = content.split('\n');

    // Extract package name.
    let pkg = '';
    for (const line of lines) {
        const m = line.match(/^\s*package\s+([\w.]+)\s*;/);
        if (m) { pkg = m[1]; break; }
    }

    // Extract top-level public/protected class name.
    let cls = '';
    for (const line of lines) {
        const m = line.match(/(?:public|protected)\s+(?:(?:abstract|final|sealed|non-sealed)\s+)*(?:class|interface|enum|record)\s+(\w+)/);
        if (m) { cls = m[1]; break; }
    }

    // Find all method declaration start lines.
    const METHOD_RE = /^[ \t]*(?:public|private|protected|static|final|synchronized|abstract|native|default|strictfp).*?(\w+)[ \t]*\(/;
    const methodStarts = [];
    for (let i = 0; i < lines.length; i++) {
        if (/^\s*(?:\/\/|\*|\/\*|@)/.test(lines[i])) continue;
        const m = METHOD_RE.exec(lines[i]);
        if (m) methodStarts.push({ name: m[1], line: i });
    }

    // Find the method whose range contains cursorLine.
    let methodName = null;
    for (let i = 0; i < methodStarts.length; i++) {
        const start = methodStarts[i].line;
        const end = i + 1 < methodStarts.length ? methodStarts[i + 1].line - 1 : lines.length - 1;
        if (cursorLine >= start && cursorLine <= end) {
            methodName = methodStarts[i].name;
            break;
        }
    }
    if (!methodName) return null;
    if (!cls) return methodName;
    if (!pkg) return cls + '.' + methodName;
    return pkg + '.' + cls + '.' + methodName;
}

/**
 * Handle unsaved changes before running ESC.  Returns true if ESC should
 * proceed, false to abort.
 *
 * Behaviour is controlled by the openjml.dirtyFileAction setting:
 *   "ask"  — prompt with Save / Run anyway / Cancel / Always save / Never save
 *   "save" — silently save first, then proceed
 *   "run"  — proceed without saving (ESC sees the last saved disk content)
 *
 * "Always save" and "Never save" update the setting globally so the dialog
 * is not shown again.
 */
async function checkDirtyAndProceed(document) {
    if (!document.isDirty) return true;
    const action = vscode.workspace.getConfiguration('openjml')
                                   .get('dirtyFileAction', 'ask');
    if (action === 'save') {
        await vscode.commands.executeCommand('workbench.action.files.save');
        return true;
    }
    if (action === 'run') {
        return true;
    }
    // action === 'ask'
    const choice = await vscode.window.showWarningMessage(
        'OpenJML: the file has unsaved changes. ESC runs on the saved file on disk and may not reflect your edits.',
        'Save and Run ESC', 'Run anyway', 'Cancel', 'Always save', 'Never save'
    );
    if (choice === 'Cancel' || choice === undefined) return false;
    if (choice === 'Always save') {
        await vscode.workspace.getConfiguration('openjml')
            .update('dirtyFileAction', 'save', vscode.ConfigurationTarget.Global);
        await vscode.commands.executeCommand('workbench.action.files.save');
        return true;
    }
    if (choice === 'Never save') {
        await vscode.workspace.getConfiguration('openjml')
            .update('dirtyFileAction', 'run', vscode.ConfigurationTarget.Global);
        return true;
    }
    if (choice === 'Save and Run ESC') {
        await vscode.commands.executeCommand('workbench.action.files.save');
    }
    return true;
}

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

async function activate(context) {
    const cfg = vscode.workspace.getConfiguration('openjml');
    const configuredPath = cfg.get('serverPath', '').trim();

    // When no path is configured, look for openjml-lsp next to the extension directory.
    // In a development layout (extension.js lives inside the openjml-lsp release tree)
    // the script is one level up.  When installed from a vsix that sibling does not exist;
    // in that case we require the user to set openjml.serverPath explicitly.
    const defaultScript = path.join(__dirname, '..', 'openjml-lsp');
    const serverScript  = configuredPath || (fs.existsSync(defaultScript) ? defaultScript : null);

    console.log('OpenJML: activating, server script =', serverScript);

    if (!serverScript) {
        vscode.window.showErrorMessage(
            'OpenJML: cannot find the openjml-lsp server script. ' +
            'Please install OpenJML (https://github.com/OpenJML/OpenJML/releases) ' +
            'and set the "openjml.serverPath" setting to the full path of the ' +
            'openjml-lsp script from your installation.',
            'Open Settings'
        ).then(choice => {
            if (choice === 'Open Settings') {
                vscode.commands.executeCommand(
                    'workbench.action.openSettings', 'openjml.serverPath');
            }
        });
        return;  // do not start the language client
    }

    // Warn if java.format.enabled is on — it adds a space after // in line comments,
    // changing //@ to // @ and silently disabling all JML annotations.
    // Use workspace state so the user is only asked once per workspace.
    const JAVA_FORMAT_KEY = 'javaFormatWarningHandled';
    if (!context.workspaceState.get(JAVA_FORMAT_KEY)
            && vscode.workspace.getConfiguration('java').get('format.enabled', true)) {
        const choice = await vscode.window.showWarningMessage(
            'OpenJML: java.format.enabled is on. It may change //@ to // @, ' +
            'silently disabling JML annotations.',
            'Disable for this workspace', 'Ignore'
        );
        await context.workspaceState.update(JAVA_FORMAT_KEY, true);
        if (choice === 'Disable for this workspace') {
            try {
                await vscode.workspace.getConfiguration('java')
                    .update('format.enabled', false,
                            vscode.ConfigurationTarget.Workspace);
                vscode.window.showInformationMessage(
                    'OpenJML: Disabled java.format.enabled in workspace settings. ' +
                    'You can still format manually with Shift+Alt+F.');
            } catch (err) {
                vscode.window.showErrorMessage(
                    'OpenJML: Could not update settings: ' + err);
            }
        }
    }

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

            // Trigger ESC on manual save if escTriggerOn == "save".
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

        if (!await checkDirtyAndProceed(editor.document)) return;

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

    // Register "Run ESC for Method" — runs ESC restricted to a single method.
    // When invoked via code lens the uri and methodName args are provided by the lens Command.
    // When invoked via keyboard the active file and cursor position are used to find the method.
    const runEscForMethodCmd = vscode.commands.registerCommand(
            'openjml.runEscForMethod', async (uri, methodName) => {

        if (!uri || !methodName) {
            // Keyboard invocation — derive uri and method from the active editor.
            const editor = vscode.window.activeTextEditor;
            if (!editor || editor.document.languageId !== 'java') {
                vscode.window.showWarningMessage('OpenJML: open a Java file to run ESC on a method.');
                return;
            }
            uri = editor.document.uri.toString();
            const cursorLine = editor.selection.active.line;
            methodName = findMethodFqnAtLine(editor.document.getText(), cursorLine);
            if (!methodName) {
                vscode.window.showWarningMessage('OpenJML: cursor is not inside a recognizable method.');
                return;
            }
        }

        // Warn if the file has unsaved changes (same behaviour as Run ESC).
        const doc = vscode.workspace.textDocuments.find(d => d.uri.toString() === uri);
        if (doc && !await checkDirtyAndProceed(doc)) return;

        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEscForMethod',
                arguments: [uri, methodName],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC failed: ' + err);
        }
    });
    context.subscriptions.push(runEscForMethodCmd);

    // "Save and Run ESC" — saves the active file first, then runs ESC.
    // Uses a normal save (with formatting) so the file is in the same state
    // as any other save.  The java.format.enabled warning at activation
    // handles disabling the one formatter that mangles //@ annotations.
    // The dirty-file warning is skipped because the save happens before ESC starts.
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
