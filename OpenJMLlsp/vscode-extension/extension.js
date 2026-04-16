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

const cp     = require('child_process');
const fs     = require('fs');
const path   = require('path');
const vscode = require('vscode');
const { LanguageClient, TransportKind, RevealOutputChannelOn, State } = require('vscode-languageclient/node');

let client;
let outputChannel;

/**
 * {@code true} when the server was stopped intentionally (settings change,
 * deactivate, explicit restart).  Prevents the state-change listener from
 * showing a crash-recovery dialog on deliberate stops.
 */
let intentionalStop = false;

/** The VS Code ExtensionContext — set once in activate(). */
let extensionContext;

/** Status bar item showing the number of running ESC tasks. */
let escStatusBar;

/** Handle returned by setInterval for the ESC-task polling loop, or null. */
let escPollTimer = null;

/**
 * Start (or keep alive) the ESC-task polling loop.
 * Queries the server every 800 ms; updates the status bar with the task count.
 * Stops automatically once the count reaches zero.
 */
function startEscPolling() {
    if (escPollTimer !== null) return;   // already polling
    escPollTimer = setInterval(async () => {
        if (!client) { stopEscPolling(); return; }
        try {
            const uris = await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.getRunningEscTasks',
                arguments: [],
            });
            const n = Array.isArray(uris) ? uris.length : 0;
            if (n === 0) {
                stopEscPolling();
            } else {
                escStatusBar.text = `OpenJML ${n} ESC task${n === 1 ? '' : 's'} running \u2026`;
                escStatusBar.show();
            }
        } catch (_) {
            stopEscPolling();
        }
    }, 800);
}

/** Stop the ESC-task polling loop and hide the status bar item. */
function stopEscPolling() {
    if (escPollTimer !== null) {
        clearInterval(escPollTimer);
        escPollTimer = null;
    }
    escStatusBar.hide();
}

/**
 * Return the absolute path of `name` if it is found on the system PATH,
 * or null if it is not.  Uses `which` on Unix/macOS and `where` on Windows.
 */
function findOnPath(name) {
    const cmd = process.platform === 'win32' ? `where ${name}` : `which ${name}`;
    try {
        return cp.execSync(cmd, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] })
                 .trim().split('\n')[0].trim() || null;
    } catch (_) {
        return null;
    }
}

/**
 * Return true if the language ID is Java or JML (both are handled by this extension).
 * ESC commands only operate on Java files; the document selector covers both.
 */
function isJmlLike(langId) {
    return langId === 'java' || langId === 'jml';
}

/**
 * Return p if it exists and is a regular file, otherwise null.
 */
function fileIfExists(p) {
    try { return fs.statSync(p).isFile() ? p : null; } catch (_) { return null; }
}

/**
 * Resolves the path to the openjml-lsp launcher script.
 * Re-reads the current setting on every call so that preference changes are
 * picked up without reloading the extension.
 *
 * Priority:
 *   1. OPENJML_SERVER_PATH env var (set by launch.json for extension development)
 *   2. openjml.serverPath setting (explicit user config)
 *   3. openjml-lsp file one directory above the extension  (dev / release-zip layout)
 *   4. openjml-lsp on the system PATH  (user added OpenJML install dir to PATH)
 */
function findServerPath() {
    const cfg = vscode.workspace.getConfiguration('openjml');
    const configuredPath = cfg.get('serverPath', '').trim();
    const siblingDir = path.join(__dirname, '..');
    return (process.env.OPENJML_SERVER_PATH || '')
        || configuredPath
        || fileIfExists(path.join(siblingDir, 'openjml-lsp'))
        || findOnPath('openjml-lsp')
        || null;
}

/** Returns true if the server script is present and executable. */
function isServerAvailable() {
    const p = findServerPath();
    if (!p) return false;
    try {
        const stat = fs.statSync(p);
        if (!stat.isFile()) return false;
        // On Unix, check execute permission.  On Windows any .cmd/.bat is runnable.
        if (process.platform !== 'win32') {
            // fs.constants.X_OK = 1
            fs.accessSync(p, fs.constants.X_OK);
        }
        return true;
    } catch (_) {
        return false;
    }
}

/**
 * Loops showing a warning dialog until the server script is found or the user
 * cancels.  Returns the resolved script path, or null if the user cancelled.
 */
async function ensureServerScript() {
    while (true) {
        if (isServerAvailable()) return findServerPath();

        const currentPath = findServerPath() || '(not configured)';
        outputChannel.appendLine(ts() + ' OpenJML server script not found: ' + currentPath);

        const choice = await vscode.window.showWarningMessage(
            'OpenJML: the openjml-lsp server script was not found or is not executable:\n\n' +
            '  ' + currentPath + '\n\n' +
            'Without a running server, all OpenJML features (type-checking, ESC, RAC, ' +
            'syntax coloring, etc.) will be non-functional.\n\n' +
            'Set the "openjml.serverPath" setting to the openjml-lsp script path, ' +
            'then click Retry.',
            'Open Settings', 'Retry', 'Cancel'
        );
        if (choice === 'Open Settings') {
            await vscode.commands.executeCommand('workbench.action.openSettings', 'openjml.serverPath');
            // Loop back to re-check after the user edits the setting.
        } else if (choice === 'Retry') {
            // Loop back to re-check.
        } else {
            // Cancel or dialog dismissed.
            return null;
        }
    }
}

/**
 * Creates, wires, and starts the LanguageClient.  If the server script is not
 * available, shows the retry dialog (ensureServerScript).  If the user cancels
 * the dialog, returns without starting (all commands remain registered but
 * non-functional).
 */
async function startClient() {
    const serverScript = await ensureServerScript();
    if (!serverScript) {
        outputChannel.appendLine(ts() + ' OpenJML server startup cancelled by user.');
        return;
    }

    outputChannel.appendLine(ts() + ' server script: ' + serverScript);

    const serverOptions = {
        command:   serverScript,
        transport: TransportKind.stdio,
    };

    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'java' }, { scheme: 'file', language: 'jml' }],
        outputChannel,          // reuse our named channel; suppresses the auto-created one
        revealOutputChannelOn: RevealOutputChannelOn.Warn,
        initializationOptions: getSettings(),
        synchronize: {
            configurationSection: 'openjml',
        },
        middleware: {
            // Override prepareRename so our server's rename provider takes priority
            // over the Red Hat Java extension for both JML comment positions and
            // regular Java identifiers.  We return the word range at the cursor
            // immediately (without a server round-trip) whenever the cursor is on
            // a Java identifier character; otherwise we fall back to the server.
            prepareRename: (document, position, token, next) => {
                const wordRange = document.getWordRangeAtPosition(
                    position, /[a-zA-Z_$][a-zA-Z0-9_$]*/);
                if (wordRange && !wordRange.isEmpty) {
                    return { range: wordRange, placeholder: document.getText(wordRange) };
                }
                return next(document, position, token);
            },
            // Suppress the LSP-channel semantic tokens in VS Code.  We register a
            // direct DocumentSemanticTokensProvider below so that our JML tokens
            // merge additively with Red Hat's Java tokens instead of competing with
            // them via the LSP provider race.
            provideDocumentSemanticTokens: (_document, _token, _next) => {
                return new vscode.SemanticTokens(new Uint32Array([]));
            },
            window: {
                // Route window/logMessage notifications from the server to our
                // dedicated OpenJML output channel instead of the generic LSP log.
                logMessage: (params, _next) => {
                    outputChannel.appendLine(params.message);
                },
            },
        },
    };

    intentionalStop = false;
    client = new LanguageClient(
        'openjml',
        'OpenJML Language Server',
        serverOptions,
        clientOptions
    );

    // Detect unexpected server death (crash or external kill).
    client.onDidChangeState(event => {
        if (event.newState === State.Stopped && !intentionalStop) {
            showCrashRecoveryDialog();
        }
    });

    // Register the client as a subscription so VS Code disposes it on deactivate.
    extensionContext.subscriptions.push(client);

    client.start().then(() => {
        outputChannel.appendLine(ts() + ' server started');
    }).catch(err => {
        outputChannel.appendLine(ts() + ' server failed to start: ' + (err?.message ?? err));
    });
}

/**
 * Shows a warning dialog telling the user the server has stopped unexpectedly,
 * and offers to restart it.
 */
async function showCrashRecoveryDialog() {
    const serverPath = findServerPath() || '(not configured)';
    outputChannel.appendLine(ts() + ' OpenJML LSP server stopped unexpectedly (path: ' + serverPath + ')');
    const choice = await vscode.window.showWarningMessage(
        'OpenJML: the LSP server has stopped unexpectedly.\n\n' +
        'Server path: ' + serverPath + '\n\n' +
        'Without a running server, all OpenJML features (type-checking, ESC, RAC, ' +
        'syntax coloring, etc.) are non-functional.\n\n' +
        'Click "Restart" to restart the server now.',
        'Restart', 'Continue without OpenJML'
    );
    if (choice === 'Restart') {
        client = null;
        await startClient();
    }
}

/**
 * Shows a warning that the server is not running and offers to restart it.
 * Called from command handlers when {@code client} is null.
 */
function requireServer() {
    vscode.window.showWarningMessage(
        'OpenJML: the server is not running. ' +
        'Without a running server, OpenJML features are non-functional.',
        'Restart Server', 'OK'
    ).then(choice => {
        if (choice === 'Restart Server') {
            client = null;
            startClient();
        }
    });
}

/**
 * Given a .jml TextDocument, find and return the vscode.Uri of the companion .java file.
 *
 * Algorithm:
 *   1. Try <same-dir>/<same-base>.java  (works when spec-file name == class name).
 *   2. Parse the .jml content for the package declaration and the first
 *      public/protected class/interface/enum/record name, then use
 *      workspace.findFiles to locate <pkg/path/ClassName>.java anywhere in the workspace.
 *
 * Returns a vscode.Uri or null if no companion is found.
 */
async function resolveCompanionJavaUri(jmlDoc) {
    // 1. Same-name .java in the same directory
    const simpleUri = jmlDoc.uri.with({ path: jmlDoc.uri.path.replace(/\.jml$/, '.java') });
    try {
        await vscode.workspace.fs.stat(simpleUri);
        return simpleUri;
    } catch (_) {}

    // 2. Parse package and class name from the spec content
    const lines = jmlDoc.getText().split('\n');
    let pkg = '';
    for (const line of lines) {
        const m = line.match(/^\s*package\s+([\w.]+)\s*;/);
        if (m) { pkg = m[1]; break; }
    }
    let cls = '';
    let inBC = false;
    for (const line of lines) {
        const s = line.trimStart();
        if (inBC) { if (s.includes('*/')) inBC = false; continue; }
        if (s.startsWith('//')) continue;
        if (s.startsWith('/*')) { if (!s.includes('*/')) inBC = true; continue; }
        const m = line.match(/^[ \t]*(?:public|protected)\s+(?:(?:abstract|final|sealed|non-sealed)\s+)*(?:class|interface|enum|record)\s+(\w+)/);
        if (m) { cls = m[1]; break; }
    }
    if (!cls) return null;

    const relPath = (pkg ? pkg.replace(/\./g, '/') + '/' : '') + cls + '.java';
    const matches = await vscode.workspace.findFiles('**/' + cls + '.java', '**/node_modules/**', 10);
    // Prefer the match whose path ends with the full package-relative path
    const best = matches.find(u => u.path.replace(/\\/g, '/').endsWith(relPath));
    return best || (matches.length > 0 ? matches[0] : null);
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
        await document.save();
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
        await document.save();
        return true;
    }
    if (choice === 'Never save') {
        await vscode.workspace.getConfiguration('openjml')
            .update('dirtyFileAction', 'run', vscode.ConfigurationTarget.Global);
        return true;
    }
    if (choice === 'Save and Run ESC') {
        await document.save();
    }
    return true;
}

function getSettings() {
    const cfg = vscode.workspace.getConfiguration('openjml');
    const sep = process.platform === 'win32' ? ';' : ':';
    const folders = vscode.workspace.workspaceFolders || [];
    const workspaceFolderPaths = folders.map(f => f.uri.fsPath).join(sep);
    return {
        checkTriggerOn:          cfg.get('checkTriggerOn',          'edit'),
        escTriggerOn:            cfg.get('escTriggerOn',            'manual'),
        propertiesFile:          cfg.get('propertiesFile',          ''),
        specsPath:               cfg.get('specsPath',               ''),
        solversPath:             cfg.get('solversPath',             ''),
        sourcePath:              cfg.get('sourcePath',              ''),
        classPath:               cfg.get('classPath',               ''),
        racOutputDir:            cfg.get('racOutputDir',            ''),
        syntaxColoringScope:     cfg.get('syntaxColoringScope',     'preserve Java coloring'),
        syntaxColoringStrategy:  cfg.get('syntaxColoringStrategy',  'ast'),
        escEngine:               cfg.get('escEngine',               'subprocess'),
        escThreads:              cfg.get('escThreads',              5),
        useIntegratedOutline:    cfg.get('useIntegratedOutline',    true),
        client:                  'vscode-java',
        workspaceFolderPaths:    workspaceFolderPaths,
    };
}

function ts() {
    return new Date().toTimeString().slice(0, 8);
}

/**
 * Resolve the filesystem paths to operate on, given optional Explorer context arguments.
 *
 * When a command is invoked from the Explorer context menu, VS Code passes:
 *   explorerUri       — the right-clicked item's vscode.Uri
 *   explorerSelection — array of all selected vscode.Uri values (multi-select)
 *
 * When invoked from the editor title/context menu or command palette, both are
 * undefined and we fall back to the active editor's file.
 *
 * Returns an array of fsPath strings, or null if no target can be determined.
 */
function resolveTargetPaths(explorerUri, explorerSelection) {
    if (explorerSelection && explorerSelection.length > 0) {
        return explorerSelection.map(u => u.fsPath || u.toString());
    }
    if (explorerUri) {
        return [explorerUri.fsPath || explorerUri.toString()];
    }
    // Fall back to the active editor.
    const editor = vscode.window.activeTextEditor;
    if (editor && isJmlLike(editor.document.languageId)) {
        return [editor.document.uri.fsPath];
    }
    vscode.window.showWarningMessage('OpenJML: open a Java or JML file, or select one in the Explorer.');
    return null;
}

/**
 * Returns the single-element command prefix used by all openjml.* commands.
 * args[0] is the project ID; an empty string means "use global/single-project settings".
 * Path configuration (sourcePath, classPath, etc.) is sent once at initialization
 * via initializationOptions and updated via workspace/didChangeConfiguration.
 */
function commandPrefix() {
    return [''];
}

async function activate(context) {
    extensionContext = context;
    outputChannel = vscode.window.createOutputChannel('OpenJML');
    context.subscriptions.push(outputChannel);
    outputChannel.appendLine(ts() + ' OpenJML extension started');

    // Status bar item: shown while ESC tasks are in flight.
    escStatusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 10);
    escStatusBar.tooltip = 'OpenJML extended static checking is running';
    escStatusBar.command = 'openjml.cancelEsc';
    context.subscriptions.push(escStatusBar);

    // Always register commands so VS Code can find them regardless of server state.
    // Each command checks whether the client is available before sending a request.

    // Register the Run ESC command manually so we can inject the active file's URI.
    // The server does NOT advertise openjml.runEsc in executeCommandProvider; if it did,
    // vscode-languageclient's ExecuteCommandFeature would auto-register the command and
    // invoke it with no arguments, so the URI would never reach the server.
    const escCmd = vscode.commands.registerCommand('openjml.runEsc', async () => {
        if (!client) { requireServer(); return; }
        const editor = vscode.window.activeTextEditor;
        if (!editor || !isJmlLike(editor.document.languageId)) {
            vscode.window.showWarningMessage('OpenJML: open a Java or JML file to run ESC.');
            return;
        }

        let doc = editor.document;
        if (doc.languageId === 'jml') {
            const javaUri = await resolveCompanionJavaUri(doc);
            if (!javaUri) {
                vscode.window.showWarningMessage('OpenJML: cannot find the companion .java file for this .jml spec.');
                return;
            }
            doc = await vscode.workspace.openTextDocument(javaUri);
        }

        if (!await checkDirtyAndProceed(doc)) return;

        const fsPath = doc.uri.fsPath;
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEsc',
                arguments: [...commandPrefix(), fsPath],
            });
            startEscPolling();
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC failed: ' + err);
        }
    });
    context.subscriptions.push(escCmd);

    // "Check JML" — explicitly triggers the JML type-check (--check) on the
    // active file or a file/folder selected in the Explorer.
    const checkJmlCmd = vscode.commands.registerCommand('openjml.checkJml',
            async (explorerUri, explorerSelection) => {
        if (!client) { requireServer(); return; }
        const paths = resolveTargetPaths(explorerUri, explorerSelection);
        if (!paths) return;
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.checkJml',
                arguments: [...commandPrefix(), ...paths],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML check failed: ' + err);
        }
    });
    context.subscriptions.push(checkJmlCmd);

    // Register "Run ESC for Method" — runs ESC restricted to a single method.
    // When invoked via code lens the uri and methodName args are provided by the lens Command.
    // When invoked via keyboard the active file and cursor position are used.  The method FQN
    // is obtained from the server-provided code lenses (which use Utils.uniqueSymbolName and
    // therefore correctly identify methods in secondary, nested, local, and anonymous classes).
    const runEscForMethodCmd = vscode.commands.registerCommand(
            'openjml.runEscForMethod', async (uri, methodName) => {
        if (!client) { requireServer(); return; }

        if (typeof uri !== 'string' || typeof methodName !== 'string') {
            // Invoked without proper args (keyboard, menu, command palette) — derive from active editor.
            const editor = vscode.window.activeTextEditor;
            if (!editor || !isJmlLike(editor.document.languageId)) {
                vscode.window.showWarningMessage('OpenJML: open a Java or JML file to run ESC on a method.');
                return;
            }
            const cursorLine = editor.selection.active.line;

            // Ask VS Code for the code lenses on this document (includes our server's lenses).
            // Filter to per-method ESC lenses (non-empty methodName argument) and find the
            // last one whose start line is at or before the cursor.  This gives the correct
            // AST-derived FQN for all class types including secondary, nested, and local classes.
            let matchedLens = null;
            try {
                const allLenses = await vscode.commands.executeCommand(
                    'vscode.executeCodeLensProvider', editor.document.uri, 50);
                const methodLenses = (allLenses || [])
                    .filter(l => l.command?.command === 'openjml.runEscForMethod'
                              && l.command.arguments?.[1])  // non-empty = per-method, not whole-file
                    .sort((a, b) => a.range.start.line - b.range.start.line);
                for (const l of methodLenses) {
                    if (l.range.start.line <= cursorLine) matchedLens = l;
                    else break;
                }
            } catch (_) { /* code lens provider unavailable — fall through to warning */ }

            if (!matchedLens) {
                vscode.window.showWarningMessage('OpenJML: cursor is not inside a recognizable method (no code lens found — try triggering a type-check first).');
                return;
            }
            [uri, methodName] = matchedLens.command.arguments;
        }

        // Warn if the file has unsaved changes (same behaviour as Run ESC).
        const doc = vscode.workspace.textDocuments.find(d => d.uri.toString() === uri);
        if (doc && !await checkDirtyAndProceed(doc)) return;

        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEscForMethod',
                arguments: [...commandPrefix(), uri, methodName],
            });
            startEscPolling();
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC failed: ' + err);
        }
    });
    context.subscriptions.push(runEscForMethodCmd);

    // "Run ESC Split by File" — verifies each file in the target set independently,
    // so a failure in one file does not block the others.
    const runEscSplitByFileCmd = vscode.commands.registerCommand('openjml.runEscSplitByFile',
            async (explorerUri, explorerSelection) => {
        if (!client) { requireServer(); return; }
        const paths = resolveTargetPaths(explorerUri, explorerSelection);
        if (!paths) return;
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEscSplitByFile',
                arguments: [...commandPrefix(), ...paths],
            });
            startEscPolling();
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC split-by-file failed: ' + err);
        }
    });
    context.subscriptions.push(runEscSplitByFileCmd);

    // "Run ESC Split by Method" — verifies each method independently, running them
    // concurrently; faster than whole-file ESC when many methods are present.
    const runEscSplitByMethodCmd = vscode.commands.registerCommand('openjml.runEscSplitByMethod',
            async (explorerUri, explorerSelection) => {
        if (!client) { requireServer(); return; }
        const paths = resolveTargetPaths(explorerUri, explorerSelection);
        if (!paths) return;
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEscSplitByMethod',
                arguments: [...commandPrefix(), ...paths],
            });
            startEscPolling();
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC split-by-method failed: ' + err);
        }
    });
    context.subscriptions.push(runEscSplitByMethodCmd);

    // "Save and Run ESC" — saves the active file first, then runs ESC.
    // Uses a normal save (with formatting) so the file is in the same state
    // as any other save.  The java.format.enabled warning at activation
    // handles disabling the one formatter that mangles //@ annotations.
    // The dirty-file warning is skipped because the save happens before ESC starts.
    const saveAndEscCmd = vscode.commands.registerCommand('openjml.saveAndRunEsc', async () => {
        if (!client) { requireServer(); return; }
        const editor = vscode.window.activeTextEditor;
        if (!editor || !isJmlLike(editor.document.languageId)) {
            vscode.window.showWarningMessage('OpenJML: open a Java or JML file to run ESC.');
            return;
        }
        await editor.document.save();
        let targetUri = editor.document.uri;
        if (editor.document.languageId === 'jml') {
            const javaUri = await resolveCompanionJavaUri(editor.document);
            if (!javaUri) {
                vscode.window.showWarningMessage('OpenJML: cannot find the companion .java file for this .jml spec.');
                return;
            }
            targetUri = javaUri;
        }
        const fsPath = targetUri.fsPath;
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEsc',
                arguments: [...commandPrefix(), fsPath],
            });
            startEscPolling();
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC failed: ' + err);
        }
    });
    context.subscriptions.push(saveAndEscCmd);

    // "Compile RAC" — compiles the focused Java file with --rac, producing class files
    // with embedded assertion checks.  Output directory is controlled by openjml.racOutputDir.
    const racCmd = vscode.commands.registerCommand('openjml.runRac',
            async (explorerUri, explorerSelection) => {
        if (!client) { requireServer(); return; }
        const paths = resolveTargetPaths(explorerUri, explorerSelection);
        if (!paths) return;
        const outputDir = getSettings().racOutputDir || '';
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runRac',
                arguments: [...commandPrefix(), outputDir, ...paths],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML RAC compile failed: ' + err);
        }
    });
    context.subscriptions.push(racCmd);

    // "Run ESC on Project" — runs ESC on all workspace folders.
    // Requires at least one workspace folder to be open.
    const escDirCmd = vscode.commands.registerCommand('openjml.runEscDir', async () => {
        if (!client) { requireServer(); return; }
        const folders = vscode.workspace.workspaceFolders;
        if (!folders || folders.length === 0) {
            vscode.window.showWarningMessage(
                'OpenJML: no workspace folder is open. Open a folder to run ESC on the project.');
            return;
        }
        const paths = folders.map(f => f.uri.fsPath);
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEsc',
                arguments: [...commandPrefix(), ...paths],
            });
            startEscPolling();
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC on project failed: ' + err);
        }
    });
    context.subscriptions.push(escDirCmd);

    // "Clear Caches and Reindex" — clears all server-side caches and restarts
    // from scratch: re-checks open files and re-indexes the workspace.
    const clearCmd = vscode.commands.registerCommand('openjml.clearAndReindex', async () => {
        if (!client) { requireServer(); return; }
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.clearAndReindex',
                arguments: [],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML clear-and-reindex failed: ' + err);
        }
    });
    context.subscriptions.push(clearCmd);

    // "Index Project" — pre-indexes the workspace for faster symbol lookup,
    // without clearing existing check/ESC results.
    const indexProjectCmd = vscode.commands.registerCommand('openjml.indexProject',
            async (explorerUri, explorerSelection) => {
        if (!client) { requireServer(); return; }
        const folders = vscode.workspace.workspaceFolders;
        const paths = explorerUri
            ? resolveTargetPaths(explorerUri, explorerSelection)
            : (folders ? folders.map(f => f.uri.fsPath) : null);
        if (!paths) {
            vscode.window.showWarningMessage('OpenJML: no folder to index.');
            return;
        }
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.indexProject',
                arguments: [...commandPrefix(), ...paths],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML index project failed: ' + err);
        }
    });
    context.subscriptions.push(indexProjectCmd);

    const clearMarkersCmd = vscode.commands.registerCommand('openjml.clearMarkers', async () => {
        if (!client) { requireServer(); return; }
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.clearMarkers',
                arguments: [],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML clear markers failed: ' + err);
        }
    });
    context.subscriptions.push(clearMarkersCmd);

    // "Clear Markers for Selection" — clears markers only for the selected file(s)
    // or folder(s) in the Explorer, rather than all markers in the workspace.
    const clearMarkersSelectedCmd = vscode.commands.registerCommand('openjml.clearMarkersSelected',
            async (explorerUri, explorerSelection) => {
        if (!client) { requireServer(); return; }
        const paths = resolveTargetPaths(explorerUri, explorerSelection);
        if (!paths) return;
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.clearMarkers',
                arguments: [...paths],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML clear markers failed: ' + err);
        }
    });
    context.subscriptions.push(clearMarkersSelectedCmd);

    // Cancel all running ESC tasks.
    // First queries the server for which files are currently being verified so the
    // confirmation dialog can list them; sends the cancel only if the user confirms.
    const cancelEscCmd = vscode.commands.registerCommand('openjml.cancelEsc', async () => {
        if (!client) { requireServer(); return; }
        try {
            const uris = await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.getRunningEscTasks',
                arguments: [],
            }) || [];

            if (!uris || uris.length === 0) {
                vscode.window.showInformationMessage('No ESC verification tasks are currently running.');
                return;
            }

            const names = uris.map(u => u.replace(/.*\//, ''));
            const list  = names.map(n => `  \u2022 ${n}`).join('\n');
            const choice = await vscode.window.showWarningMessage(
                `Cancel ESC verification of:\n${list}`,
                { modal: true },
                'Cancel ESC'
            );
            if (choice !== 'Cancel ESC') return;

            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.cancelEsc',
                arguments: [],
            });
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML cancel ESC failed: ' + err);
        }
    });
    context.subscriptions.push(cancelEscCmd);

    // Warn if java.format.enabled is on — it adds a space after // in line comments,
    // changing //@ to // @ and silently disabling all JML annotations.
    // Use workspace state so the user is only asked once per workspace.
    // Wrap the entire block so that a missing workspace never aborts activation.
    try {
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
    } catch (_) {
        // No workspace open — skip the java.format.enabled check silently.
    }

    // When openjml.serverPath changes, stop the current server and restart at the
    // new path.  Other openjml.* changes are forwarded to the running server by
    // vscode-languageclient's synchronize.configurationSection mechanism.
    context.subscriptions.push(
        vscode.workspace.onDidChangeConfiguration(async e => {
            if (!e.affectsConfiguration('openjml.serverPath')) return;
            outputChannel.appendLine(ts() + ' Server path changed; stopping current OpenJML LSP server.');
            if (client) {
                intentionalStop = true;
                await client.stop();
                client = null;
            }
            await startClient();
        })
    );

    // When workspace folders are added or removed, notify the server so it can
    // update its workspaceFolderPaths and re-register file watchers accordingly.
    // Workspace folders are not part of openjml.* config, so we send manually.
    context.subscriptions.push(
        vscode.workspace.onDidChangeWorkspaceFolders(() => {
            if (!client) return;
            const sep = process.platform === 'win32' ? ';' : ':';
            const folders = vscode.workspace.workspaceFolders || [];
            const paths = folders.map(f => f.uri.fsPath).join(sep);
            client.sendNotification('workspace/didChangeConfiguration', {
                settings: { openjml: { workspaceFolderPaths: paths } }
            });
        })
    );

    // Register a direct DocumentSemanticTokensProvider for JML syntax colouring.
    // This runs independently of (and merges additively with) the Red Hat Java
    // extension's semantic tokens, avoiding the LSP-channel provider race.
    // Token types must match SemanticTokensProvider.TOKEN_TYPES on the server.
    const jmlLegend = new vscode.SemanticTokensLegend(['keyword', 'macro', 'variable'], []);
    const jmlTokensProvider = vscode.languages.registerDocumentSemanticTokensProvider(
        [{ language: 'java' }, { language: 'jml' }],
        {
            async provideDocumentSemanticTokens(document) {
                if (!client) return new vscode.SemanticTokens(new Uint32Array([]));
                try {
                    const data = await client.sendRequest('workspace/executeCommand', {
                        command:   'openjml.getSemanticTokens',
                        arguments: [document.uri.toString()],
                    });
                    if (!Array.isArray(data) || data.length === 0)
                        return new vscode.SemanticTokens(new Uint32Array([]));
                    return new vscode.SemanticTokens(new Uint32Array(data));
                } catch (_) {
                    return new vscode.SemanticTokens(new Uint32Array([]));
                }
            },
        },
        jmlLegend
    );
    context.subscriptions.push(jmlTokensProvider);

    // When focus returns to an already-open Java file, trigger a --check recheck so
    // that stale diagnostics from fixed dependencies are cleared without requiring
    // the user to make an edit.  A short debounce (200 ms) avoids spurious requests
    // during rapid tab switches.
    let focusDebounceTimer = null;
    context.subscriptions.push(
        vscode.window.onDidChangeActiveTextEditor(editor => {
            if (!editor || !isJmlLike(editor.document.languageId)) return;
            const uri = editor.document.uri.toString();
            if (focusDebounceTimer) clearTimeout(focusDebounceTimer);
            focusDebounceTimer = setTimeout(() => {
                focusDebounceTimer = null;
                if (!client) return;
                client.sendRequest('workspace/executeCommand', {
                    command:   'openjml.focusFile',
                    arguments: [uri],
                }).catch(() => {});  // ignore errors (server may not be ready)
            }, 200);
        })
    );

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
            if (!isJmlLike(doc.languageId)) return;
            const uri = doc.uri.toString();
            const wasManual = pendingManualSave.delete(uri); // always clear, even on auto-save

            // Trigger ESC on manual save if escTriggerOn == "save".
            if (!wasManual) return;
            const escTriggerOn = vscode.workspace.getConfiguration('openjml')
                                                 .get('escTriggerOn', 'manual');
            if (escTriggerOn !== 'save') return;
            if (!client) return;
            try {
                await client.sendRequest('workspace/executeCommand', {
                    command:   'openjml.runEsc',
                    arguments: [...commandPrefix(), doc.uri.fsPath],
                });
                startEscPolling();
            } catch (err) {
                // ESC errors are surfaced by the server via diagnostics; ignore here.
            }
        })
    );

    // Start the language client (shows retry dialog if script not found).
    await startClient();
}

function deactivate() {
    if (!client) return undefined;
    intentionalStop = true;
    return client.stop();
}

module.exports = { activate, deactivate };
