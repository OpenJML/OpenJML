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
 * Given Java source content and a 0-based cursor line, return the
 * fully-qualified method name (pkg.Class.method) of the method that
 * contains that line, or null if not found.
 *
 * Uses the same heuristic regex as JavaSourceScanner.methodFqn() on the server side.
 * If the regex logic changes here it MUST be updated there too (and vice versa).
 */
function findMethodFqnAtLine(content, cursorLine) {
    const lines = content.split('\n');

    // Extract package name.
    let pkg = '';
    for (const line of lines) {
        const m = line.match(/^\s*package\s+([\w.]+)\s*;/);
        if (m) { pkg = m[1]; break; }
    }

    // Extract top-level public/protected class name, skipping block-comment lines.
    let cls = '';
    let inBlockComment = false;
    for (const line of lines) {
        const stripped = line.trimStart();
        if (inBlockComment) { if (stripped.includes('*/')) inBlockComment = false; continue; }
        if (stripped.startsWith('//')) continue;
        if (stripped.startsWith('/*')) { if (!stripped.includes('*/')) inBlockComment = true; continue; }
        const m = line.match(/^[ \t]*(?:public|protected)\s+(?:(?:abstract|final|sealed|non-sealed)\s+)*(?:class|interface|enum|record)\s+(\w+)/);
        if (m) { cls = m[1]; break; }
    }

    // Find all method declaration start lines.
    const METHOD_RE = /^[ \t]*(?:public|private|protected|static|final|synchronized|abstract|native|default|strictfp)[^(;{]*(\w+)[ \t]*\(/;
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
    return {
        checkTriggerOn:          cfg.get('checkTriggerOn',          'edit'),
        escTriggerOn:            cfg.get('escTriggerOn',            'manual'),
        propertiesFile:          cfg.get('propertiesFile',          ''),
        specsPath:               cfg.get('specsPath',               ''),
        solversPath:             cfg.get('solversPath',             ''),
        sourcePath:              cfg.get('sourcePath',              ''),
        classPath:               cfg.get('classPath',               ''),
        racOutputDir:            cfg.get('racOutputDir',            ''),
        syntaxColoringStrategy:  cfg.get('syntaxColoringStrategy',  'ast'),
        escEngine:               cfg.get('escEngine',               'subprocess'),
        escThreads:              cfg.get('escThreads',              5),
        useIntegratedOutline:    cfg.get('useIntegratedOutline',    true),
    };
}

function ts() {
    return new Date().toTimeString().slice(0, 8);
}

/**
 * Build the fixed 4-element command prefix used by all openjml.* commands:
 *   [sourcePath, classPath, specsPath, propertiesFile]
 * Empty strings are used for absent values so that argument positions are fixed.
 */
function commandPrefix() {
    const s = getSettings();
    return [s.sourcePath || '', s.classPath || '', s.specsPath || '', s.propertiesFile || ''];
}

async function activate(context) {
    extensionContext = context;
    outputChannel = vscode.window.createOutputChannel('OpenJML');
    context.subscriptions.push(outputChannel);
    outputChannel.appendLine(ts() + ' OpenJML extension started');

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
        if (!client) { requireServer(); return; }

        if (typeof uri !== 'string' || typeof methodName !== 'string') {
            // Invoked without proper args (keyboard, menu, command palette) — derive from active editor.
            const editor = vscode.window.activeTextEditor;
            if (!editor || !isJmlLike(editor.document.languageId)) {
                vscode.window.showWarningMessage('OpenJML: open a Java or JML file to run ESC on a method.');
                return;
            }
            // For .jml files: extract the method FQN from the spec content (spec files have
            // method stubs matching the .java signatures), then redirect to the companion .java.
            const cursorLine = editor.selection.active.line;
            methodName = findMethodFqnAtLine(editor.document.getText(), cursorLine);
            if (!methodName) {
                vscode.window.showWarningMessage('OpenJML: cursor is not inside a recognizable method.');
                return;
            }
            if (editor.document.languageId === 'jml') {
                const javaUri = await resolveCompanionJavaUri(editor.document);
                if (!javaUri) {
                    vscode.window.showWarningMessage('OpenJML: cannot find the companion .java file for this .jml spec.');
                    return;
                }
                uri = javaUri.toString();
            } else {
                uri = editor.document.uri.toString();
            }
        }

        // Warn if the file has unsaved changes (same behaviour as Run ESC).
        const doc = vscode.workspace.textDocuments.find(d => d.uri.toString() === uri);
        if (doc && !await checkDirtyAndProceed(doc)) return;

        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runEscForMethod',
                arguments: [...commandPrefix(), uri, methodName],
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
        } catch (err) {
            vscode.window.showErrorMessage('OpenJML ESC failed: ' + err);
        }
    });
    context.subscriptions.push(saveAndEscCmd);

    // "Compile RAC" — compiles the focused Java file with --rac, producing class files
    // with embedded assertion checks.  Output directory is controlled by openjml.racOutputDir.
    const racCmd = vscode.commands.registerCommand('openjml.runRac', async () => {
        if (!client) { requireServer(); return; }
        const editor = vscode.window.activeTextEditor;
        if (!editor || !isJmlLike(editor.document.languageId)) {
            vscode.window.showWarningMessage('OpenJML: open a Java or JML file to compile RAC.');
            return;
        }
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
        const outputDir = getSettings().racOutputDir || '';
        try {
            await client.sendRequest('workspace/executeCommand', {
                command:   'openjml.runRac',
                arguments: [...commandPrefix(), outputDir, fsPath],
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

    // Register a direct DocumentSemanticTokensProvider for JML syntax colouring.
    // This runs independently of (and merges additively with) the Red Hat Java
    // extension's semantic tokens, avoiding the LSP-channel provider race.
    // Token types must match SemanticTokensProvider.TOKEN_TYPES on the server.
    const jmlLegend = new vscode.SemanticTokensLegend(['keyword', 'macro'], []);
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
