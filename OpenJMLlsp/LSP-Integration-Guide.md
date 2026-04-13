# OpenJML Language Server — Integration Guide

David R. Cok -- 5 April 2026 (cf. https://github.com/OpenJML/OpenJML)

This document describes how to connect an LSP client to the OpenJML language server.
It covers the server's capabilities, configuration, wire protocol, and known limitations.
The intended audience is a developer integrating the server into an editor, IDE, or
build tool. Note that some such integrations are available as companion projects to this one
in the OpenJML github project; as of this writing these are VSCode and Eclipse.

---

## Overview

The OpenJML language server provides Java Modeling Language (JML) checking for Java
source files.  The OpenJML tool is built on OpenJDK, so this server is also an
OpenJDK language server, with JML capability included.

Besides conventional LSP services (e.g., syntax coloring),
the server enables some OpenJML capabilities. These are the same capabilities that
are available in the OpenJML command-line tool.

- **`--check`** — JML type-checking. Fast; runs on every edit or save. Reports syntax
  errors, type errors, and JML annotation errors as LSP diagnostics.

- **`--esc`** — Extended Static Checking. Slower; invokes an SMT solver to prove or
  disprove JML specifications such as method postconditions and invariants. Reports verification failures as LSP
  diagnostics and updates per-method status badges (code lenses).

- **`--rac`** - Compile Java code with JML assertions as .class files with runtime checks ("Runtime-Assertion-Checking").

The server links in OpenJML and they run together in a single JVM process.
That process may spawn one or more subprocesses to execute SMT proof checks.
These checking commands run inside this one server process, though some commands may run 
on separate, concurrent threads.
Their diagnostics, perhaps accumulated,
are sent to the client using a `textDocument/publishDiagnostics` notification.

---

## Starting the Server

### Transport

The server communicates with the client exclusively over **stdio** (JSON-RPC on stdin/
stdout). There is no TCP socket or named-pipe option.

Stderr from the server and openjml is redirected to a log file by the launcher script, so Java
stack traces and internal debug messages go there, not to the client.
In the dev launcher (no bundled `jdk/` directory) the log is `/tmp/openjml-lsp-debug.log`, truncated on each restart.
In a release installation the log is `~/.openjml/logs/openjml-lsp-<pid>.log`, unique per server instance.
Either default can be overridden by setting `OPENJML_LSP_LOG` before starting the server.

### Launcher Script

The server is started by the `openjml-lsp` bash script in the installation root:

```
openjml-lsp
```

No arguments are required or supported on the command line; all configuration is passed
through LSP initialization options or `workspace/didChangeConfiguration` or environment variables.

The server is released as part of an OpenJML release and
requires an installation of OpenJML to operate. 

The script expects one of two layouts:

- **Release layout** (`jdk/` sibling directory present): uses `jdk/`, `openjml-lsp.jar`,
  and `lsp/org.eclipse.lsp4j-*.jar` relative to the installation directory. A public OpenJML release,
  unzipped into some empty directory, will have the correct layout.
- **Development layout** (sibling `OpenJMLsrc/` folder): uses the build output from
  `OpenJMLsrc/build/*/jdk` and `build/openjml-lsp.jar` from the `OpenJMLlsp` directory.
  An OpenJML development environment, as described in the OpenJML wiki pages, has this layout.

FIXME: double-check all the above paths

### Required Files

| File | Purpose |
|---|---|
| `lsp/openjml-lsp.jar` | Server logic |
| `lsp/org.eclipse.lsp4j-1.0.0.jar` | LSP4J protocol library |
| `lsp/org.eclipse.lsp4j.jsonrpc-1.0.0.jar` | JSON-RPC transport |
| `jdk/bin/java` | JDK used to run the server (bundled with OpenJML) |

### Environment Variables

The launcher sets these if not already present in the environment:

| Variable | Default | Purpose |
|---|---|---|
| `OPENJML_INSTALL` | Directory containing `openjml-lsp` script | Root of the OpenJML installation |
| `OPENJML_SPECS` | `$OPENJML_INSTALL/specs` | Path to bundled JML specification files |
| `OPENJML_SOLVERS` | `$OPENJML_INSTALL` | Directory containing SMT solver binaries |

A client may override any of these before spawning the server process. They serve as
fallbacks when the equivalent settings are not provided via LSP configuration.

### Eclipse-only: Server Path System Property

The Eclipse plugin resolves the `openjml-lsp` launcher path in this order:

1. The value stored in the OpenJML Preferences page (`openjml.lspServerPath`).
2. The Java system property `openjml.lsp.server.path` — intended for the test harness
   and development setups where modifying workspace preferences is inconvenient.
3. The Eclipse install directory (release layout).
4. `openjml-lsp` on `PATH` (last resort).

To use option 2, pass `-Dopenjml.lsp.server.path=/path/to/openjml-lsp` in the Eclipse
JVM arguments (e.g. in `eclipse.ini` or a launch configuration).

### JVM Notes

The server's JVM requires several `--add-exports` flags to expose Gson (which is bundled
inside `jdk.compiler`) and other OpenJDK internals to the unnamed module used by LSP4J for JSON-RPC serialization.
These flags are set automatically by the launcher script; client integrators do not need
to set them.

Do **not** put a separate Gson jar on the classpath; that creates a split-package that the JVM
will refuse to load.

---

## LSP Handshake

### `initialize` Request

The server reads configuration from `initializationOptions` in the `initialize` request.
The value is deserialized directly as an `OpenJMLSettings` object (no enclosing key).

Example:

```json
{
  "initializationOptions": {
    "specsPath": "/path/to/Specs/specs",
    "solversPath": "/path/to/Solvers",
    "checkTriggerOn": "edit",
    "escTriggerOn": "manual"
  }
}
```

See the [Configuration](#configuration) section for all recognized fields.

### `initialize` Response (ServerCapabilities)

The server advertises the following capabilities:

| Capability | Value |
|---|---|
| `textDocumentSync` | `2` (Incremental) by default; `1` (Full) when `incrementalSync` is `false` |
| `hoverProvider` | `true` |
| `codeLensProvider` | `{ "resolveProvider": false }` |
| `completionProvider` | trigger characters: `\`, `@` |
| `documentSymbolProvider` | `true` |
| `foldingRangeProvider` | `true` |
| `workspaceSymbolProvider` | `true` |
| `definitionProvider` | `true` |
| `declarationProvider` | `true` |
| `referencesProvider` | `true` |
| `renameProvider` | `{ "prepareProvider": true }` |
| `signatureHelpProvider` | trigger characters: `(`, `,` |
| `semanticTokensProvider` | full-file; see legend in response |
| `inlayHintProvider` | `{ "resolveProvider": false }` — shows inferred types of `var`-declared locals |

`textDocumentSync: Incremental` (default) means the client sends only the changed
ranges on each `textDocument/didChange` notification; the server applies them
internally and passes the reconstructed full text to OpenJML.  Setting
`incrementalSync: false` reverts to `Full` (client sends entire file each time).

---

## Configuration

Settings arrive via two channels:

1. **`initializationOptions`** in the `initialize` request — values applied once at
   startup. The JSON object is deserialized directly as an `OpenJMLSettings` object.

2. **`workspace/didChangeConfiguration`** — runtime updates. The notification's
   `settings` object must have an `"openjml"` key; the value is an `OpenJMLSettings`-
   shaped JSON object. Only non-null fields overwrite the current settings, so partial
   updates are safe.

Example `workspace/didChangeConfiguration` payload:

```json
{
  "settings": {
    "openjml": {
      "specsPath": "/path/to/Specs/specs",
      "solversPath": "/path/to/Solvers",
      "checkTriggerOn": "save"
    }
  }
}
```

### Global Settings Reference

These fields apply to the server as a whole (default settings used when no per-project
settings match a given file):

| Field | Type | Default | Description |
|---|---|---|---|
| `specsPath` | string | env `OPENJML_SPECS` | Path to JML specification files, passed as `--specs-path` |
| `solversPath` | string | env `OPENJML_SOLVERS` | Path to SMT solver binaries, passed as `--solvers-path` |
| `sourcePath` | string | none | Source root(s) for cross-file references (see note on effective sourcepath below) |
| `classPath` | string | none | Classpath for pre-compiled dependencies, passed as `-classpath`; also used as a sourcepath fallback (see note) |
| `checkTriggerOn` | string | `"edit"` | When to run `--check`: `"edit"` or `"save"` |
| `escTriggerOn` | string | `"manual"` | When to run `--esc`: `"manual"`, `"save"`, or `"edit"` (see note) |
| `incrementalSync` | boolean | `true` | When `true`, advertise `Incremental` sync and apply ranged edits internally; when `false`, revert to `Full` sync |
| `javaMode` | string | `"full"` | Java-capability mode: `"full"` enables all Java+JML capabilities; `"jml-only"` suppresses capabilities that duplicate a co-present Java language server (e.g. JDT, Red Hat Java). See note below. |
| `client` | string | `"generic"` | Known-client hint for default tuning. Values: `"generic"` (no assumptions), `"eclipse-jdt"`, `"vscode-java"`, `"intellij"`. When set to a known Java-capable client, `javaMode` defaults to `"jml-only"` unless explicitly overridden. |
| `projects` | array | none | Per-project configuration objects; see [Multi-Project Support](#multi-project-support) below. |

`null` or absent fields leave the current value unchanged.

### Multi-Project Support

The server supports multiple independent projects within a single workspace.  Each
project is a separate compilation domain with its own source folders, classpath, specs
path, and properties file.  A file belongs to the project whose `rootPaths` contains
its path as a prefix.

Per-project settings are conveyed in a **`projects`** array inside the top-level
`OpenJMLSettings` object (either in `initializationOptions` or `workspace/didChangeConfiguration`).
Each element is a `ProjectConfig` object:

| Field | Type | Description |
|---|---|---|
| `id` | string | Unique project identifier (no path separators). Used as the lookup key in command arguments. The Eclipse plugin uses the Eclipse project name (`IProject.getName()`). |
| `rootPaths` | list | This project's own source folder paths (not including dependency sources). Used to map a file URI to its owning project. |
| `sourcePath` | string | Path-separator-separated list of source roots, including own source folders **and** transitive dependency source folders. Passed as `-sourcepath`. |
| `classPath` | string | Path-separator-separated list of compiled dependency output directories and any additional user classpath entries. Passed as `-classpath`. |
| `specsPath` | string | OpenJML specs path for this project (`--specs-path`). If absent, the global `specsPath` is used. |
| `propertiesFile` | string | Path to a user-supplied OpenJML `.properties` file. May be null. |
| `generatedPropertiesFile` | string | Path to a `.properties` file generated from the IDE preferences page. May be null. |
| `outputDir` | string | Directory for RAC-compiled `.class` files (`-d`). Defaults to the IDE project's build output folder. |

Example:

```json
{
  "settings": {
    "openjml": {
      "projects": [
        {
          "id": "MyLibrary",
          "rootPaths": ["/workspace/MyLibrary/src"],
          "sourcePath": "/workspace/MyLibrary/src",
          "classPath": "/workspace/deps/commons.jar",
          "specsPath": "/path/to/Specs/specs",
          "outputDir": "/workspace/MyLibrary/bin"
        },
        {
          "id": "MyApp",
          "rootPaths": ["/workspace/MyApp/src"],
          "sourcePath": "/workspace/MyApp/src:/workspace/MyLibrary/src",
          "classPath": "/workspace/MyLibrary/bin:/workspace/deps/commons.jar",
          "specsPath": "/path/to/Specs/specs",
          "outputDir": "/workspace/MyApp/bin"
        }
      ]
    }
  }
}
```

When a project list is configured:
- The server maps each incoming file URI to the project whose `rootPaths` contains
  the file's path.  If no project matches, global settings are used.
- File-watcher events are scoped to the union of all projects' `rootPaths`.
- Commands that name a `projectId` are dispatched using that project's settings.

A single-project client (e.g. VS Code) does not need to use `projects` at all —
the global `sourcePath`, `classPath`, etc. settings are used for all files.

### Notes on Settings

**Note on `javaMode` and `client`:** OpenJML's LSP server implements capabilities that
overlap with those of full Java language servers (JDT, Red Hat Java, etc.).  By default
all capabilities are active (`javaMode: "full"`).  If another Java LS is active for the
same workspace, clients can avoid duplicate hints, signature help, etc. by setting
`javaMode: "jml-only"` or by naming the client (`client: "eclipse-jdt"`).

Integrators building a plugin that co-exists with a known Java LS should set `client`
in `initializationOptions` — the server then applies the appropriate defaults
automatically.  For example, the OpenJMLUI Eclipse plugin sets `client: "eclipse-jdt"`
so that Java-overlapping features are suppressed by default, with no configuration
required from the end user.

**Note on effective `-sourcepath`:** The server does not pass `sourcePath` directly
to OpenJML. It constructs an effective sourcepath by joining (in order, omitting
empty parts): a temp directory holding any in-memory file content; the workspace
folder roots reported at `initialize` time (only when `sourcePath` is absent, to
avoid duplicate-class issues); the user-supplied `sourcePath` (when present, this
is used alone — workspace folders are excluded); and `classPath` as a final fallback
when `sourcePath` is absent. `--specs-path` and `-classpath` are passed through
unchanged.

**Note on `escTriggerOn: "edit"`:** The server implements this mode (ESC is debounced
and re-run on every keystroke), but it is expensive and no known client UI exposes it
as an option. Client integrators may choose to omit it from their settings UI.

When `specsPath` or `solversPath` is null or empty, the server falls back to the
`OPENJML_SPECS` and `OPENJML_SOLVERS` environment variables set by the launcher.
In addition, if they are not set, OpenJML sets them based on the value of `OPENJML_INSTALL`;
consequently, for any configuration using an installation of OpenJML and intending to use
the installed content for specifications and solvers, these variables should be left unset.


---

## Document Synchronization

Sync kind is **Incremental** (`TextDocumentSyncKind.Incremental`) by default.
Each `textDocument/didChange` notification carries a list of ranged edits; the
server applies them in the order given (each range refers to the document state
after all preceding changes in the same event) and reconstructs the full text
before passing it to OpenJML.  Set `incrementalSync: false` in
`initializationOptions` to revert to **Full** sync, where every notification
must contain the complete document text in `contentChanges[0].text`.

### `textDocument/didOpen`

- Stores the document content.
- Runs `--check` immediately (no debounce).
- Does **not** run `--esc` or `--rac` automatically on open.

### `textDocument/didChange`

- Stores the updated content.
- **Marks the file dirty** (adds the URI to an internal dirty-URI set). While a file is
  marked dirty, multi-file check or ESC invocations (e.g. `openjml.checkJML` or
  `openjml.runEsc` on a directory) use the in-memory content for this file instead of
  reading it from disk. This ensures that unsaved edits are included in context-aware
  cross-file checks even before the file is saved.
- If `checkTriggerOn` is `"edit"`: schedules `--check` with a 500 ms debounce.
  A new change before 500 ms resets the timer.
- If `checkTriggerOn` is `"save"`: no `--check` is triggered by change (i.e., an edit).
- If `escTriggerOn` is `"edit"`: schedules `--esc` with a 2000 ms debounce.
  A new change before 2000 ms resets the timer.
- `--esc` on change is expensive and not recommended for large files.

### `textDocument/didSave`

- **Clears the dirty mark** for the URI (removes it from the dirty-URI set). After save,
  the file's in-memory content matches the disk, so subsequent multi-file checks read
  the file from disk directly and no longer need to mock it from memory.
- Cancels any pending debounced check or ESC.
- Runs `--check` immediately using the saved (in-memory) content.
- Does **not** run `--esc` automatically on save from the server side. If ESC-on-save
  behavior is desired, the client should issue an explicit `workspace/executeCommand`
  with `openjml.runEsc` after saving. (The VS Code extension does this via its own
  `onDidSaveTextDocument` handler so it can distinguish manual saves from auto-saves.)

### `textDocument/didClose`

- **Clears the dirty mark** for the URI (removes it from the dirty-URI set).
- Cancels all pending debounced and running checks for the URI.
- Clears all stored diagnostics for the URI.
- Publishes an empty `textDocument/publishDiagnostics` to clear all diagnostics (and their visible annotations) from the client.
- Removes stored content and per-method ESC status.

---

## Diagnostics

### Publication

Diagnostics are sent via `textDocument/publishDiagnostics`. Both `--check` and `--esc`
results are maintained separately per URI and merged before each publication. Neither
pass's results overwrite the other's.

The merging policy is:

- When `--esc` runs it subsumes `--check` (ESC performs all the same type and
  annotation checks), so an ESC result replaces the `--check` diagnostics entirely,
  eliminating duplication.
- When `--check` runs after a previous ESC (e.g. triggered by an edit), it replaces
  check-level diagnostics but retains ESC verification failures (postcondition
  violations, assertion failures). Those may be stale after the edit, but remain
  useful until a fresh ESC run either confirms or clears them.

ESC verification failures are identified by the `data` field of the LSP `Diagnostic`
object: the server sets `data` to `"esc-verification"` on any diagnostic produced
from a proof obligation failure.

### Diagnostic Format

Each diagnostic has the following fields (LSP `Diagnostic` type):

| Field | Value |
|---|---|
| `range.start/end` | Zero-based line and character offset of the reported location |
| `severity` | `1` (Error) or `2` (Warning) |
| `source` | `"openjml.check"` for `--check` results; `"openjml.esc"` for `--esc` results |
| `message` | Human-readable error or warning text from OpenJML |
| `code` | OpenJML diagnostic code string (e.g., `"jml.message"`) |

### OpenJML Exit Codes

These exit codes are logged to stderr and influence how the server interprets results:

| Code | Meaning |
|---|---|
| 0 | Success — no parse, type, or verification errors (warnings may still be present) |
| 1 | Syntax or type errors |
| 2 | Bad command-line arguments (indicates a server bug) |
| 3 or 4 | Catastrophic error — resource exhaustion (e.g. out of memory), significant misconfiguration, or internal bug |
| 6 | ESC verification failures (postcondition or assertion violations) |

---

## Implemented LSP Features

### Hover — `textDocument/hover`

Two cases are handled:

1. **`var` declaration** — if the cursor is on the `var` keyword or the variable name
   of a `var`-declared local, the server returns the inferred type as a plain-text
   string of the form `: TypeName` (e.g. `: int`, `: String`).  Type names are
   shortened by stripping `java.lang.`, `org.jmlspecs.lang.internal.` (JML built-in
   types appear as `\bigint`, `\real`, etc.), and the containing file's own package
   prefix.  This hover is always active regardless of `javaMode`.

2. **Method body / JML spec** — if the cursor is anywhere else inside a method, the
   server returns the JML specification lines (consecutive `//@ ...` comment lines)
   immediately preceding the method declaration, formatted as a Markdown code block.

Returns null if none of the above conditions are met (e.g. cursor is outside any
method, or the method has no JML annotations).

### Inlay Hints — `textDocument/inlayHint`

Returns `InlayHint` objects of kind `Type` for `var`-declared local variables,
showing the inferred type immediately after the variable name in the form `: TypeName`.
Type names are shortened identically to the hover case above.

**`javaMode` interaction:**
- `"full"` (default): hints are returned for all `var`-declared variables.
- `"jml-only"`: hints for plain Java `var` declarations are suppressed (a co-present
  Java LS such as JDT or Red Hat Java already provides those).  Hints for JML
  `ghost` and `model` `var` declarations are always emitted regardless of `javaMode`,
  because no other language server is aware of them.

**Client notes:**
- Standard LSP clients (VS Code, Neovim, Helix, etc.) display these as inline
  annotations natively.
- **VS Code with vscode-java**: `client: "vscode-java"` defaults `javaMode` to
  `"jml-only"`, so only JML ghost/model var hints are shown (vscode-java handles
  Java vars itself).
- **IntelliJ**: IntelliJ has its own built-in Java type inference display.  Whether
  LSP inlay hints from OpenJML are also shown depends on the LSP plugin in use;
  `client: "intellij"` defaults to `"jml-only"` as a conservative default.
- **Eclipse with OpenJMLUI**: LSP4E does not route `textDocument/inlayHint` responses
  to the JDT Java editor.  The OpenJMLUI plugin works around this via a direct call
  from a code mining provider, but `LineContentCodeMining` does not visually render
  in the JDT Java editor from external providers.  The inferred type is accessible
  instead via the hover described above.  `client: "eclipse-jdt"` defaults to
  `"jml-only"`.

### Code Lens Refresh — `workspace/codeLens/refresh` (server → client)

Sent by the server whenever per-method ESC status changes — for example when ESC
begins (status → CHECKING), completes (status → Verified / Not verified), or is
cancelled. The client should respond by re-requesting `textDocument/codeLens` for
any open documents of interest.

### Code Lens — `textDocument/codeLens`

Returns one code lens per detected method in the document. Each lens shows the current
ESC verification status for that method together with an inline action button. The label
format is:

| Status | Label |
|---|---|
| Not run | `OpenJML: — ▶ Run ESC` |
| In progress | `OpenJML: ⧗ Checking… ✕ Cancel` |
| Verified | `OpenJML: ✓ Verified ↺ Re-run` |
| Infeasible precondition | `OpenJML: Infeasible ↺ Re-run` |
| Not verified | `OpenJML: ✗ Not verified (N issue(s)) ↺ Re-run` |
| Skipped | `OpenJML: Skipped ▶ Run ESC` |
| Solver timeout | `OpenJML: Timeout ↺ Re-run` |
| Cancelled | `OpenJML: Cancelled ▶ Run ESC` |
| Type/check error | `OpenJML: Check error ↺ Re-run` |
| Check error in deps | `OpenJML: Check error in other files ↺ Re-run` |

Each code lens embeds the command `openjml.runEscForMethod` with arguments
`[uri, "name@startLine"]`, where `name` is the simple method name and `startLine` is
the 0-based line number of the method declaration. This two-element format is the
**code-lens format** and is detected by the server as distinct from the old VS Code
4-prefix format and the Eclipse project-ID format. A client that supports code lens
execution can invoke (or cancel) ESC on a single method by sending
`workspace/executeCommand` with that command and those arguments.

The command is always `openjml.runEscForMethod` regardless of the current status; when
the method is already CHECKING the server aborts the in-flight proof (via
`openjml.abortCurrentProof` semantics) instead of starting a new one, so a single
command handles both Run and Cancel without VS Code treating a command change as a new
lens and showing duplicates.  Aborting the current proof does not stop a whole-file or
project ESC run from continuing to the next method.

The server sends a `workspace/codeLens/refresh` notification whenever method ESC status
changes (including when a check moves from CHECKING to a final state). A client should
re-query `textDocument/codeLens` on receiving this notification.

### Completion — `textDocument/completion`

Provides JML keyword and backslash-token completions inside JML annotations
(`//@ ...` and `/*@ ... */`). Trigger characters are `\` and `@`.

Two categories of items are offered:

- **JML keywords** — clause and modifier names (`requires`, `ensures`, `ghost`,
  `invariant`, etc.) — offered when the cursor is inside a JML annotation and the
  partial word does not start with `\`.
- **Backslash tokens** — built-in JML expressions (`\result`, `\old`, `\forall`,
  `\nothing`, etc.) — offered when the partial word starts with `\`.

Completions are only offered when the cursor is inside a JML annotation context;
positions in regular Java code return an empty list.

### Document Symbols — `textDocument/documentSymbol`

Returns a hierarchical symbol tree for the document. When `useIntegratedOutline` is
`true` (the default), all Java and JML symbols are returned together — classes,
methods, fields, and JML ghost/model declarations — giving an integrated view.
When `false`, only JML-specific symbols are returned, intended to complement a
competing Java outline provider.

The handler waits for any in-flight `--check` to complete before returning, so the
outline reflects the current source rather than a stale AST. For `.jml` spec files,
symbols are looked up under the companion `.java` URI.

### Folding Ranges — `textDocument/foldingRange`

Returns folding ranges for JML annotation blocks (consecutive `//@ ...` or `/*@ ... */`
comment sequences that span multiple lines) and Java text blocks (`""" ... """`).
The implementation is a pure character scan — no AST is required — so folding is
available immediately, even before the first `--check` run.  Java structural folds
(class bodies, method bodies, imports) are provided by the client's own Java language
support, not by this server.

If the document has not yet been opened (content not in memory), the server reads it
from disk.

**Eclipse plugin note:** The OpenJMLUI Eclipse plugin does not use this LSP request for
its folding support.  LSP4E's folding reconciling strategy requires projection (fold
annotation) support to be enabled on the editor before the reconciler is installed, and
there is no suitable extension point to guarantee that ordering for either the JDT Java
editor or the Generic Editor.  Instead, the plugin installs `JmlFoldingManager` directly
on each editor's `ProjectionViewer` via a part listener, running the same character-scan
algorithm locally without a server round-trip.  For `.java` files, `JmlFoldingManager`
folds (JML annotation blocks) coexist with JDT's built-in structural folds (methods,
imports, Javadoc) in the same `ProjectionAnnotationModel` without interfering.  For
`.jml` files opened in the Generic Editor, `JmlFoldingManager` provides all folding.
Other clients that do not have this constraint can use `textDocument/foldingRange`
normally.

**Implications for generic clients:** None. Generic clients use `textDocument/foldingRange`
through the standard LSP protocol. The Eclipse plugin's local algorithm is a workaround
for LSP4E's projection-ordering constraint and does not represent a UX difference from
what generic clients receive via the server.

### Semantic Tokens — `textDocument/semanticTokens/full`

Returns full-file semantic token data for JML keyword and clause highlighting.
The server's token legend (returned in `ServerCapabilities.semanticTokensProvider.legend`) is:

| Index | Token type | Used for |
|---|---|---|
| 0 | `keyword` | JML clause and modifier keywords (`requires`, `ensures`, `invariant`, `ghost`, etc.) |
| 1 | `macro` | JML backslash expressions (`\result`, `\old`, `\forall`, `\nothing`, etc.) |
| 2 | `variable` | JML identifiers that resolve to variables or fields in the AST (AST strategy only) |

No token modifiers are used; the modifiers list in the legend is empty.

Clients map these type names to editor colors. The names (`keyword`, `macro`, `variable`)
are drawn from the LSP standard token type vocabulary, so most clients will have
default colors for them — though what those colors look like varies by theme and client.
A client that needs specific JML-aware colors should configure its theme to handle these
three type names explicitly.

The current set of three token types is minimal. Planned additions (all drawn from
the LSP standard token type vocabulary, so clients will have fallback colors without
custom configuration):

| Token type | Intended use |
|---|---|
| `type` | JML primitive types: `\bigint`, `\real`, `TYPE` |
| `modifier` | JML method/class modifiers: `pure`, `spec_public`, `helper`, `non_null`, `nullable` |
| `property` | Ghost and model field declarations |
| `number` | Numeric literals inside JML expressions |
| `operator` | JML-specific operators: `==>`, `<==`, `<==>`, `<:` |
| `comment` | The `//@ ` and `/*@ */` annotation delimiters themselves |

The server also currently uses no token modifiers (`modifiers: []`). The LSP standard
modifier vocabulary includes `declaration` and `definition`, which can be combined with
any token type to distinguish a symbol's declaration site from its use sites. For
example, a ghost variable declaration could be tagged `variable` + `declaration`
modifier, while references carry only `variable`. Most clients render declaration sites
distinctly (bold, underline) when modifiers are present. Adding these modifiers is
planned alongside the token type expansion.

Two strategies are available via the `syntaxColoringStrategy` setting:

- `"ast"` (default) — AST-based coloring when a `--check` result is cached (no
  false positives for identifiers that share a JML keyword name); falls back to
  regex before the first check.
- `"regex"` — always uses regex-based coloring (instant, but may color non-JML
  identifiers that happen to match JML keywords).

Non-VS Code clients should use this standard request. See
[`openjml.getSemanticTokens`](#openjmlgetsemantictokens) for the VS Code-specific
alternative.

**Implications for generic clients:** None for the standard semantic token request.
Generic clients receive JML semantic tokens via `textDocument/semanticTokens/full`
through the normal LSP negotiation path. The Eclipse plugin's `JmlColorizer` is a
workaround for JDT's presentation layer intercepting LSP4E's token delivery for `.java`
files, and for LSP4E's semantic token reconciler not re-firing after `publishDiagnostics`.
A generic client with proper semantic token support gets the equivalent result through
the standard path. One potential improvement: the server could send
`workspace/semanticTokens/refresh` after each `--check` completes, signaling
well-behaved clients to re-request tokens without needing a client-side workaround.
This is not yet implemented.

### Go to Definition — `textDocument/definition`

Resolves the declaration of the identifier under the cursor. Works for identifiers
in both regular Java code and JML clauses (`//@ requires`, `//@ ensures`, etc.).
Requires a cached AST from a prior `--check` run for the document.

### Go to Declaration — `textDocument/declaration`

For Java and JML identifiers, declaration and definition are the same location.
Delegates to the same logic as `textDocument/definition`.

### Find References — `textDocument/references`

Finds all references to the symbol under the cursor across every AST currently in
the cache (i.e., all files that have been opened and checked in the current session).
Symbol identity is used for matching, which is correct within a single OpenJML
compilation context.

Note: the search is limited to files whose ASTs are cached. Files that have not been
opened or checked since the server started are not searched.

### Rename — `textDocument/rename` / `textDocument/prepareRename`

`prepareRename` validates that the cursor is on a renameable symbol (a valid Java
identifier character) and signals that rename is supported. It returns
`defaultBehavior: true` so the client infers the rename range from the identifier
word boundary.

`rename` validates the new name, finds all references across cached ASTs, applies
the edits in memory, then validates the result by running `--check` on the modified
content and comparing the before and after diagnostic sets. The comparison is non-trivial: it
must account for cases where the new name shadows — or no longer shadows — another
identifier, silently changing the meaning of existing references without necessarily
producing new errors. If the rename is judged unsafe, or the new name is syntactically
invalid, a descriptive error is returned rather than applying the edits.

### Signature Help — `textDocument/signatureHelp`

Triggered when the cursor is inside a method call argument list. The server scans
backward from the cursor position to find the enclosing `(` and counts commas to
determine the active parameter index. It then looks up the matching method declaration
in the cached AST and returns a `SignatureHelp` response containing one
`SignatureInformation` entry with labelled `ParameterInformation` items.

Trigger characters: `(` and `,`.

If the source file has not yet been type-checked (no AST cached), an empty
`SignatureHelp` is returned gracefully. Only the first matching overload is returned;
overload resolution across multiple signatures is not yet supported.

**Method lookup scope and known limitations**

The server searches for method declarations only within the current file's
`JmlCompilationUnit` and its sibling `.jml` specs file (if any). This covers:

- Regular Java methods declared in the same source file.
- JML model methods (`//@ model public int foo(int x);`) declared in the same
  file or in the companion `.jml` file.
- Accessor methods synthesised for JML model fields
  (`//@ model public int size;`), stored in `typeSpecs.modelFieldMethods`.

**Cross-class calls are not supported.** When the receiver of a call is an
object of another class (e.g. `list.isEmpty(`, `Collections.max(`), the server
cannot resolve the receiver type and returns an empty result. Full cross-class
support would require resolving the receiver expression using OpenJML's
`Resolve`/`Symtab` infrastructure. Eclipse's own JDT parameter hints
(`Ctrl+Shift+Space`) handle cross-class calls for Java code.

**Auto-trigger in `.java` file JML regions.** Eclipse's Java editor suppresses
LSP4E's automatic `(` / `,` trigger inside comment partitions
(`__java_singleline_comment`, `__java_multiline_comment`). As a result,
signature help does not pop up automatically when typing `(` inside a
`//@ assert` or similar JML statement in a `.java` file. Use the
`Ctrl+Shift+J H` ("JML Parameter Hints") key binding to invoke it manually.
Standalone `.jml` files are opened in the Generic Editor where the automatic
trigger works normally.

**Implications for generic clients:** Generic clients are better here. Standard
LSP clients honor `(` and `,` as trigger characters in all editing contexts,
including inside comment-like regions. JDT's comment partition suppression is an
Eclipse-specific limitation. No server-side change is needed; generic clients
receive full automatic signature help trigger behavior without any workaround.

### Workspace Symbols — `workspace/symbol`

Returns declarations from the AST cache whose simple name contains the query string
(case-insensitive substring match). An empty query returns all indexed declarations.
Searches only files present in the current AST cache.

**Project-filtered query encoding:** To restrict results to a single project without
using a custom command, the Eclipse plugin encodes the project root into the query
string as `"<projectRoot>\n<identifier>"` (project path, a newline character, then the
actual search term). The server detects the newline and passes only the matching
project's nav section to the search. Generic clients that do not need per-project
filtering should pass a plain query string. For programmatic project-scoped lookups,
`openjml.symbolsForProject` is cleaner and does not require this encoding.

### Configuration — `workspace/didChangeConfiguration`

Handled as described in the [Configuration](#configuration) section.

### `workspace/didChangeWatchedFiles`

The server registers two file watchers during `initialized()` via
`client/registerCapability`:

| Glob | Events watched |
|------|---------------|
| `**/*.jml` | Created, Changed, Deleted |
| `**/*.java` | Created, Deleted |

**`.jml` events** — the server reads the updated spec file from disk and
re-checks the companion `.java` file.  On Deleted, diagnostics for the
companion `.java` are cleared.  Events for files that are currently open in
the editor are ignored (the editor's `textDocument/did*` path handles them).

**`.java` events** — Created: the file is indexed into the workspace symbol
table.  Deleted: the AST cache entry and diagnostics for the file are
cleared.  Changed-while-not-open: ignored (the user opens the file to
trigger a re-check).

**Root filtering** — when per-project settings are configured (via the `projects`
array), events are scoped to the union of all projects' `rootPaths`.  Events for
files outside those roots (e.g. files in non-JML projects in a multi-project Eclipse
workspace) are silently dropped.  When no per-project settings are configured the
filter falls back to `workspaceFolderPaths`; if that is also absent, all events are
processed.


---

## Custom Commands — `workspace/executeCommand`

Commands are dispatched via `workspace/executeCommand`.  Two argument formats are
supported; the server auto-detects which is in use:

### Argument formats

**Project-ID format** (used by the Eclipse plugin when per-project settings are
configured):
```
args[0]  projectId   -- short project name (no path separators); selects per-project settings
args[1+]             -- command-specific paths / URIs
```

**Legacy format** (used by VS Code and generic clients):
```
args[0]  sourcePath      -- paths for -sourcepath (empty = use server default)
args[1]  classPath       -- paths for -classpath  (empty = use server default)
args[2]  specsPath       -- path to OpenJML specs dir (empty = use server default)
args[3]  propertiesFile  -- path to a generated .properties file (empty = none)
args[4+]                 -- command-specific paths / URIs
```

**Format detection:** if `args[0]` contains no path-separator characters (`/`, `\`,
`:`) and matches a project id registered via the `projects` settings array, the
project-ID format is used.  Otherwise the legacy format is assumed.

In the legacy format, non-empty values in `args[0..3]` override the corresponding
server settings for that invocation only.

### `openjml.checkJML`

Run `--check` on one or more files or directories.

```
command:   "openjml.checkJML"
arguments (project-ID): ["<projectId>", "<path1>", "<path2>", ...]
arguments (legacy):     ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
                         "<path1>", "<path2>", ...]
```

`path1..N` are file-system paths (files or directories). All `.java` files under a
directory are checked recursively.

### `openjml.runEsc`

Run `--esc` on one or more files or directories.

```
command:   "openjml.runEsc"
arguments (project-ID): ["<projectId>", "<path1>", "<path2>", ...]
arguments (legacy):     ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
                         "<path1>", "<path2>", ...]
```

Cancels any currently running ESC for the same URIs. Marks all methods as CHECKING
immediately. As each method's proof finishes, its code lens is updated in real time
(via `IProofResultListener`) so the user sees individual methods flip from
⧗ Checking… to their final state rather than all updating at once. Accumulated
diagnostics are also published progressively per file. A final pass after the run
reconciles any remaining state.

A path that starts with `file://` is treated as a document URI and checked against
in-memory content rather than the on-disk file.

### `openjml.runEscForMethod`

Run `--esc` on a single named method. Marks only the target method as CHECKING;
other methods' statuses are left unchanged. On completion, only that method's
diagnostics and code lens are updated; other methods are unaffected.

```
command:   "openjml.runEscForMethod"
arguments (code-lens):  ["<file-uri>", "<name@startLine>"]
arguments (project-ID): ["<projectId>", "<file-uri>", "<name@startLine>"]
arguments (legacy):     ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
                         "<file-uri>", "<fully-qualified-method-name>"]
```

**Code-lens format** (the preferred format for new clients): exactly two elements where
the first starts with `file://`. `name@startLine` is the simple method name followed by
`@` and the 0-based start line of the method declaration (e.g. `add@5`). This allows
overloaded methods on different lines to be distinguished. This is the format emitted by
`textDocument/codeLens` responses.

**Project-ID format**: three elements where `args[0]` is a bare project ID (no `/`, `\`,
or `:`) and `args[2]` is the `name@startLine` method reference.

**Legacy format**: six elements in the old VS Code 4-prefix layout. The method reference
is a fully-qualified name (`package.ClassName.methodName`); if the simple name uniquely
identifies a method the package/class prefix may be omitted. An empty method name causes
the whole file to be checked.

### `openjml.runEscSplitByFile`

Run `--esc` on a set of files, launching a separate ESC invocation per file (in
parallel). Each file's result is published as it completes, rather than waiting for
all files to finish.

```
command:   "openjml.runEscSplitByFile"
arguments (project-ID): ["<projectId>", "<path1>", "<path2>", ...]
arguments (legacy):     ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
                         "<path1>", "<path2>", ...]
```

### `openjml.runEscSplitByMethod`

Run `--esc` on a set of files, launching a separate ESC invocation per method (in
parallel). Per-method code lens updates arrive in real time as each proof completes.

```
command:   "openjml.runEscSplitByMethod"
arguments (project-ID): ["<projectId>", "<path1>", "<path2>", ...]
arguments (legacy):     ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
                         "<path1>", "<path2>", ...]
```

### `openjml.runRac`

Compile one or more files or directories with JML assertions as runtime checks.

```
command:   "openjml.runRac"
arguments (project-ID): ["<projectId>", "<path1>", "<path2>", ...]
arguments (legacy):     ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
                         "<outputDir>", "<path1>", "<path2>", ...]
```

`outputDir` (legacy format only) is the directory for compiled class files. In the
project-ID format the `outputDir` from the project's `ProjectConfig` is used.

### `openjml.saveAndRunEsc` (VS Code extension UI command — not a server command)

This is a VS Code extension-level command registered in `package.json` and bound to
menu items and keyboard shortcuts. When the user triggers it, the VS Code extension
saves the document (equivalent to `textDocument/didSave`) and then sends
`workspace/executeCommand` with `openjml.runEsc` to the server. The string
`openjml.saveAndRunEsc` is **never sent to the server**; it is handled entirely
client-side by the VS Code extension. Other clients (Eclipse, generic LSP clients)
should implement the same pattern: save first, then call `openjml.runEsc`.

### `openjml.cancelEsc`

Cancel one or more in-progress ESC runs.  **Stops all remaining proofs** in the
targeted run — no further methods are attempted after cancellation.

```
command:   "openjml.cancelEsc"
arguments: ["<target>"]
```

`target` controls what is cancelled:

| Value | Effect |
|-------|--------|
| `null` / absent / `""` | Cancel all ESC runs |
| A plain file URI (e.g. `file:///…/Foo.java`) | Cancel the whole-file ESC for that URI |
| `"<uri>#<methodName>"` | Cancel the per-method ESC for the named method |

Cancelled methods have their code lens status set to `Cancelled`; other methods are
unaffected.

Use `openjml.abortCurrentProof` instead when the intent is to skip only the
currently-running proof and continue proving the remaining methods.

### `openjml.abortCurrentProof`

Abort only the currently-running method proof, then allow the ESC loop to continue
with the next method.  The in-progress SMT solver invocation is killed immediately
and the method is reported `Cancelled`, but no further proofs are prevented.

```
command:   "openjml.abortCurrentProof"
arguments: ["<target>"]
```

`target` uses the same format as `openjml.cancelEsc`.  If the target identifies a
whole-file or project run, only the single method currently being proved is aborted;
the remaining methods in the queue are unaffected.

| Situation | `openjml.cancelEsc` | `openjml.abortCurrentProof` |
|-----------|--------------------|-----------------------------|
| Current method | CANCELLED | CANCELLED |
| Remaining methods | not attempted | continue normally |
| Overall run exit code | CANCELLED (5) | determined by remaining proofs |

The code lens "✕ Cancel" action uses `openjml.abortCurrentProof` semantics so
that cancelling one method in a whole-file run does not discard all pending proofs.

### `openjml.getRunningEscTasks`

Returns the list of currently running ESC task keys as a JSON array of strings.
Each entry is either a plain file URI (whole-file ESC) or a `"<uri>#<methodName>@<startLine>"`
string (per-method ESC). Returns an empty array when no ESC is in progress.

```
command:   "openjml.getRunningEscTasks"
arguments: []
```

Clients can use this to populate a cancellation UI (e.g. a checklist dialog or
Quick Pick) before calling `openjml.cancelEsc` or `openjml.abortCurrentProof`.

### `openjml.indexProject`

Trigger a `--check` pass on all source directories of the specified project,
rebuilding the declaration index used by `workspace/symbol` ("Find All Declarations").
Does **not** clear existing diagnostics or the AST cache — use `openjml.clearAndReindex`
for a full reset.

```
command:   "openjml.indexProject"
arguments: ["<projectId>"]
```

When `projectId` matches a project registered via the `projects` settings array, only
that project's `rootPaths` are indexed.  An absent or empty `projectId` indexes all
configured projects.

**Eclipse plugin:** exposed as the "Index Project" item in the OpenJML main menu,
editor popup, and Package Explorer context menu.  Intended for use before "Find All
Declarations" to ensure files that have not yet been opened are covered by the index.

### `openjml.symbolsForProject`

Return `workspace/symbol`-style declarations filtered to a single project. This is the
server-side alternative to the `workspace/symbol` project-encoded query; it avoids the
cross-project leakage that can occur when multiple projects share a single nav section.

```
command:   "openjml.symbolsForProject"
arguments: ["<query>", "<projectRoot>"]
```

| Argument | Description |
|---|---|
| `query` | Symbol name to search (case-sensitive exact match; empty = return all). |
| `projectRoot` | File-system path of the project root (e.g. `/home/user/myproject`). When absent or empty, symbols from all projects are returned. |

Returns a JSON array of `SymbolInformation` objects (same format as `workspace/symbol`).

**Note on case sensitivity:** unlike the plain `workspace/symbol` handler (case-insensitive
substring match), this command uses an exact case-sensitive match on the symbol name. Pass
an empty query to retrieve all symbols for the project.

**Eclipse plugin:** replaces the earlier `workspace/symbol`-with-encoded-query approach;
the handler calls this command and presents results in the "Find All Declarations" dialog.

### `openjml.focusFile`

Notify the server that the user has switched focus to an already-open file. Triggers
a `--check` recheck so that stale diagnostics from fixed dependencies are cleared.

```
command:   "openjml.focusFile"
arguments: ["<file-uri>"]
```

**Implications for generic clients:** This is a real UX gap for clients that do not
implement it. Without `openjml.focusFile`, a client that edits file A, switches to
file B, then returns to file A will see stale diagnostics on A until the next edit or
save triggers a new `--check`. The Eclipse plugin sends the focus command on every
editor tab switch (200 ms debounced) to keep diagnostics current proactively.

Client authors should implement the equivalent:
- **VS Code:** already implemented via `onDidChangeActiveTextEditor` with a 200 ms
  debounce (see the VS Code extension source).
- **IntelliJ / other IDEs:** hook the "file editor gained focus" event and send
  `openjml.focusFile` with the same debounce.
- **Bare LSP clients** that do not implement this get degraded-but-functional behavior:
  diagnostics are correct after the next edit or save, just not updated proactively
  on focus change.

### `openjml.getSemanticTokens`

VS Code-specific workaround. Returns JML semantic token data directly as the command
result rather than via `textDocument/semanticTokens/full`. The VS Code extension uses
this because it registers its own `DocumentSemanticTokensProvider` directly (to avoid
being overwritten by the Red Hat Java extension), bypassing the standard LSP
negotiation.

**Non-VS Code clients should use `textDocument/semanticTokens/full` instead.** The
server advertises `semanticTokensProvider` in `ServerCapabilities` and handles the
standard request; both paths call the same underlying token computation. The Eclipse
plugin uses the standard protocol via LSP4E's `SemanticTokensClient`.

```
command:   "openjml.getSemanticTokens"
arguments: ["<file-uri>"]
```

### `openjml.clearAndReindex`

Clear all server-side caches (AST cache, diagnostics, ESC status) and restart as if
the server had just connected — re-checking all open files and re-indexing the
workspace. Takes no arguments.

### `openjml.clearMarkers`

Clears all OpenJML diagnostics without scheduling any new checks. The server clears
its internal diagnostic state and sends `textDocument/publishDiagnostics` with an
empty list for every URI that currently has diagnostics; the client's normal handling
of those notifications removes the visible annotations. A client that already knows
its display is stale (e.g. after a workspace rebuild) may also clear its own
annotations independently, before or without waiting for the server's response —
both approaches are valid and complementary. Takes no arguments.

---

## Not Yet Implemented

The following LSP features are not currently supported. Clients should not rely on
them being available.

| Feature | Notes |
|---|---|
| `textDocument/codeAction` | Quick fixes — code lens is used for ESC invocation instead |
| `textDocument/formatting` | Code formatting; must be JML-comment-aware to avoid corrupting `//@ ` lines |
| `textDocument/rangeFormatting` | Range-based formatting |
| `textDocument/documentHighlight` | Highlight all occurrences of a symbol in the current file |
| `window/progress` / `$/progress` | Progress reporting for long-running check and ESC operations |
| `textDocument/implementation` | Go to implementation (out of scope for JML-focused server) |
| `textDocument/typeDefinition` | Go to type definition (out of scope) |

---

## Threading and Concurrency

The server uses a single-threaded LSP dispatch thread (managed by LSP4J) and a
cached thread pool for check and ESC tasks. Debouncing uses a single-threaded
scheduled executor.

Within a single file, starting a new ESC cancels the previous one via
`Future.cancel(true)`. A generation counter ensures that results from a superseded
ESC run are silently discarded if they arrive after a newer run has already started.

ESC runs for different files may overlap concurrently.

The `--check` runner never updates method ESC status or requests a code lens refresh,
so in-progress edits do not disturb the ESC status badges visible to the user.

---

## Error Handling and Logging

All diagnostic output goes to the log file described above
(`~/.openjml/logs/openjml-lsp-<pid>.log` in production, `/tmp/openjml-lsp-debug.log` in dev).
The JSON-RPC stream on stdout is protected by two complementary redirections:

1. The launcher script redirects the process's stderr to the log file
   (`exec 2>>"$LOG"`) before starting Java.
2. `ServerLauncher.main()` captures the real stdout as the LSP wire stream, then calls
   `System.setOut(System.err)` so that any subsequent `System.out.println` calls —
   from OpenJML, from javac, or from the server itself — are routed to stderr and
   therefore to the log file, never to the JSON-RPC channel.

OpenJML's compiler text output is additionally captured via the `PrintWriter` argument
to `IAPI.make()` (a `StringWriter` in the server) and discarded, so it does not appear
even in the log under normal operation. Only debug-level output (`System.err` calls in
the server) and verbose OpenJML output (when verbose mode is active) appear in the log.

If OpenJML exits with code 3 or 4 (catastrophic error), the server marks all methods
as `Check error` and publishes whatever diagnostics were collected before the failure.

If OpenJML exits with code 2 (bad command-line arguments), a message is written to
the debug log; this always indicates a bug in the server.

---

## VS Code Extension Notes

The bundled VS Code extension (`OpenJMLlsp/vscode-extension/`) has several design decisions that differ from a generic LSP client. This section documents them for extension maintainers and third-party client authors.

### Client identifier and `javaMode` default

The extension passes `client: "vscode-java"` in `initializationOptions`. This causes the server to default `javaMode` to `"jml-only"`, which suppresses features that overlap with the Red Hat Java extension (`documentSymbol` Java members, Java hover, Java inlay hints). The `openjml.javaMode` and `openjml.client` settings in `package.json` let users override these if they want full coverage (e.g., when Red Hat Java is not installed).

### Semantic tokens — additive merge with Red Hat Java

The vscode-languageclient library's built-in semantic tokens feature competes with the Red Hat Java extension's semantic tokens provider via a provider race that VS Code resolves non-deterministically. To avoid this:

1. The LSP-channel semantic tokens response is suppressed in middleware:
   ```js
   provideDocumentSemanticTokens: (_document, _token, _next) =>
       new vscode.SemanticTokens(new Uint32Array([]))
   ```
2. A separate `DocumentSemanticTokensProvider` is registered directly with VS Code via `vscode.languages.registerDocumentSemanticTokensProvider`. It fetches tokens by calling the `openjml.getSemanticTokens` custom command and returns them as a `vscode.SemanticTokens` object.

This approach merges the JML tokens additively on top of whatever Red Hat produces. The legend must include all three server token types in order: `['keyword', 'macro', 'variable']`.

### `prepareRename` middleware

The extension overrides `prepareRename` in middleware to return the word range at the cursor immediately for Java identifiers, bypassing the server round-trip. This is required because the Red Hat extension's rename provider would otherwise race with ours and win. For non-identifier positions the call falls through to the server.

### `java.format.enabled` caveat

The Red Hat Java formatter rewrites `//@ ` to `// @` (inserts a space after `//`), silently disabling all JML annotations. The extension warns once per workspace on activation and offers to disable `java.format.enabled`. Users who need formatting can still invoke it manually via Shift+Alt+F; they should configure a formatter profile that excludes line-comment reformatting.

### Type-checking triggers

`--check` (JML type-check) is triggered automatically:
- On `textDocument/didOpen` — unconditionally
- On `textDocument/didChange` — debounced (250 ms) when `checkTriggerOn == "edit"`
- On `textDocument/didSave` — unconditionally
- On tab focus (`openjml.focusFile`) — debounced (200 ms) when returning to an already-open file

There is no manual "run check" command; checking is always automatic. ESC (`--esc`) is separate and has its own trigger setting (`openjml.escTriggerOn`).

---

## Known Limitations

- **Single-file scope**: Each check or ESC invocation processes one file at a time.
  Cross-file type information (e.g., specs for imported classes) is available if
  `sourcePath` is configured, but the server does not automatically re-check
  dependent files when a spec file changes.

- **ESC-on-save**: The server does not trigger ESC from `textDocument/didSave`.
  Clients that want ESC-on-save must issue `openjml.runEsc` themselves after save.

- **Method detection is approximate**: Code lens placement and hover use a
  regex-based source scanner, not a full parser. Constructor names, lambda bodies,
  anonymous class methods, and certain generics may not be detected correctly.

- **Workspace folders**: The server accepts workspace folder roots (from
  `workspaceFolders` in `initialize` and the `workspaceFolderPaths` setting) and
  uses them as a fallback `-sourcepath` when no explicit source path is configured.
  However, per-folder configuration, cross-folder dependency tracking, and
  `workspace/didChangeWorkspaceFolders` are not implemented.

