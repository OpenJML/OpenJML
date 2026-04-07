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

Stderr from the server and openjml is redirected to `/tmp/openjml-lsp-debug.log` by the launcher script, so Java
stack traces and internal debug messages go there, not to the client.

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
   startup. The JSON object is deserialized directly as `OpenJMLSettings`.

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

### Settings Reference

| Field | Type | Default | Description |
|---|---|---|---|
| `specsPath` | string | env `OPENJML_SPECS` | Path to JML specification files, passed as `--specs-path` |
| `solversPath` | string | env `OPENJML_SOLVERS` | Path to SMT solver binaries, passed as `--solvers-path` |
| `sourcePath` | string | none | User source root(s) for cross-file references (see note on effective sourcepath below) |
| `classPath` | string | none | Classpath for pre-compiled dependencies, passed as `-classpath` directly; also used as a sourcepath fallback (see note) |
| `checkTriggerOn` | string | `"edit"` | When to run `--check`: `"edit"` or `"save"` |
| `escTriggerOn` | string | `"manual"` | When to run `--esc`: `"manual"`, `"save"`, or `"edit"` (see note) |
| `incrementalSync` | boolean | `true` | When `true`, advertise `Incremental` sync and apply ranged edits internally; when `false`, revert to `Full` sync |
| `javaMode` | string | `"full"` | Java-capability mode: `"full"` enables all Java+JML capabilities; `"jml-only"` suppresses capabilities that duplicate a co-present Java language server (e.g. JDT, Red Hat Java). See note below. |
| `client` | string | `"generic"` | Known-client hint for default tuning. Values: `"generic"` (no assumptions), `"eclipse-jdt"`, `"vscode-java"`, `"intellij"`. When set to a known Java-capable client, `javaMode` defaults to `"jml-only"` unless explicitly overridden. |
| `jmlWorkspaceRoots` | string | none | Path-separator-separated list of filesystem paths the server should treat as its JML workspace. The server uses these paths to scope file-watcher events and workspace indexing. If absent or blank, the server falls back to the workspace folders reported in the `initialize` request. The Eclipse plugin populates this automatically from the set of open projects that carry JML nature. |

`null` or absent fields leave the current value unchanged.

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
- If `checkTriggerOn` is `"edit"`: schedules `--check` with a 500 ms debounce.
  A new change before 500 ms resets the timer.
- If `checkTriggerOn` is `"save"`: no `--check` is triggered by change (i.e., an edit).
- If `escTriggerOn` is `"edit"`: schedules `--esc` with a 2000 ms debounce.
  A new change before 2000 ms resets the timer.
- `--esc` on change is expensive and not recommended for large files.

### `textDocument/didSave`

- Cancels any pending debounced check or ESC.
- Runs `--check` immediately from disk.
- Does **not** run `--esc` automatically on save from the server side. If ESC-on-save
  behavior is desired, the client should issue an explicit `workspace/executeCommand`
  with `openjml.runEsc` after saving. (The VS Code extension does this via its own
  `onDidSaveTextDocument` handler so it can distinguish manual saves from auto-saves.)

### `textDocument/didClose`

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
ESC verification status for that method as a display-only command label. The label
format is:

| Status | Label |
|---|---|
| Not run | `OpenJML: —` |
| In progress | `OpenJML: ⧗ Checking…` |
| Verified | `OpenJML: ✓ Verified` |
| Infeasible precondition | `OpenJML: Infeasible` |
| Not verified | `OpenJML: ✗ Not verified (N issue(s))` |
| Skipped | `OpenJML: Skipped` |
| Solver timeout | `OpenJML: Timeout` |
| Cancelled | `OpenJML: Cancelled` |
| Type/check error | `OpenJML: Check error` |

Each code lens embeds a command (`openjml.runEscForMethod` by default) with arguments
`[uri, fully-qualified-method-name]`. A client that supports code lens execution can
invoke ESC on a single method by sending `workspace/executeCommand` with that command
and those arguments.

The server sends a `client/refreshCodeLenses` notification whenever method ESC status
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

Returns folding ranges for block comments, JML annotation blocks, class bodies,
and method bodies. If the document has not yet been opened (content not in memory),
the server reads it from disk.

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

### Workspace Symbols — `workspace/symbol`

Returns declarations from all currently open (cached) files whose simple name
contains the query string (case-insensitive substring match). An empty query
returns all indexed declarations. Searches only files present in the current
AST cache.

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

**Root filtering** — if `jmlWorkspaceRoots` is configured, only events whose
file path begins with one of those roots are acted upon.  Events for files
outside the effective roots (e.g. non-JML projects in a multi-project
workspace) are silently dropped.  When `jmlWorkspaceRoots` is absent the
filter is disabled and all events are processed.

**Watcher re-registration** — when `jmlWorkspaceRoots` changes via
`workspace/didChangeConfiguration`, the server unregisters the old watchers
and re-registers them immediately so the new scope takes effect.


---

## Custom Commands — `workspace/executeCommand`

All commands share a fixed 4-element argument prefix followed by command-specific
arguments. Empty strings are used for absent optional values so that positions are
always fixed:

```
args[0]  sourcePath      -- paths for -sourcepath (empty = use server default)
args[1]  classPath       -- paths for -classpath  (empty = use server default)
args[2]  specsPath       -- path to OpenJML specs dir (empty = use server default)
args[3]  propertiesFile  -- path to a generated .properties file (empty = none)
```

When non-empty, these per-invocation values override the corresponding server
settings for that invocation only.

### `openjml.checkJML`

Run `--check` on one or more files or directories.

```
command:   "openjml.checkJML"
arguments: ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
            "<path1>", "<path2>", ...]
```

`path1..N` are file-system paths (files or directories). Use `--dirs` semantics:
all `.java` files under a directory are checked recursively.

### `openjml.runEsc`

Run `--esc` on one or more files or directories.

```
command:   "openjml.runEsc"
arguments: ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
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
arguments: ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
            "<file-uri>", "<fully-qualified-method-name>"]
```

`fully-qualified-method-name` is in the form `package.ClassName.methodName`. If the
simple name (`methodName`) uniquely identifies a method in the file, the package and
class prefix are optional. An empty method name causes the whole file to be checked.

### `openjml.runRac`

Compile one or more files or directories with JML assertions as runtime checks.

```
command:   "openjml.runRac"
arguments: ["<sourcePath>", "<classPath>", "<specsPath>", "<propertiesFile>",
            "<outputDir>", "<path1>", "<path2>", ...]
```

`outputDir` is the directory for compiled class files (empty = server default,
typically `rac-classes` in the workspace root).

### `openjml.focusFile`

Notify the server that the user has switched focus to an already-open file. Triggers
a `--check` recheck so that stale diagnostics from fixed dependencies are cleared.

```
command:   "openjml.focusFile"
arguments: ["<file-uri>"]
```

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
| `textDocument/formatting` | Code formatting |
| `textDocument/rangeFormatting` | Range-based formatting |
| `textDocument/documentHighlight` | Highlight all occurrences of a symbol |
| `textDocument/implementation` | Go to implementation |
| `textDocument/typeDefinition` | Go to type definition |

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

All diagnostic output goes to `/tmp/openjml-lsp-debug.log`. The JSON-RPC stream on
stdout is protected by two complementary redirections:

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

## Known Limitations

- **Single-file scope**: Each check or ESC invocation processes one file at a time.
  Cross-file type information (e.g., specs for imported classes) is available if
  `sourcePath` is configured, but the server does not automatically re-check
  dependent files when a spec file changes.

- **Temp file for unsaved content**: When checking content that has not yet been
  saved to disk, the server writes it to a temporary file, passes that path to
  OpenJML, then deletes it. OpenJML has an existing mechanism (used in its test
  suite) for wrapping an in-memory string as a mock `JavaFileObject`, which would
  eliminate the temp file entirely and remove the associated disk I/O on every
  keystroke check. Using mock files is a planned optimization.

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

