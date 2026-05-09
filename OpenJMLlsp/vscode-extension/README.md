<!-- SYNC: This file and openjml.github.io/documentation/openjml-vscode.md are kept as
     strict copies of each other (the .md file has a Jekyll front-matter header instead
     of this heading).  Edit one and apply the same change to the other. -->
# OpenJML for Visual Studio Code

JML specification type-checking and extended static checking (ESC) for Java,
powered by the [OpenJML](https://www.openjml.org) tool.

## Installation

0. Install VSCode, and have the executable findable on PATH or in a standard Applications folder
1. Download a current [OpenJML release](https://github.com/OpenJML/OpenJML/releases) into a clean folder.
2. Unzip the release `.zip` file in that folder.
3. Run `./install-vscode-extension` from that folder (do not move the script or any other contents of the installation folder).

The script installs the VS Code extension and sets `openjml.serverPath` automatically.
If the script fails it emits instructions for a manual workaround.

## Requirements

The extension requires an OpenJML installation on the local machine.
`openjml.serverPath` must point to the OpenJML installation folder or the `openjml-lsp` launcher script from the OpenJML distribution;
the installer sets this automatically.

**Version requirements:**
- VS Code 1.79 or later (the extension manifest declares `engines.vscode: ^1.79.0`; tested against 1.118).
- The UI test suite (`OpenJMLTest/vscode/`) requires Node.js ≥ 20 (`@vscode/vsce` and ExTester both require Node 16+; Node 20 LTS is the minimum recommended version).
- `vscode-extension-tester` ≥ 8.23 is required; versions targeting VS Code ≤ 1.110 use `@redhat-developer/locators` which does not support the xterm.js output panel used in 1.117+.

## Features

- JML type-check diagnostics (squigglies) on edit or save, with auto-recheck on focus changes
- Extended static checking (ESC) via SMT solver — manually or on save
- Per-method ESC status code lens (`✓ Verified` / `✗ N issue(s)`) for all classes in a file,
  including secondary top-level classes, member nested classes, local classes, and anonymous classes
- Ability to split ESC tasks to promote concurrency
- Hover showing JML specifications above the method under cursor
- JML keyword and backslash-token completion inside `//@ ...` and `/*@ ... */` annotations
- Document outline with Java and JML symbols (classes, methods, ghost/model declarations)
- Go to definition, find references, and rename for Java and JML identifiers
- Workspace symbol search (Find All Declarations) for cross-file navigation
- Signature help inside method call argument lists
- Folding ranges for multi-line JML annotation blocks
- JML syntax highlighting (semantic tokens) merged additively with Red Hat Java Extension coloring — covers JML clause keywords, modifiers, backslash expressions, operators, and literals inside JML context; in `full` mode also covers all Java symbols
- Status bar indicator showing how many ESC tasks are currently running
- Compilation with Runtime Assertion Checking
- Explorer context menu for running ESC and RAC on files and folders

## Commands

| Command | Palette title | Default keybinding |
|---|---|---|
| `openjml.checkJml` | OpenJML: Check JML | — |
| `openjml.runEsc` | OpenJML: Run ESC | Cmd+E / Ctrl+E |
| `openjml.runEscForMethod` | OpenJML: Run ESC for Method | Cmd+Alt+E / Ctrl+Alt+E |
| `openjml.saveAndRunEsc` | OpenJML: Save and Run ESC | Ctrl+Cmd+E / Ctrl+Shift+E |
| `openjml.runEscSplitByFile` | OpenJML: Run ESC Split by File | — |
| `openjml.runEscSplitByMethod` | OpenJML: Run ESC Split by Method | — |
| `openjml.runEscDir` | OpenJML: Run ESC on Project | — |
| `openjml.runRac` | OpenJML: Compile RAC | — |
| `openjml.indexProject` | OpenJML: Index Project | — |
| `openjml.clearMarkers` | OpenJML: Clear Markers | — |
| `openjml.clearMarkersSelected` | OpenJML: Clear Markers for Selection | — |
| `openjml.clearAndReindex` | OpenJML: Clear Caches and Reindex | — |
| `openjml.cancelEsc` | OpenJML: Cancel ESC | — |
| `openjml.abortMethodProof` | OpenJML: Abort Method Proof | — |

**Run ESC for Method** uses the code lens at or above the cursor to identify the method and its
fully-qualified name, so it works correctly for methods in secondary classes and nested classes.

**Run ESC Split by File / Split by Method** launch parallel ESC invocations — one per file
or one per method — to take advantage of concurrency.

**Save and Run ESC** saves the file first, then runs ESC. Useful when `dirtyFileAction` is set to `run`,
which means the default behavior is to check the editor content.

**Index Project** runs `--check` on all source files in the workspace, populating the declaration
index used by various navigation command.

**Clear Markers for Selection** clears OpenJML diagnostics for the file(s) or folder(s) selected
in the Explorer. **Clear Markers** clears all OpenJML diagnostics workspace-wide.

## Status Bar

While ESC tasks are running, a status bar item appears at the bottom of the window:

```
OpenJML N ESC task(s) running …
```

Clicking the item invokes **Cancel ESC**, stopping all in-progress proofs.

## Syntax Highlighting

OpenJML uses LSP semantic tokens to color JML constructs.  Tokens are emitted for the
following categories, all using names from the standard LSP token vocabulary so that VS Code
color themes apply automatically:

| Category | Examples |
|---|---|
| `keyword` | `requires`, `ensures`, `invariant`, `ghost`, `model`, `also`, `behavior`, `loop_invariant`,  …  |
| `modifier` | `pure`, `spec_public`, `spec_protected`, `nullable`, `non_null`, `strictly_pure`, `helper`,  …  |
| `function` | <code>\result</code>, <code>\old</code>, <code>\forall</code>, <code>\exists</code>, <code>\nothing</code>, <code>\fresh</code>, <code>\typeof</code>,  …  |
| `type` | `int`, `boolean`, <code>\bigint</code>, <code>\real</code>, <code>\locset</code>,  …  |
| `operator` | `==>`, `<==`, `<==>`, `<:`, `+`, `-`, `==`, … |
| `string` | String literals and text blocks inside JML expressions |
| `number` | Numeric and character literals inside JML expressions |
| `macro` | Reserved; not currently emitted |
| `decorator` | `@Override`, `@NonNull`, and other annotations |
| `comment` | Reserved; not currently emitted |
| `method`, `property`, `variable`, `parameter` | Resolved symbols inside JML expressions (AST strategy only)  (property = Java class field)|
| `class`, `interface`, `enum`, `struct` | Class, interface, enum, and record type references in JML expressions (AST strategy only; `struct` = Java record) |
| `namespace` | Package-qualified name prefixes in JML expressions (AST strategy only) |
| `typeParameter` | Type parameter references in JML expressions (AST strategy only) |
| `enumMember` | Enum constant references in JML expressions (AST strategy only) |

In addition, the declaration site of a symbol (e.g. a ghost field declaration) receives the
`declaration` modifier, `final` fields and locals receive `readonly`, `static` members
receive `static`, deprecated symbols receive `deprecated`, abstract methods and classes
receive `abstract`, and type references whose fully-qualified name begins with `java.` or
`javax.` receive `defaultLibrary`.

### Modes

**`preserve Java coloring`** (default, `openjml.syntaxColoringScope`; recommended with Red Hat
Java Extension installed): tokens are emitted only inside JML annotation context.  Java
constructs outside JML annotations are left to the Red Hat Java Extension.

**`overwrite Java coloring`** (set `openjml.syntaxColoringScope` to `overwrite Java coloring`):
tokens are emitted for all Java and JML constructs throughout the file, replacing whatever the
Java language server produced.  Use when no other Java extension is active.

### Strategies

**`ast`** (default): uses the attributed AST after the first `--check` completes.  Precise —
no false positives for Java identifiers named `requires`, `ensures`, etc.

**`regex`**: always uses regex-based line scanning instead of the AST.  Available as a
fallback but may incorrectly color Java identifiers that share a name with a JML keyword.

### Color adaptation

**For `.jml` files**: semantic token colors follow the active color theme automatically.
To override individual token category colors, add a `semanticTokenColorCustomizations`
entry to your VS Code settings:

```json
"editor.semanticTokenColorCustomizations": {
    "rules": {
        "keyword": "#569cd6",
        "modifier": "#c586c0",
        "function": "#4ec9b0"
    }
}
```

The names match the token type strings listed in the table above.

**For `.java` files**: the Red Hat Java Language Support extension registers its semantic
token provider asynchronously and can override OpenJML's tokens for JML content inside
`//@ …` and `/*@ … */` lines, treating those ranges as plain comments.  To ensure JML
constructs remain distinctly colored, the extension also applies **text editor decorations**
for the key JML token types (`keyword`, `modifier`, `function`, `method`, `type`).
Decorations take unconditional precedence over semantic tokens in VS Code's rendering
pipeline.

The decoration colors are fixed approximations of the VS Code Dark+/Light+ defaults for
each token type; they do **not** follow `editor.semanticTokenColorCustomizations` overrides
and do not adapt to custom color themes that assign non-standard colors to those token
types.  The VS Code extension API does not expose the active theme's semantic token colors
(only workbench color registry IDs are accessible via `ThemeColor`), so exact
theme-adaptive coloring is not achievable with the current API.

## Settings

| Setting | Default | Description |
|---|---|---|
| `openjml.serverPath` | `` | Path to the OpenJML installation folder or a `openjml-lsp` launcher script. Leave empty to auto-discover it in the OpenJML installation. Requires OpenJML to be installed separately. |
| `openjml.checkTriggerOn` | `edit` | When to run `--check`: `edit` (on every change), `save` (only on file save), or `manual` (never automatic; use the OpenJML: Check JML command). |
| `openjml.escTriggerOn` | `manual` | When to run `--esc`: `manual` (only via command) or `save` (on file save). |
| `openjml.dirtyFileAction` | `ask` | What to do when ESC is invoked on a file with unsaved changes: `ask` (prompt each time), `save` (always save silently first), or `run` (always run on the editor content). |
| `openjml.toolOptions` | `[]` | Project-independent OpenJML command-line options prepended to every tool invocation. Use `["--properties", "/path/to/file"]` to pass a properties file — one idiomatic way to supply a sequence of options; alternatively put individual flags directly in this array. Project-dependent settings (source path, class path, specs path) belong in the named settings below. |
| `openjml.specsPath` | `` | User additions prepended to the OpenJML specspath. If empty, OpenJML uses its default (sourcepath plus built-in system library specifications). If non-empty, this value is prepended to the assembled sourcepath and the result is passed as `--specs-path`. |
| `openjml.sourcePath` | `` | User additions prepended to the server-assembled sourcepath (which already includes the workspace folder roots). |
| `openjml.classPath` | `` | User additions prepended to the server-assembled classpath (which already includes the Java output directory). |
| `openjml.escEngine` | `fresh` | ESC execution engine: `fresh` (default — spawns a fresh OpenJML compilation context for each ESC task) or `concurrent` (share OpenJDK compilation contexts, which shares parsing and typechecking effort). |
| `openjml.escThreads` | `5` | Maximum number of concurrent ESC tasks. |
| `openjml.syntaxColoringScope` | `preserve Java coloring` | How OpenJML's semantic tokens interact with Java coloring: `preserve Java coloring` (default) — emit tokens only inside JML annotation context, leaving Java code to the Java language server; `overwrite Java coloring` — emit tokens for all Java and JML constructs, replacing whatever the Java language server produced. |
| `openjml.syntaxColoringStrategy` | `ast` | JML syntax coloring strategy: `ast` (uses the attributed AST when available — precise, no false positives) or `regex` (always uses regex line scanning — may color Java identifiers that share a name with a JML keyword). |
| `openjml.useIntegratedOutline` | `true` | When `true`, the Outline panel shows all Java and JML symbols together. When `false`, only JML-specific symbols are shown (complementing the Red Hat Java Extension's outline). |
| `openjml.javaMode` | `jml-only` | Controls which inlay hints are shown. `jml-only` (default) — suppress `var`-type hints for plain Java locals (assumes the Red Hat Java Extension shows those); JML ghost/model `var` hints are always shown. `full` — show `var`-type hints for all locals. |
| `openjml.client` | `vscode-java` | Client identifier sent to the server. Controls `javaMode` defaults. Leave as `vscode-java` when the Red Hat Java Extension is active. |
| `openjml.racOutputDir` | `` | Output directory for RAC-compiled class files (`-d`). Relative paths are resolved against the workspace root. Leave empty to use the Java output directory (`java.project.outputPath`). |

## Paths

The classpath, sourcepath, and specspath are crucial quantities for OpenJML. The server assembles them automatically from the workspace:

- **classpath** — `openjml.classPath` (user additions) + Java output directory (`java.project.outputPath`) + RAC output directory (if non-empty and different from the Java output directory).
- **sourcepath** — `openjml.sourcePath` (user additions) + the workspace folder roots.
- **specspath** — if `openjml.specsPath` is empty, no `--specs-path` is passed and OpenJML uses its default (sourcepath plus built-in system library specifications). If non-empty, the value is prepended to the assembled sourcepath and passed as `--specs-path`.

Path values may contain environment-variable references of the form `$VARNAME`, `${VARNAME}`, or `$(VARNAME)`; the server substitutes the variable's value before passing the result to OpenJML.

## Co-existing with the Red Hat Java Extension

This extension is designed to work alongside the
[Red Hat Language Support for Java](https://marketplace.visualstudio.com/items?itemName=redhat.java)
extension.  With the default settings, OpenJML only adds JML-specific capabilities — type-check diagnostics,
ESC code lenses, JML completions, JML hover, JML syntax coloring — and defers Java navigation,
outline, and plain-Java `var` inlay hints to the Red Hat extension (`openjml.javaMode: "jml-only"`).
Java syntax coloring is preserved by default via `openjml.syntaxColoringScope: "preserve Java coloring"`.  The JML semantic tokens are merged *additively* on top of whatever the Red Hat
extension produces, so JML keywords and modifiers are colored without disturbing Java coloring.

**Warning:** The Red Hat Java formatter normalizes `//` comment lines by inserting a space after
`//`, changing `//@ requires ...` to `// @ requires ...`, which silently disables all JML
annotations on those lines. The extension warns once per workspace on activation
and offers to disable `java.format.enabled`. Manual formatting (Shift+Alt+F) is still available;
configure a formatter profile that excludes comment reformatting if you need both.

**Outline duplication:** With `useIntegratedOutline: true` (the default), the Outline panel
receives declarations from both the Red Hat Java extension (Java symbols) and the OpenJML
extension (Java + JML symbols together). This produces duplicate Java entries. To remove the
duplicates either fold/close the Java contribution in the Outline panel, or set
`openjml.useIntegratedOutline` to `false` so OpenJML shows only JML-specific symbols and
defers Java symbols entirely to the Red Hat extension.
