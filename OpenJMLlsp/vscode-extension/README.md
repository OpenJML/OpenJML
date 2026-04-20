<!-- SYNC: This file and openjml.github.io/documentation/openjml-vscode.md are kept as
     strict copies of each other (the .md file has a Jekyll front-matter header instead
     of this heading).  Edit one and apply the same change to the other. -->
# OpenJML for Visual Studio Code

JML specification type-checking and extended static checking (ESC) for Java,
powered by the [OpenJML](https://www.openjml.org) tool.

## Installation

1. Download a current [OpenJML release](https://github.com/OpenJML/OpenJML/releases) into a clean folder.
2. Unzip the release `.zip` file in that folder.
3. Run `./install-vscode-extension` from that folder (do not move the script or any other contents of the installation folder).

The script installs the VS Code extension and sets `openjml.serverPath` automatically.
If the script fails it prints instructions for a manual workaround.

## Requirements

The extension requires an OpenJML installation on the local machine.
`openjml.serverPath` must point to the `openjml-lsp` launcher script from the OpenJML distribution;
the installer sets this automatically.

## Features

- JML type-check diagnostics (squigglies) on edit or save
- Extended static checking (ESC) via SMT solver — manually, on save, or on edit
- Per-method ESC status code lens (`✓ Verified` / `✗ N issue(s)`) for all classes in a file,
  including secondary top-level classes, member nested classes, local classes, and anonymous classes
- Hover showing JML specifications above the method under cursor
- JML keyword and backslash-token completion inside `//@ ...` and `/*@ ... */` annotations
- Document outline with Java and JML symbols (classes, methods, ghost/model declarations)
- Go to definition, find references, and rename for Java and JML identifiers
- Signature help inside method call argument lists
- Folding ranges for multi-line JML annotation blocks
- JML syntax highlighting (semantic tokens) merged additively with Red Hat Java Extension coloring — covers JML clause keywords, modifiers, backslash expressions, operators, and literals inside JML context; in `full` mode also covers all Java symbols
- Status bar indicator showing how many ESC tasks are currently running
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
or one per method — so code lenses update as each proof completes rather than all at once.

**Save and Run ESC** saves the file first, then runs ESC. Useful when `dirtyFileAction` is `run`
(which would otherwise verify the saved disk copy, not the current edits).

**Index Project** runs `--check` on all source files in the workspace, populating the declaration
index used by "Find All Declarations" (`workspace/symbol`). Run it once after opening a project
so that cross-file navigation covers files that have not yet been edited.

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
| `keyword` | `requires`, `ensures`, `invariant`, `ghost`, `model`, `also`, `behavior`, `loop_invariant` |
| `modifier` | `pure`, `spec_public`, `spec_protected`, `nullable`, `non_null`, `strictly_pure`, `helper` |
| `function` | `\result`, `\old`, `\forall`, `\exists`, `\nothing`, `\fresh`, `\typeof` |
| `type` | `int`, `boolean`, `\bigint`, `\real`, `\locset` |
| `operator` | `==>`, `<==`, `<==>`, `<:`, `+`, `-`, `==`, … |
| `string` | String literals and text blocks inside JML expressions |
| `number` | Numeric and character literals inside JML expressions |
| `decorator` | `@Override`, `@NonNull`, and other annotations |
| `method`, `property`, `variable`, `parameter` | Resolved symbols inside JML expressions (AST strategy only) |

In addition, the declaration site of a symbol (e.g. a ghost field declaration) receives the
`declaration` modifier, `final` fields and locals receive `readonly`, and `static` members
receive `static`.

### Modes

**`jml-only`** (default, recommended with Red Hat Java Extension installed): only JML constructs
are highlighted.  Java constructs outside JML annotation context are left to the Red Hat Java
Extension.

**`full`** (set `openjml.javaMode` to `full`): all Java and JML constructs are highlighted,
including class/method/field declarations throughout the file.  Use when no other Java
extension is active.

### Strategies

**`ast`** (default): uses the attributed AST after the first `--check` completes.  Precise —
no false positives for Java identifiers named `requires`, `ensures`, etc.  Falls back to
regex before the first check.

**`regex`**: always uses line-pattern matching against JML comment regions.  Instant on every
keystroke, but may incorrectly color Java identifiers that share a name with a JML keyword.

### Customizing colors

To override a token category's color, add a `semanticTokenColorCustomizations` entry to your
VS Code settings:

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

## Settings

| Setting | Default | Description |
|---|---|---|
| `openjml.serverPath` | `` | Path to the `openjml-lsp` launcher script. Leave empty to auto-discover it in the parent directory of the extension or on the system PATH. Requires OpenJML to be installed separately. |
| `openjml.checkTriggerOn` | `edit` | When to run `--check`: `edit` (on every change), `save` (only on file save), or `manual` (never automatic; use the OpenJML: Check JML command). |
| `openjml.escTriggerOn` | `manual` | When to run `--esc`: `manual` (only via command), `save` (on file save), or `edit` (on every change — expensive). |
| `openjml.dirtyFileAction` | `ask` | What to do when ESC is invoked on a file with unsaved changes: `ask` (prompt each time), `save` (always save silently first), or `run` (always run on the saved disk file). |
| `openjml.propertiesFile` | `` | Path to an OpenJML `.properties` file for project-level options (prover, timeout, nullable-by-default, etc.). Leave empty to auto-discover `openjml.properties` in the workspace root. |
| `openjml.specsPath` | `` | Path to the OpenJML specs directory. Leave empty to use the default from the launcher script. |
| `openjml.sourcePath` | `` | Source root(s) for cross-file references (`-sourcepath`). Separate multiple roots with `:` (Unix) or `;` (Windows). Leave empty for single-file projects. |
| `openjml.classPath` | `` | Classpath for pre-compiled dependencies (`-classpath`). Separate multiple entries with `:` (Unix) or `;` (Windows). Leave empty if no external jars are needed. |
| `openjml.escEngine` | `subprocess` | ESC execution engine: `subprocess` (default — spawns a fresh OpenJML process), `concurrent` (in-process per-method, serialized within a file), or `fresh` (truly concurrent, higher startup cost). |
| `openjml.escThreads` | `5` | Maximum concurrent ESC threads (only used when `escEngine` is `concurrent`). |
| `openjml.syntaxColoringScope` | `preserve Java coloring` | How OpenJML's semantic tokens interact with Java coloring: `preserve Java coloring` (default) — emit tokens only inside JML annotation context, leaving Java code to the Java language server; `overwrite Java coloring` — emit tokens for all Java and JML constructs, replacing whatever the Java language server produced. |
| `openjml.syntaxColoringStrategy` | `ast` | JML syntax coloring strategy: `ast` (uses the attributed AST when available — precise, no false positives; falls back to regex before the first type-check) or `regex` (always uses regex — instant on every keystroke, but may color Java identifiers that share a name with a JML keyword). |
| `openjml.useIntegratedOutline` | `true` | When `true`, the Outline panel shows all Java and JML symbols together. When `false`, only JML-specific symbols are shown (complementing the Red Hat Java Extension's outline). |
| `openjml.javaMode` | `jml-only` | Controls which constructs are highlighted and navigated. `jml-only` (default) — only JML constructs; defers Java navigation and coloring to the Red Hat Java Extension. `full` — all Java and JML constructs; use when no Java extension is installed. |
| `openjml.client` | `vscode-java` | Client identifier sent to the server. Controls `javaMode` defaults. Leave as `vscode-java` when the Red Hat Java Extension is active. |
| `openjml.racOutputDir` | `` | Output directory for RAC-compiled class files (`-d`). Relative paths are resolved against the workspace root. Leave empty to use `rac-classes` in the workspace root. |

## Co-existing with the Red Hat Java Extension

This extension is designed to work alongside the
[Red Hat Language Support for Java](https://marketplace.visualstudio.com/items?itemName=redhat.java)
extension.  With `javaMode: "jml-only"` (the default), OpenJML only adds JML-specific
capabilities — type-check diagnostics, ESC code lenses, JML completions, JML hover, JML syntax
coloring — and defers Java navigation, outline, inlay hints, and Java coloring to the Red Hat
extension.  The JML semantic tokens are merged *additively* on top of whatever the Red Hat
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
