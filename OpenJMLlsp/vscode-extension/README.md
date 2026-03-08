# OpenJML for Visual Studio Code

JML specification type-checking and extended static checking (ESC) for Java,
powered by the [OpenJML](https://www.openjml.org) tool.

## Requirements

Install OpenJML and set `openjml.serverPath` in your workspace settings to the
full path of the `openjml-lsp` launcher script from the OpenJML distribution.

## Features

- JML type-check diagnostics (squigglies) on edit or save
- Extended static checking (ESC) via SMT solver — manually or on save
- Per-method ESC status code lens (✓ Verified / ✗ N issues)
- Hover showing JML specifications above the method under cursor

## Commands

| Command | Default keybinding |
|---|---|
| OpenJML: Run ESC | Cmd+E / Ctrl+E |
| OpenJML: Run ESC for Method | Cmd+Alt+E / Ctrl+Alt+E |
| OpenJML: Save and Run ESC | — |

## Settings

| Setting | Default | Description |
|---|---|---|
| `openjml.serverPath` | `` | Path to `openjml-lsp` script |
| `openjml.checkTriggerOn` | `edit` | When to run `--check` |
| `openjml.escTriggerOn` | `manual` | When to run `--esc` |
| `openjml.specsPath` | `` | Path to specs directory |
| `openjml.solversPath` | `` | Path to SMT solvers directory |
| `openjml.sourcePath` | `` | Source roots for cross-file references |
| `openjml.classPath` | `` | Classpath for pre-compiled dependencies |
| `openjml.dirtyFileAction` | `ask` | What to do when ESC is invoked on unsaved changes |
