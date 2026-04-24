/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.eclipse.widgets.LabelFieldEditor;

/**
 * Abstract base for OpenJML preference pages.
 *
 * <p>Manages the field-editor lifecycle ({@link #performOk},
 * {@link #performDefaults}) and provides the two field-creation methods
 * ({@link #createPluginAndLspFields} and {@link #createToolOptionFields})
 * shared by the main tabbed page and the individual sub-pages.
 *
 * <p>All {@link BooleanFieldEditor}s are created with
 * {@link BooleanFieldEditor#SEPARATE_LABEL} so that the label occupies the
 * left column and the checkbox the right column, consistent with
 * {@link StringFieldEditor} and {@link ComboFieldEditor}.  This avoids any
 * need to call the protected {@code adjustForNumColumns} method.
 *
 * <p>{@link #finalizeTab} restores a clean 2-column {@link GridLayout} after
 * all editors for a tab have been created, because {@link FieldEditor}
 * constructors reset the parent's layout as a side-effect.
 */
abstract class OpenJMLPreferencesBase extends PreferencePage
        implements IWorkbenchPreferencePage {

    protected final List<FieldEditor> allEditors = new ArrayList<>();

    /** Reference to the server-path field editor, saved for validation in {@link #performOk}. */
    private StringFieldEditor serverPathEditor;
    private StringFieldEditor timeoutEditor;

    /** Syntax-color block; non-null only when the Syntax Colors tab has been created. */
    private SyntaxColorBlock syntaxColorBlock;

    // -----------------------------------------------------------------------
    // IWorkbenchPreferencePage
    // -----------------------------------------------------------------------

    @Override
    public void init(IWorkbench workbench) {
        setPreferenceStore(org.openjml.ui.Activator.getDefault().getPreferenceStore());
    }

    // -----------------------------------------------------------------------
    // Lifecycle
    // -----------------------------------------------------------------------

    @Override
    public boolean performOk() {
        // Validate the server path before committing if the user explicitly set one.
        if (serverPathEditor != null) {
            String typedPath = serverPathEditor.getStringValue().trim();
            if (!typedPath.isBlank()) {
                if (!OpenJMLStreamConnectionProvider.isServerAvailable(typedPath)) {
                    String script = OpenJMLStreamConnectionProvider.resolveToScript(typedPath);
                    String msg = "OpenJML launcher not found or not executable:\n\n  " + script;
                    setErrorMessage(msg);
                    setValid(false);
                    MessageDialog.openError(getShell(), "OpenJML: Launcher Not Found", msg);
                    return false;  // keep dialog open
                }
            } else {
                // Blank = look up "openjml-lsp" on $PATH at startup.
                // No validation performed here; any failure will surface when the server starts.
            }
        }
        // Validate the timeout field: must be blank or a non-negative integer.
        if (timeoutEditor != null) {
            String timeoutVal = timeoutEditor.getStringValue().trim();
            if (!timeoutVal.isBlank()) {
                boolean valid = false;
                try {
                    valid = Long.parseLong(timeoutVal) >= 0;
                } catch (NumberFormatException ignored) {}
                if (!valid) {
                    String msg = "Proof timeout must be a non-negative integer or blank (for no timeout).";
                    setErrorMessage(msg);
                    setValid(false);
                    MessageDialog.openError(getShell(), "OpenJML: Invalid Timeout", msg);
                    return false;
                }
            }
        }

        setErrorMessage(null);
        setValid(true);

        // Store all fields.  The Activator property-change listener fires synchronously
        // here for lspServerPathKey changes and calls LspPartListener.restartServer(),
        // which handles stopping the old server (on a background thread) and reconnecting.
        allEditors.forEach(FieldEditor::store);
        if (syntaxColorBlock != null) syntaxColorBlock.store(getPreferenceStore());
        return true;
    }

    @Override
    protected void performDefaults() {
        allEditors.forEach(FieldEditor::loadDefault);
        if (syntaxColorBlock != null) syntaxColorBlock.loadDefaults();
        super.performDefaults();
    }

    // -----------------------------------------------------------------------
    // Field-editor helpers
    // -----------------------------------------------------------------------

    /** Registers an editor: wires it to this page and the store, loads it. */
    protected void addEditor(FieldEditor editor) {
        editor.setPage(this);
        editor.setPreferenceStore(getPreferenceStore());
        editor.load();
        allEditors.add(editor);
    }

    protected void addLabel(Composite parent, String text, int swtOptions) {
        addEditor(new LabelFieldEditor("zzzzz.label", text, swtOptions, parent));
    }

    protected void addSpace(Composite parent) {
        addEditor(new LabelFieldEditor("zzzzz.space", "", SWT.NONE, parent));
    }

    /**
     * Creates a boolean field editor using {@link BooleanFieldEditor#SEPARATE_LABEL}
     * style so that the label sits in the left column and the checkbox in the
     * right column — consistent with all other 2-column field editors and
     * avoiding any call to the inaccessible {@code adjustForNumColumns} method.
     */
    protected void addBoolean(Composite parent, String key, String label) {
        addEditor(new BooleanFieldEditor(key, label, BooleanFieldEditor.SEPARATE_LABEL, parent));
    }

    /**
     * Restores a clean 2-column {@link GridLayout} on {@code parent} after all
     * its field editors have been created.  Necessary because each
     * {@link FieldEditor} constructor resets the parent layout as a side-effect.
     */
    protected void finalizeTab(Composite parent) {
        GridLayout layout = new GridLayout(2, false);
        layout.marginWidth = 0;
        layout.marginHeight = 0;
        layout.verticalSpacing = 4;
        parent.setLayout(layout);
    }

    // -----------------------------------------------------------------------
    // Shared field-creation methods
    // -----------------------------------------------------------------------

    /** Populates a composite with Tab 1 — Plugin and LSP Settings. */
    protected void createPluginAndLspFields(Composite parent) {

        // ── LSP Server ──────────────────────────────────────────────────────
        addLabel(parent, "LSP Server", SWT.SEPARATOR | SWT.HORIZONTAL);

        serverPathEditor = new StringFieldEditor(OpenJMLOptions.lspServerPathKey,
                "OpenJML installation folder or launcher script path (blank = find on PATH):",
                parent);
        addEditor(serverPathEditor);

        addSpace(parent);

        // ── Analysis triggers ───────────────────────────────────────────────
        addLabel(parent, "Analysis Triggers", SWT.SEPARATOR | SWT.HORIZONTAL);

        addEditor(new ComboFieldEditor(OpenJMLOptions.checkTriggerOnKey,
                "JML type-check trigger:",
                new String[][] {
                    { "On edit (instant feedback)", "edit"   },
                    { "On save only",               "save"   },
                    { "Manual only — slow/problematic codebases", "manual" } },
                parent));

        addEditor(new ComboFieldEditor(OpenJMLOptions.escTriggerOnKey,
                "ESC (static checking) trigger:",
                new String[][] {
                    { "Manual only", "manual" },
                    { "On save",     "save"   } },
                parent));

        addEditor(new ComboFieldEditor(OpenJMLOptions.escDirtyFilesBehaviorKey,
                "ESC behavior on edited (unsaved) files:",
                new String[][] {
                    { "Always ask",                            "ask"     },
                    { "Always act on edited content",          "content" },
                    { "Always save edited files then run ESC", "save"    } },
                parent));

        addSpace(parent);

        // ── Paths ───────────────────────────────────────────────────────────
        addLabel(parent, "Paths", SWT.SEPARATOR | SWT.HORIZONTAL);

        // propertiesFile preference hidden — use toolOptions instead.
        // addEditor(new StringFieldEditor(OpenJMLOptions.propertiesFileKey,
        //         "openjml.properties file (blank = auto-discover):",
        //         parent));
        addEditor(new StringFieldEditor(OpenJMLOptions.specsPathKey,
                "Specs path (blank = default from launcher):",
                parent));

        addEditor(new StringFieldEditor(OpenJMLOptions.sourcePathKey,
                "Source path for -sourcepath (blank = single-file):",
                parent));
        addEditor(new StringFieldEditor(OpenJMLOptions.classPathKey,
                "Classpath for -classpath (blank = none):",
                parent));

        addSpace(parent);

        // ── ESC engine ──────────────────────────────────────────────────────
        addLabel(parent, "ESC Engine", SWT.SEPARATOR | SWT.HORIZONTAL);

        addEditor(new ComboFieldEditor(OpenJMLOptions.escEngineKey,
                "ESC engine:",
                new String[][] {
                    { "fresh (separate process, default)", "fresh" },
                    { "concurrent (in-process, shared IAPI)",  "concurrent" } },
                parent));

        addEditor(new StringFieldEditor(OpenJMLOptions.escThreadsKey,
                "ESC parallel threads (0 = server default):",
                parent));

        addSpace(parent);

        // ── RAC / Outline ───────────────────────────────────────────────────
        addLabel(parent, "RAC and Outline", SWT.SEPARATOR | SWT.HORIZONTAL);

        addEditor(new StringFieldEditor(OpenJMLOptions.racOutputDirKey,
                "RAC output directory (blank = project output):",
                parent));

        addBoolean(parent, OpenJMLOptions.racSaveBeforeKey,
                "Always save edited files before running RAC (no dialog)");

        addBoolean(parent, OpenJMLOptions.useIntegratedOutlineKey,
                "Show full Java+JML outline (uncheck for JML-only symbols)");

        addSpace(parent);

        // ── Syntax coloring ─────────────────────────────────────────────────
        addLabel(parent, "Syntax Coloring", SWT.SEPARATOR | SWT.HORIZONTAL);

        addEditor(new ComboFieldEditor(OpenJMLOptions.syntaxColoringStrategyKey,
                "JML syntax coloring strategy:",
                new String[][] {
                    { "Regex (instant, always active)",                           "regex" },
                    { "AST (precise, uses attributed tree; falls back to regex)", "ast"   } },
                parent));

        addEditor(new ComboFieldEditor(OpenJMLOptions.syntaxColoringScopeKey,
                "JML syntax coloring scope (.java files):",
                new String[][] {
                    { "Preserve Java coloring (JML annotations only)", "preserve Java coloring" },
                    { "Overwrite Java coloring (all Java + JML)",       "overwrite Java coloring" } },
                parent));

        finalizeTab(parent);
    }

    /** Populates a composite with Tab 2 — OpenJML Tool Options (JML / ESC / RAC). */
    protected void createToolOptionFields(Composite parent) {

        // ── JML ─────────────────────────────────────────────────────────────
        addLabel(parent, "JML", SWT.SEPARATOR | SWT.HORIZONTAL);

        addBoolean(parent, OpenJMLOptions.nullableByDefaultKey,
                "Nullable by default (--nullable-by-default)");

        addEditor(new ComboFieldEditor(OpenJMLOptions.langKey,
                "Language variant (--lang):",
                new String[][] {
                    { "openjml (default)", "openjml" },
                    { "jml (strict)",      "jml"     } },
                parent));

        addBoolean(parent, OpenJMLOptions.showNotImplementedKey,
                "Warn about unimplemented constructs (--show-not-implemented)");

        addEditor(new StringFieldEditor(OpenJMLOptions.optionalKeysKey,
                "Optional annotation keys, comma-separated (--keys):",
                parent));

        addEditor(new ComboFieldEditor(OpenJMLOptions.verbosityKey,
                "Verbosity level (--verboseness):",
                new String[][] {
                    { "normal",   "1" },
                    { "progress", "2" },
                    { "verbose",  "3" },
                    { "debug",    "4" } },
                parent));

        addBoolean(parent, OpenJMLOptions.checkAccessibleKey,
                "Check accessible clauses (--check-accessible)");

        addEditor(new ComboFieldEditor(OpenJMLOptions.codeMathKey,
                "Arithmetic mode for Java code (--code-math):",
                new String[][] {
                    { "java",   "java"   },
                    { "safe",   "safe"   },
                    { "bigint", "bigint" } },
                parent));

        addEditor(new ComboFieldEditor(OpenJMLOptions.specMathKey,
                "Arithmetic mode for specs (--spec-math):",
                new String[][] {
                    { "java",   "java"   },
                    { "safe",   "safe"   },
                    { "bigint", "bigint" } },
                parent));

        addEditor(new ComboFieldEditor(OpenJMLOptions.arithmeticKey,
                "Arithmetic warning severity (--arithmetic-failure):",
                new String[][] {
                    { "soft",  "soft"  },
                    { "hard",  "hard"  },
                    { "quiet", "quiet" } },
                parent));

        addBoolean(parent, OpenJMLOptions.allowPureInSpecsKey,
                "Allow pure methods in specifications (--allow-pure-in-specs)");

        addBoolean(parent, OpenJMLOptions.requireWhiteSpaceKey,
                "Require white space after @ in JML comment (--require-white-space)");

        addEditor(new StringFieldEditor(OpenJMLOptions.warnKey,
                "Warning keys to enable, comma-separated (--warn):",
                parent));

        addEditor(new StringFieldEditor(OpenJMLOptions.noWarnKey,
                "Warning keys to disable, comma-separated (--no-warn):",
                parent));

        addSpace(parent);

        // ── ESC ─────────────────────────────────────────────────────────────
        addLabel(parent, "ESC", SWT.SEPARATOR | SWT.HORIZONTAL);

        addEditor(new ComboFieldEditor(OpenJMLOptions.escMaxWarningsKey,
                "Max warnings per method (--esc-max-warnings):",
                new String[][] {
                    { "all", "2147483647" },
                    { "1", "1" }, { "2", "2" }, { "3", "3" },
                    { "4", "4" }, { "5", "5" }, { "6", "6" },
                    { "7", "7" }, { "8", "8" }, { "9", "9" } },
                parent));

        timeoutEditor = new StringFieldEditor(OpenJMLOptions.timeoutKey,
                "Proof timeout in seconds (--timeout; blank = infinite):",
                parent);
        addEditor(timeoutEditor);

        addEditor(new ComboFieldEditor(OpenJMLOptions.feasibilityKey,
                "Feasibility checking (--check-feasibility):",
                new String[][] {
                    { "none",  "none"  },
                    { "basic", "basic" },
                    { "all",   "all"   } },
                parent));

        addBoolean(parent, OpenJMLOptions.traceKey,
                "Enable counterexample tracing (--trace)");

        addBoolean(parent, OpenJMLOptions.subexpressionsKey,
                "Enable tracing with subexpressions (--subexpressions)");

        addBoolean(parent, OpenJMLOptions.counterexampleKey,
                "Output complete raw counterexample (--counterexample)");

        addEditor(new ComboFieldEditor(OpenJMLOptions.escBvKey,
                "Bit-vector arithmetic (--esc-bv):",
                new String[][] {
                    { "auto",  "auto"  },
                    { "true",  "true"  },
                    { "false", "false" } },
                parent));

        addBoolean(parent, OpenJMLOptions.escTriggersKey,
                "Enable quantifier triggers in SMT encoding (--triggers)");

        addBoolean(parent, OpenJMLOptions.escWarningsPathKey,
                "Find all counterexample paths to each invalid assert (--esc-warnings-path)");

        addEditor(new StringFieldEditor(OpenJMLOptions.splitKey,
                "Split proof into sections (--split; blank = none):",
                parent));

        addEditor(new StringFieldEditor(OpenJMLOptions.solverSeedKey,
                "Seed for solver RNG (--solver-seed; 0 = default):",
                parent));

        addSpace(parent);

        // ── RAC ─────────────────────────────────────────────────────────────
        addLabel(parent, "RAC", SWT.SEPARATOR | SWT.HORIZONTAL);

        addBoolean(parent, OpenJMLOptions.compileToJavaAssertKey,
                "Compile JML checks as Java asserts (--rac-compile-to-java-assert)");

        addBoolean(parent, OpenJMLOptions.racCheckJavaFeaturesKey,
                "Check Java language features at runtime (--rac-java-checks)");

        addBoolean(parent, OpenJMLOptions.racCheckAssumptionsKey,
                "Check that assumptions hold at runtime (--rac-check-assumptions)");

        addBoolean(parent, OpenJMLOptions.racPreconditionEntryKey,
                "Distinguish entry vs. internal precondition failures (--rac-precondition-entry)");

        addEditor(new ComboFieldEditor(OpenJMLOptions.racShowSourceKey,
                "Source info in RAC error messages (--rac-show-source):",
                new String[][] {
                    { "source (full source line)",   "source" },
                    { "line (file and line number)", "line"   },
                    { "none",                        "none"   } },
                parent));

        addBoolean(parent, OpenJMLOptions.showNotExecutableKey,
                "Warn about non-executable constructs (--show-not-executable)");

        addEditor(new ComboFieldEditor(OpenJMLOptions.racMissingModelFieldRepKey,
                "Action when model field has no rep clause (--rac-missing-model-field-rep):",
                new String[][] {
                    { "skip",  "skip"  },
                    { "warn",  "warn"  },
                    { "error", "error" } },
                parent));

        finalizeTab(parent);
    }

    // -----------------------------------------------------------------------
    // Tab 2 — Syntax Colors
    // -----------------------------------------------------------------------

    /**
     * Populates a composite with Tab 2 — JML Syntax Colors.
     *
     * <p>Uses a JDT-style list + panel layout: a scrolling list on the left
     * shows all 19 active token types; selecting one shows its color and
     * style options on the right.
     */
    protected void createSyntaxColorFields(Composite parent) {
        syntaxColorBlock = new SyntaxColorBlock(getPreferenceStore());
        syntaxColorBlock.createControl(parent);
    }

    // -----------------------------------------------------------------------
    // SyntaxColorBlock — JDT-style list + color-panel widget
    // -----------------------------------------------------------------------

    /**
     * A JDT-style syntax-color control.
     *
     * <p>Left side: a {@code org.eclipse.swt.widgets.List} of token-type labels.
     * Right side: a {@link ColorSelector} button plus Bold / Italic / Underline /
     * Strikethrough checkboxes.  Changing the list selection updates the right panel.
     * Changes are held in memory until {@link #store(IPreferenceStore)} is called.
     */
    private static final class SyntaxColorBlock {

        private final java.util.List<OpenJMLOptions.TokenColorEntry> entries =
                OpenJMLOptions.TOKEN_COLORS;

        // In-memory state (parallel to entries list)
        private final RGB[]     currentColors;
        private final boolean[] currentBold;
        private final boolean[] currentItalic;
        private final boolean[] currentUnder;
        private final boolean[] currentStrike;

        // Widgets (null until createControl is called)
        private org.eclipse.swt.widgets.List list;
        private ColorSelector colorSelector;
        private Button boldBtn, italicBtn, underlineBtn, strikeBtn;
        private int selectedIndex = 0;

        /** True once the user changes any value in this instance's UI. */
        private boolean modified = false;

        SyntaxColorBlock(IPreferenceStore store) {
            int n = entries.size();
            currentColors = new RGB[n];
            currentBold    = new boolean[n];
            currentItalic  = new boolean[n];
            currentUnder   = new boolean[n];
            currentStrike  = new boolean[n];
            loadFrom(store);
        }

        private void loadFrom(IPreferenceStore store) {
            for (int i = 0; i < entries.size(); i++) {
                OpenJMLOptions.TokenColorEntry e = entries.get(i);
                currentColors[i] = PreferenceConverter.getColor(store, e.colorKey());
                currentBold[i]    = store.getBoolean(e.boldKey());
                currentItalic[i]  = store.getBoolean(e.italicKey());
                currentUnder[i]   = store.getBoolean(e.underlineKey());
                currentStrike[i]  = store.getBoolean(e.strikethroughKey());
            }
        }

        /**
         * Saves all current values to the preference store, but only if this
         * instance was actually modified by the user.  This prevents a stale
         * page instance (e.g., a sub-page opened but not touched) from
         * overwriting changes made in a different page instance.
         */
        void store(IPreferenceStore store) {
            if (!modified) return;
            // Capture any unsaved state from the currently-displayed panel
            // before writing arrays to the store.
            saveCurrentPanel();
            for (int i = 0; i < entries.size(); i++) {
                OpenJMLOptions.TokenColorEntry e = entries.get(i);
                PreferenceConverter.setValue(store, e.colorKey(), currentColors[i]);
                store.setValue(e.boldKey(),          currentBold[i]);
                store.setValue(e.italicKey(),        currentItalic[i]);
                store.setValue(e.underlineKey(),     currentUnder[i]);
                store.setValue(e.strikethroughKey(), currentStrike[i]);
            }
            // Refresh active colorizers so changes are visible immediately.
            LspPartListener.refreshAllColorizers();
        }

        /** Resets all values to their defaults and updates the UI. */
        void loadDefaults() {
            modified = true;
            for (int i = 0; i < entries.size(); i++) {
                OpenJMLOptions.TokenColorEntry e = entries.get(i);
                currentColors[i] = e.defaultRgb();
                currentBold[i]    = e.bold();
                currentItalic[i]  = e.italic();
                currentUnder[i]   = e.underline();
                currentStrike[i]  = e.strikethrough();
            }
            if (list != null && !list.isDisposed()) updatePanel(selectedIndex);
        }

        void createControl(Composite parent) {
            // Set the layout directly on parent (consistent with how other tabs call
            // finalizeTab).  2-column grid: list on left, color panel on right.
            GridLayout layout = new GridLayout(2, false);
            layout.marginWidth  = 0;
            layout.marginHeight = 0;
            layout.verticalSpacing = 4;
            parent.setLayout(layout);

            // ── Left: token-type list ───────────────────────────────────────
            list = new org.eclipse.swt.widgets.List(parent,
                    SWT.SINGLE | SWT.BORDER);
            list.add("");                                              // blank line above first entry
            for (OpenJMLOptions.TokenColorEntry e : entries) list.add(e.label());
            list.add("");                                              // blank line below last entry

            // Size exactly to show all items (including spacers) with no scrollbars.
            int itemH = list.getItemHeight();
            GridData listGd = new GridData(SWT.FILL, SWT.BEGINNING, false, false);
            listGd.widthHint  = 240;
            listGd.heightHint = list.getItemCount() * itemH + 4;     // +4 for border
            list.setLayoutData(listGd);

            // ── Right: color + style panel ──────────────────────────────────
            Composite panel = new Composite(parent, SWT.NONE);
            panel.setLayout(new GridLayout(2, false));
            panel.setLayoutData(new GridData(SWT.FILL, SWT.BEGINNING, false, false));

            new Label(panel, SWT.NONE).setText("Color:");
            colorSelector = new ColorSelector(panel);
            colorSelector.getButton().setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, false, false));

            boldBtn      = addStyleCheck(panel, "Bold");
            italicBtn    = addStyleCheck(panel, "Italic");
            underlineBtn = addStyleCheck(panel, "Underline");
            strikeBtn    = addStyleCheck(panel, "Strikethrough");

            // ── Wire up listeners ───────────────────────────────────────────
            list.addSelectionListener(new SelectionAdapter() {
                @Override public void widgetSelected(SelectionEvent e) {
                    int sel = list.getSelectionIndex();
                    // Index 0 = top spacer; index entries.size()+1 = bottom spacer — ignore both.
                    if (sel <= 0 || sel > entries.size()) return;
                    saveCurrentPanel();
                    selectedIndex = sel - 1;   // offset by 1 for the top blank item
                    updatePanel(selectedIndex);
                }
            });

            colorSelector.addListener(event -> {
                Object newVal = event.getNewValue();
                if (newVal instanceof RGB rgb && selectedIndex >= 0 && selectedIndex < entries.size()) {
                    currentColors[selectedIndex] = rgb;
                    modified = true;
                }
            });

            boldBtn.addSelectionListener(new SelectionAdapter() {
                @Override public void widgetSelected(SelectionEvent e) {
                    if (selectedIndex >= 0) { currentBold[selectedIndex] = boldBtn.getSelection(); modified = true; }
                }
            });
            italicBtn.addSelectionListener(new SelectionAdapter() {
                @Override public void widgetSelected(SelectionEvent e) {
                    if (selectedIndex >= 0) { currentItalic[selectedIndex] = italicBtn.getSelection(); modified = true; }
                }
            });
            underlineBtn.addSelectionListener(new SelectionAdapter() {
                @Override public void widgetSelected(SelectionEvent e) {
                    if (selectedIndex >= 0) { currentUnder[selectedIndex] = underlineBtn.getSelection(); modified = true; }
                }
            });
            strikeBtn.addSelectionListener(new SelectionAdapter() {
                @Override public void widgetSelected(SelectionEvent e) {
                    if (selectedIndex >= 0) { currentStrike[selectedIndex] = strikeBtn.getSelection(); modified = true; }
                }
            });

            // Select the first real entry (index 1 — index 0 is the top blank spacer).
            if (!entries.isEmpty()) {
                list.setSelection(1);
                updatePanel(0);
            }
        }

        private static Button addStyleCheck(Composite parent, String label) {
            new Label(parent, SWT.NONE).setText("");   // spacer in col 1
            Button btn = new Button(parent, SWT.CHECK);
            btn.setText(label);
            btn.setLayoutData(new GridData(SWT.LEFT, SWT.CENTER, false, false));
            return btn;
        }

        /** Saves the panel's current widget state back into the in-memory arrays. */
        private void saveCurrentPanel() {
            if (selectedIndex < 0 || selectedIndex >= entries.size()) return;
            currentColors[selectedIndex] = colorSelector.getColorValue();
            currentBold[selectedIndex]    = boldBtn.getSelection();
            currentItalic[selectedIndex]  = italicBtn.getSelection();
            currentUnder[selectedIndex]   = underlineBtn.getSelection();
            currentStrike[selectedIndex]  = strikeBtn.getSelection();
        }

        /** Populates the right panel from the in-memory arrays for the given index. */
        private void updatePanel(int idx) {
            if (idx < 0 || idx >= entries.size()) return;
            colorSelector.setColorValue(currentColors[idx]);
            boldBtn.setSelection(currentBold[idx]);
            italicBtn.setSelection(currentItalic[idx]);
            underlineBtn.setSelection(currentUnder[idx]);
            strikeBtn.setSelection(currentStrike[idx]);
        }
    }
}
