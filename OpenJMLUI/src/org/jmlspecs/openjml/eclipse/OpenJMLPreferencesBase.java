/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
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
        allEditors.forEach(FieldEditor::store);
        return true;
    }

    @Override
    protected void performDefaults() {
        allEditors.forEach(FieldEditor::loadDefault);
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

        addEditor(new StringFieldEditor(OpenJMLOptions.lspServerPathKey,
                "Server script path (blank = find on PATH or beside Eclipse):",
                parent));

        addSpace(parent);

        // ── Analysis triggers ───────────────────────────────────────────────
        addLabel(parent, "Analysis Triggers", SWT.SEPARATOR | SWT.HORIZONTAL);

        addEditor(new ComboFieldEditor(OpenJMLOptions.checkTriggerOnKey,
                "JML type-check trigger:",
                new String[][] {
                    { "On edit (instant feedback)", "edit" },
                    { "On save only",               "save" } },
                parent));

        addEditor(new ComboFieldEditor(OpenJMLOptions.escTriggerOnKey,
                "ESC (static checking) trigger:",
                new String[][] {
                    { "Manual only",          "manual" },
                    { "On save",              "save"   },
                    { "On edit (expensive)",  "edit"   } },
                parent));

        addSpace(parent);

        // ── Paths ───────────────────────────────────────────────────────────
        addLabel(parent, "Paths", SWT.SEPARATOR | SWT.HORIZONTAL);

        addEditor(new StringFieldEditor(OpenJMLOptions.propertiesFileKey,
                "openjml.properties file (blank = auto-discover):",
                parent));
        addEditor(new StringFieldEditor(OpenJMLOptions.specsPathKey,
                "Specs path (blank = default from launcher):",
                parent));
        addEditor(new StringFieldEditor(OpenJMLOptions.solversPathKey,
                "Solvers path (blank = default from launcher):",
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
                    { "subprocess (separate process, default)", "subprocess" },
                    { "concurrent (in-process, shared IAPI)",  "concurrent" },
                    { "fresh (in-process, fresh IAPI per method)", "fresh"  } },
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
                    { "quiet",    "0" },
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
                    { "safe",   "safe"   },
                    { "java",   "java"   },
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
                "Warning keys to enable/disable, comma-separated (--warn):",
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

        addEditor(new StringFieldEditor(OpenJMLOptions.timeoutKey,
                "Proof timeout in seconds (--timeout; blank = infinite):",
                parent));

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
}
