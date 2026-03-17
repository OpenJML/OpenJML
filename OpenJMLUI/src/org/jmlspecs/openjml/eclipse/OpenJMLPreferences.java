/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.eclipse.widgets.LabelFieldEditor;

/**
 * Eclipse preferences page for OpenJML LSP settings.
 *
 * <p>Depends only on {@link OpenJMLOptions} (plain string key constants) and
 * standard Eclipse JFace APIs — no dependency on legacy OpenJML classes
 * (JmlOption, Strings, etc.) — so this page always loads in a PDE runtime
 * workbench even when the old OpenJML JARs are absent.
 */
public class OpenJMLPreferences extends FieldEditorPreferencePage
        implements IWorkbenchPreferencePage {

    public OpenJMLPreferences() {
        super(FLAT);
    }

    @Override
    public void init(IWorkbench workbench) {
        setPreferenceStore(org.openjml.ui.Activator.getDefault().getPreferenceStore());
    }

    @Override
    protected void createFieldEditors() {

        // ── LSP Server ──────────────────────────────────────────────────────
        addLabel("LSP Server", SWT.SEPARATOR | SWT.HORIZONTAL);

        addField(new StringFieldEditor(OpenJMLOptions.lspServerPathKey,
                "Server script path (blank = find on PATH or beside Eclipse):",
                getFieldEditorParent()));

        addSpace();

        // ── Analysis triggers ───────────────────────────────────────────────
        addLabel("Analysis Triggers", SWT.SEPARATOR | SWT.HORIZONTAL);

        addField(new ComboFieldEditor(OpenJMLOptions.checkTriggerOnKey,
                "JML type-check trigger:",
                new String[][] {
                    { "On edit (instant feedback)", "edit" },
                    { "On save only",               "save" } },
                getFieldEditorParent()));

        addField(new ComboFieldEditor(OpenJMLOptions.escTriggerOnKey,
                "ESC (static checking) trigger:",
                new String[][] {
                    { "Manual only",          "manual" },
                    { "On save",              "save"   },
                    { "On edit (expensive)",  "edit"   } },
                getFieldEditorParent()));

        addSpace();

        // ── Paths ───────────────────────────────────────────────────────────
        addLabel("Paths", SWT.SEPARATOR | SWT.HORIZONTAL);

        addField(new StringFieldEditor(OpenJMLOptions.propertiesFileKey,
                "openjml.properties file (blank = auto-discover):",
                getFieldEditorParent()));
        addField(new StringFieldEditor(OpenJMLOptions.specsPathKey,
                "Specs path (blank = default from launcher):",
                getFieldEditorParent()));
        addField(new StringFieldEditor(OpenJMLOptions.solversPathKey,
                "Solvers path (blank = default from launcher):",
                getFieldEditorParent()));
        addField(new StringFieldEditor(OpenJMLOptions.sourcePathKey,
                "Source path for -sourcepath (blank = single-file):",
                getFieldEditorParent()));
        addField(new StringFieldEditor(OpenJMLOptions.classPathKey,
                "Classpath for -classpath (blank = none):",
                getFieldEditorParent()));

        addSpace();

        // ── ESC engine ──────────────────────────────────────────────────────
        addLabel("ESC Engine", SWT.SEPARATOR | SWT.HORIZONTAL);

        addField(new ComboFieldEditor(OpenJMLOptions.escEngineKey,
                "ESC engine:",
                new String[][] {
                    { "subprocess (separate process, default)", "subprocess" },
                    { "concurrent (in-process, shared IAPI)",  "concurrent" },
                    { "fresh (in-process, fresh IAPI per method)", "fresh"  } },
                getFieldEditorParent()));

        addField(new StringFieldEditor(OpenJMLOptions.escThreadsKey,
                "ESC parallel threads (0 = server default):",
                getFieldEditorParent()));

        addSpace();

        // ── RAC / Outline ───────────────────────────────────────────────────
        addLabel("RAC and Outline", SWT.SEPARATOR | SWT.HORIZONTAL);

        addField(new StringFieldEditor(OpenJMLOptions.racOutputDirKey,
                "RAC output directory (blank = project output):",
                getFieldEditorParent()));

        addField(new BooleanFieldEditor(OpenJMLOptions.useIntegratedOutlineKey,
                "Use integrated JML outline (uncheck for full Java+JML outline)",
                getFieldEditorParent()));
    }

    private void addLabel(String text, int swtOptions) {
        addField(new LabelFieldEditor("zzzzz.lsp.label", text, swtOptions,
                getFieldEditorParent()));
    }

    private void addSpace() {
        addField(new LabelFieldEditor("zzzzz.lsp.space", "", SWT.NONE,
                getFieldEditorParent()));
    }
}
