/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.preference.IPreferenceStore;

/**
 * Preference keys and defaults for the LSP-based OpenJML integration.
 *
 * <p>All keys are plain string literals — no dependency on OpenJML classes
 * (JmlOption, Strings, etc.) — so this class always loads successfully in a
 * PDE runtime workbench even when the legacy OpenJML JARs are absent.
 *
 * <p>Mirror of the settings in the VS Code {@code package.json} / OpenJMLSettings.
 */
public class OpenJMLOptions {

    // -----------------------------------------------------------------------
    // Key constants
    // -----------------------------------------------------------------------

    /** Path to the openjml-lsp launcher script. */
    public static final String lspServerPathKey        = "openjml.lspServerPath";

    /** When to run --check: "edit" (default) or "save". */
    public static final String checkTriggerOnKey       = "openjml.checkTriggerOn";
    /** When to run --esc: "manual" (default), "save", or "edit". */
    public static final String escTriggerOnKey         = "openjml.escTriggerOn";

    /** Path to openjml.properties (blank = auto-discover at workspace root). */
    public static final String propertiesFileKey       = "openjml.propertiesFile";
    /** Path to OpenJML specs directory (blank = use launcher default). */
    public static final String specsPathKey            = "openjml.specsPath";
    /** Path to SMT solvers directory (blank = use launcher default). */
    public static final String solversPathKey          = "openjml.solversPath";
    /** Source root(s) for -sourcepath (blank = single-file mode). */
    public static final String sourcePathKey           = "openjml.sourcePath";
    /** Classpath for pre-compiled dependencies (blank = none). */
    public static final String classPathKey            = "openjml.classPath";

    /** ESC engine: "subprocess" (default), "concurrent", or "fresh". */
    public static final String escEngineKey            = "openjml.escEngine";
    /** Number of parallel ESC threads (0 = server default). */
    public static final String escThreadsKey           = "openjml.escThreads";

    /** Output directory for RAC-compiled classes (blank = project output). */
    public static final String racOutputDirKey         = "openjml.racOutputDir";

    /** Whether the outline shows JML-only items (true) or full Java+JML (false). */
    public static final String useIntegratedOutlineKey = "openjml.useIntegratedOutline";

    // -----------------------------------------------------------------------
    // Defaults
    // -----------------------------------------------------------------------

    /**
     * Register defaults in the preference store.  Call this early in
     * {@code Activator.start()} before any legacy OpenJML code runs.
     */
    public static void initializeDefaults(IPreferenceStore store) {
        store.setDefault(checkTriggerOnKey,       "edit");
        store.setDefault(escTriggerOnKey,         "manual");
        store.setDefault(escEngineKey,            "subprocess");
        store.setDefault(escThreadsKey,           "0");
        store.setDefault(useIntegratedOutlineKey, "true");
    }

    // -----------------------------------------------------------------------
    // Accessors
    // -----------------------------------------------------------------------

    public static String value(String key) {
        return org.openjml.ui.Activator.getDefault().getPreferenceStore().getString(key);
    }

    private static String nonBlank(String s, String fallback) {
        return (s == null || s.isBlank()) ? fallback : s;
    }

    /** Collect all LSP settings into a map suitable for initializationOptions. */
    public static java.util.Map<String, Object> buildInitializationOptions() {
        var opts = new java.util.LinkedHashMap<String, Object>();
        opts.put("checkTriggerOn",      nonBlank(value(checkTriggerOnKey),  "edit"));
        opts.put("escTriggerOn",        nonBlank(value(escTriggerOnKey),    "manual"));
        opts.put("specsPath",           value(specsPathKey));
        opts.put("sourcePath",          value(sourcePathKey));
        opts.put("classPath",           value(classPathKey));
        opts.put("solversPath",         value(solversPathKey));
        opts.put("propertiesFile",      value(propertiesFileKey));
        opts.put("racOutputDir",        value(racOutputDirKey));
        opts.put("escEngine",           nonBlank(value(escEngineKey), "subprocess"));
        opts.put("useIntegratedOutline",value(useIntegratedOutlineKey));
        String threads = value(escThreadsKey);
        if (threads != null && !threads.isBlank() && !threads.equals("0")) {
            try { opts.put("escThreads", Integer.parseInt(threads.trim())); }
            catch (NumberFormatException ignored) {}
        }
        return opts;
    }
}
