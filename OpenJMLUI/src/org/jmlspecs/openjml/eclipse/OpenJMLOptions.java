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
    // Key constants — Tab 1: Plugin and LSP Settings
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

    /** Syntax coloring strategy: "ast" (default) or "regex". */
    public static final String syntaxColoringStrategyKey = "openjml.syntaxColoringStrategy";

    // -----------------------------------------------------------------------
    // Key constants — Tab 2: OpenJML Tool Options — JML section
    // -----------------------------------------------------------------------

    /** Makes all references nullable by default (--nullable-by-default). */
    public static final String nullableByDefaultKey    = "openjml.nullableByDefault";
    /** Language variant (--lang): "openjml" (default) or "jml5" (strict). */
    public static final String langKey                 = "openjml.lang";
    /** Warn about unimplemented constructs (--show-not-implemented). */
    public static final String showNotImplementedKey   = "openjml.showNotImplemented";
    /** Optional annotation keys, comma-separated (--keys). */
    public static final String optionalKeysKey         = "openjml.optionalKeys";
    /** Verbosity level (--verboseness): 0=quiet 1=normal 2=progress 3=verbose 4=debug. */
    public static final String verbosityKey            = "openjml.verboseness";
    /** Check accessible clauses (--check-accessible; default true). */
    public static final String checkAccessibleKey      = "openjml.checkAccessible";
    /** Arithmetic mode for Java code (--code-math): java/safe/bigint. */
    public static final String codeMathKey             = "openjml.codeMath";
    /** Arithmetic mode for specifications (--spec-math): java/safe/bigint. */
    public static final String specMathKey             = "openjml.specMath";
    /** Arithmetic warning severity (--arithmetic-failure): hard/soft/quiet. */
    public static final String arithmeticKey           = "openjml.arithmeticFailure";
    /** Allow pure methods in specifications (--allow-pure-in-specs; default true). */
    public static final String allowPureInSpecsKey     = "openjml.allowPureInSpecs";
    /** Require white space after @ in JML comment (--require-white-space; default false). */
    public static final String requireWhiteSpaceKey    = "openjml.requireWhiteSpace";
    /** Warning keys to enable/disable, comma-separated (--warn). */
    public static final String warnKey                 = "openjml.warn";

    // -----------------------------------------------------------------------
    // Key constants — Tab 2: OpenJML Tool Options — ESC section
    // -----------------------------------------------------------------------

    /** Maximum ESC warnings per method (--esc-max-warnings). */
    public static final String escMaxWarningsKey       = "openjml.escMaxWarnings";
    /** ESC proof attempt timeout in seconds (--timeout; blank = infinite). */
    public static final String timeoutKey              = "openjml.timeout";
    /** Feasibility checking (--check-feasibility): none/basics/all. */
    public static final String feasibilityKey          = "openjml.feasibility";
    /** Enable counterexample tracing (--trace). */
    public static final String traceKey                = "openjml.trace";
    /** Enable tracing with subexpressions (--subexpressions). */
    public static final String subexpressionsKey       = "openjml.subexpressions";
    /** Output complete raw counterexample (--counterexample). */
    public static final String counterexampleKey       = "openjml.counterexample";
    /** Bit-vector arithmetic (--esc-bv): auto/true/false. */
    public static final String escBvKey                = "openjml.escBv";
    /** Enable quantifier triggers in SMT encoding (--triggers; default true). */
    public static final String escTriggersKey          = "openjml.escTriggers";
    /** Find all counterexample paths to each invalid assert (--esc-warnings-path). */
    public static final String escWarningsPathKey      = "openjml.escWarningsPath";
    /** Split proof into sections (--split). */
    public static final String splitKey                = "openjml.split";
    /** Seed for solver RNG (--solver-seed; 0 = default). */
    public static final String solverSeedKey           = "openjml.solverSeed";

    // -----------------------------------------------------------------------
    // Key constants — Tab 2: OpenJML Tool Options — RAC section
    // -----------------------------------------------------------------------

    /** Compile JML checks as Java asserts (--rac-compile-to-java-assert). */
    public static final String compileToJavaAssertKey  = "openjml.racCompileToJavaAssert";
    /** Enable explicit checking of Java language features (--rac-java-checks). */
    public static final String racCheckJavaFeaturesKey = "openjml.racJavaChecks";
    /** Enable runtime checking that assumptions hold (--rac-check-assumptions). */
    public static final String racCheckAssumptionsKey  = "openjml.racCheckAssumptions";
    /** Distinguish entry vs. internal precondition failures (--rac-precondition-entry). */
    public static final String racPreconditionEntryKey = "openjml.racPreconditionEntry";
    /** Source information in RAC error messages (--rac-show-source): none/line/source. */
    public static final String racShowSourceKey        = "openjml.racShowSource";
    /** Warn about non-executable constructs (--show-not-executable). */
    public static final String showNotExecutableKey    = "openjml.showNotExecutable";
    /** Action when model field has no rep clause (--rac-missing-model-field-rep). */
    public static final String racMissingModelFieldRepKey = "openjml.racMissingModelFieldRep";

    // -----------------------------------------------------------------------
    // Defaults
    // -----------------------------------------------------------------------

    /**
     * Register defaults in the preference store.  Call this early in
     * {@code Activator.start()} before any legacy OpenJML code runs.
     */
    public static void initializeDefaults(IPreferenceStore store) {
        // Tab 1
        store.setDefault(checkTriggerOnKey,           "edit");
        store.setDefault(escTriggerOnKey,             "manual");
        store.setDefault(escEngineKey,                "subprocess");
        store.setDefault(escThreadsKey,               "0");
        store.setDefault(useIntegratedOutlineKey,     "true");
        store.setDefault(syntaxColoringStrategyKey,   "ast");
        // Tab 2 — JML
        store.setDefault(nullableByDefaultKey,        "false");
        store.setDefault(langKey,                     "openjml");
        store.setDefault(showNotImplementedKey,       "false");
        store.setDefault(optionalKeysKey,             "");
        store.setDefault(verbosityKey,                "1");
        store.setDefault(checkAccessibleKey,          "true");
        store.setDefault(codeMathKey,                 "safe");
        store.setDefault(specMathKey,                 "bigint");
        store.setDefault(arithmeticKey,               "soft");
        store.setDefault(allowPureInSpecsKey,         "true");
        store.setDefault(requireWhiteSpaceKey,        "false");
        store.setDefault(warnKey,                     "");
        // Tab 2 — ESC
        store.setDefault(escMaxWarningsKey,           "2147483647");
        store.setDefault(timeoutKey,                  "");
        store.setDefault(feasibilityKey,              "none");
        store.setDefault(traceKey,                    "false");
        store.setDefault(subexpressionsKey,           "false");
        store.setDefault(counterexampleKey,           "false");
        store.setDefault(escBvKey,                    "auto");
        store.setDefault(escTriggersKey,              "true");
        store.setDefault(escWarningsPathKey,          "false");
        store.setDefault(splitKey,                    "");
        store.setDefault(solverSeedKey,               "0");
        // Tab 2 — RAC
        store.setDefault(compileToJavaAssertKey,      "false");
        store.setDefault(racCheckJavaFeaturesKey,     "false");
        store.setDefault(racCheckAssumptionsKey,      "true");
        store.setDefault(racPreconditionEntryKey,     "false");
        store.setDefault(racShowSourceKey,            "source");
        store.setDefault(showNotExecutableKey,        "false");
        store.setDefault(racMissingModelFieldRepKey,  "skip");
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

    /** Collect all settings into a map suitable for LSP initializationOptions. */
    public static java.util.Map<String, Object> buildInitializationOptions() {
        var opts = new java.util.LinkedHashMap<String, Object>();

        // Tab 1 — plugin / LSP settings
        opts.put("checkTriggerOn",         nonBlank(value(checkTriggerOnKey),  "edit"));
        opts.put("escTriggerOn",           nonBlank(value(escTriggerOnKey),    "manual"));
        opts.put("specsPath",              value(specsPathKey));
        opts.put("sourcePath",             value(sourcePathKey));
        opts.put("classPath",              value(classPathKey));
        opts.put("solversPath",            value(solversPathKey));
        opts.put("propertiesFile",         value(propertiesFileKey));
        opts.put("racOutputDir",           value(racOutputDirKey));
        opts.put("escEngine",              nonBlank(value(escEngineKey), "subprocess"));
        opts.put("useIntegratedOutline",   value(useIntegratedOutlineKey));
        opts.put("syntaxColoringStrategy", nonBlank(value(syntaxColoringStrategyKey), "ast"));
        String threads = value(escThreadsKey);
        if (threads != null && !threads.isBlank() && !threads.equals("0")) {
            try { opts.put("escThreads", Integer.parseInt(threads.trim())); }
            catch (NumberFormatException ignored) {}
        }

        // Tab 2 — JML tool options
        opts.put("nullableByDefault",      value(nullableByDefaultKey));
        opts.put("lang",                   nonBlank(value(langKey), "openjml"));
        opts.put("showNotImplemented",     value(showNotImplementedKey));
        opts.put("optionalKeys",           value(optionalKeysKey));
        opts.put("verboseness",            nonBlank(value(verbosityKey), "1"));
        opts.put("checkAccessible",        value(checkAccessibleKey));
        opts.put("codeMath",               nonBlank(value(codeMathKey), "safe"));
        opts.put("specMath",               nonBlank(value(specMathKey), "bigint"));
        opts.put("arithmeticFailure",      nonBlank(value(arithmeticKey), "soft"));
        opts.put("allowPureInSpecs",       value(allowPureInSpecsKey));
        opts.put("requireWhiteSpace",      value(requireWhiteSpaceKey));
        String warn = value(warnKey);
        if (warn != null && !warn.isBlank()) opts.put("warn", warn);

        // Tab 2 — ESC tool options
        opts.put("escMaxWarnings",         nonBlank(value(escMaxWarningsKey), "2147483647"));
        String timeout = value(timeoutKey);
        if (timeout != null && !timeout.isBlank()) opts.put("timeout", timeout);
        opts.put("feasibility",            nonBlank(value(feasibilityKey), "none"));
        opts.put("trace",                  value(traceKey));
        opts.put("subexpressions",         value(subexpressionsKey));
        opts.put("counterexample",         value(counterexampleKey));
        opts.put("escBv",                  nonBlank(value(escBvKey), "auto"));
        opts.put("escTriggers",            value(escTriggersKey));
        opts.put("escWarningsPath",        value(escWarningsPathKey));
        String split = value(splitKey);
        if (split != null && !split.isBlank()) opts.put("split", split);
        String solverSeed = value(solverSeedKey);
        if (solverSeed != null && !solverSeed.isBlank() && !solverSeed.equals("0")) opts.put("solverSeed", solverSeed);

        // Tab 2 — RAC tool options
        opts.put("racCompileToJavaAssert", value(compileToJavaAssertKey));
        opts.put("racJavaChecks",          value(racCheckJavaFeaturesKey));
        opts.put("racCheckAssumptions",    value(racCheckAssumptionsKey));
        opts.put("racPreconditionEntry",   value(racPreconditionEntryKey));
        opts.put("racShowSource",          nonBlank(value(racShowSourceKey), "source"));
        opts.put("showNotExecutable",      value(showNotExecutableKey));
        opts.put("racMissingModelFieldRep", nonBlank(value(racMissingModelFieldRepKey), "skip"));

        return opts;
    }
}
