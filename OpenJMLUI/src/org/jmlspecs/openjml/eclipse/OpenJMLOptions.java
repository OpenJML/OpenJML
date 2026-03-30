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
    // Tool-option descriptor — links a preference key to an openjml flag
    // -----------------------------------------------------------------------

    /**
     * Describes one openjml tool option managed by the Tab 2 preference page.
     *
     * @param prefKey      Eclipse preference-store key, e.g. {@code "openjml.codeMath"}
     * @param openjmlFlag  openjml flag name with leading dashes, e.g. {@code "--code-math"}
     * @param defaultValue default value as a string, matching {@link #initializeDefaults}
     * @param isBoolean    {@code true} for boolean (no-arg) flags
     */
    public record ToolOption(String prefKey, String openjmlFlag,
                             String defaultValue, boolean isBoolean) {
        /**
         * Property-file key used by openjml's {@code --properties} mechanism:
         * {@code "org.openjml.option.<flag-name-without-leading-dashes>"}.
         */
        public String propertyFileKey() {
            return "org.openjml.option." + openjmlFlag.substring(2);
        }
    }

    /**
     * All Tab-2 tool options in declaration order.
     * Used to write the generated properties file and to build command-line args.
     * Maintaining this list keeps {@link #writePropertiesFile()} and
     * {@link #buildToolCommandLineArgs()} free of per-option switch/if logic.
     */
    public static final java.util.List<ToolOption> TOOL_OPTIONS = java.util.List.of(
        // ── JML ──────────────────────────────────────────────────────
        new ToolOption(nullableByDefaultKey,       "--nullable-by-default",        "false",      true),
        new ToolOption(langKey,                    "--lang",                        "openjml",    false),
        new ToolOption(showNotImplementedKey,      "--show-not-implemented",        "false",      true),
        new ToolOption(optionalKeysKey,            "--keys",                        "",           false),
        new ToolOption(verbosityKey,               "--verboseness",                 "1",          false),
        new ToolOption(checkAccessibleKey,         "--check-accessible",            "true",       true),
        new ToolOption(codeMathKey,                "--code-math",                   "safe",       false),
        new ToolOption(specMathKey,                "--spec-math",                   "bigint",     false),
        new ToolOption(arithmeticKey,              "--arithmetic-failure",          "soft",       false),
        new ToolOption(allowPureInSpecsKey,        "--allow-pure-in-specs",         "true",       true),
        new ToolOption(requireWhiteSpaceKey,       "--require-white-space",         "false",      true),
        new ToolOption(warnKey,                    "--warn",                        "",           false),
        // ── ESC ──────────────────────────────────────────────────────
        new ToolOption(escMaxWarningsKey,          "--esc-max-warnings",            "2147483647", false),
        new ToolOption(timeoutKey,                 "--timeout",                     "",           false),
        new ToolOption(feasibilityKey,             "--check-feasibility",           "none",       false),
        new ToolOption(traceKey,                   "--trace",                       "false",      true),
        new ToolOption(subexpressionsKey,          "--subexpressions",              "false",      true),
        new ToolOption(counterexampleKey,          "--counterexample",              "false",      true),
        new ToolOption(escBvKey,                   "--esc-bv",                      "auto",       false),
        new ToolOption(escTriggersKey,             "--triggers",                    "true",       true),
        new ToolOption(escWarningsPathKey,         "--esc-warnings-path",           "false",      true),
        new ToolOption(splitKey,                   "--split",                       "",           false),
        new ToolOption(solverSeedKey,              "--solver-seed",                 "0",          false),
        // ── RAC ──────────────────────────────────────────────────────
        new ToolOption(compileToJavaAssertKey,     "--rac-compile-to-java-assert",  "false",      true),
        new ToolOption(racCheckJavaFeaturesKey,    "--rac-java-checks",             "false",      true),
        new ToolOption(racCheckAssumptionsKey,     "--rac-check-assumptions",       "true",       true),
        new ToolOption(racPreconditionEntryKey,    "--rac-precondition-entry",      "false",      true),
        new ToolOption(racShowSourceKey,           "--rac-show-source",             "source",     false),
        new ToolOption(showNotExecutableKey,       "--show-not-executable",         "false",      true),
        new ToolOption(racMissingModelFieldRepKey, "--rac-missing-model-field-rep", "skip",       false)
    );

    // -----------------------------------------------------------------------
    // Internal policy flags
    // -----------------------------------------------------------------------

    /**
     * When {@code true} (default), Tab-2 options are communicated to the LSP
     * server via a generated {@code .properties} file passed as
     * {@code --properties}.  When {@code false}, options are passed as
     * individual command-line flags in a {@code toolArgs} list.
     */
    private static final boolean USE_PROPERTIES_FILE = true;

    /**
     * When {@code true} (default), only options whose current value differs
     * from the factory default are written / included.  When {@code false},
     * every option is always written regardless of its value.
     */
    private static final boolean ONLY_NON_DEFAULTS = true;

    // -----------------------------------------------------------------------
    // Generated properties file
    // -----------------------------------------------------------------------

    /** Path of the last successfully written generated properties file. */
    private static volatile java.nio.file.Path generatedPropertiesFilePath;

    /**
     * Returns the OS path of the last written generated preferences file, or
     * {@code null} if it has not been written yet.
     */
    public static String getGeneratedPropertiesFilePath() {
        java.nio.file.Path p = generatedPropertiesFilePath;
        return p != null ? p.toString() : null;
    }

    /** Returns the plugin's Eclipse state directory, falling back to a temp dir. */
    private static java.nio.file.Path stateDir() {
        try {
            org.eclipse.core.runtime.IPath loc =
                    org.openjml.ui.Activator.getDefault().getStateLocation();
            return java.nio.file.Paths.get(loc.toOSString());
        } catch (Exception e) {
            return java.nio.file.Paths.get(System.getProperty("java.io.tmpdir"),
                    "openjml-eclipse");
        }
    }

    /**
     * Writes the current Tab-2 preference values to a {@code .properties} file
     * in the plugin's state directory and caches the path.
     *
     * <p>The file is read by openjml via {@code --properties}, which maps each
     * {@code org.openjml.option.<flag>=<value>} entry to the corresponding
     * command-line flag.
     *
     * <p>Safe to call from any thread; returns the file path on success or
     * {@code null} on failure.
     *
     * <p>Boolean options that need to be <em>disabled</em> (current value
     * {@code "false"} but default is {@code "true"}) are skipped in properties-file
     * mode because openjml's properties reader cannot negate boolean flags.
     * Use {@code USE_PROPERTIES_FILE = false} (command-line mode) if reliable
     * negation of default-true booleans is required.
     */
    public static java.nio.file.Path writePropertiesFile() {
        org.eclipse.jface.preference.IPreferenceStore store;
        try {
            store = org.openjml.ui.Activator.getDefault().getPreferenceStore();
        } catch (Exception e) {
            return null; // activator not yet available
        }
        var props = new java.util.Properties();
        for (ToolOption opt : TOOL_OPTIONS) {
            String val = store.getString(opt.prefKey());
            if (val == null) val = "";
            if (ONLY_NON_DEFAULTS && opt.defaultValue().equals(val)) continue;
            if (opt.isBoolean()) {
                if ("true".equals(val)) {
                    props.setProperty(opt.propertyFileKey(), "true");
                }
                // "false" on a boolean cannot be reliably communicated via
                // the properties file (the reader always treats the entry as
                // enabling the flag), so we omit it here.
            } else if (!val.isBlank()) {
                props.setProperty(opt.propertyFileKey(), val);
            }
        }
        try {
            java.nio.file.Path dir = stateDir();
            java.nio.file.Files.createDirectories(dir);
            java.nio.file.Path file = dir.resolve("eclipse-preferences.properties");
            try (var os = java.nio.file.Files.newOutputStream(file)) {
                props.store(os, "Generated by OpenJML Eclipse plugin — do not edit manually");
            }
            generatedPropertiesFilePath = file;
            return file;
        } catch (Exception e) {
            Console.log("Failed to write preferences properties file: " + e);
            return null;
        }
    }

    /**
     * Builds a list of openjml command-line arguments from the current Tab-2
     * preference values.  Used when {@link #USE_PROPERTIES_FILE} is
     * {@code false}.
     *
     * <p>Only non-default values are included when {@link #ONLY_NON_DEFAULTS}
     * is {@code true}.  Boolean flags that need to be disabled are passed as
     * {@code --flag=false}, which openjml correctly interprets as a negation.
     */
    public static java.util.List<String> buildToolCommandLineArgs() {
        org.eclipse.jface.preference.IPreferenceStore store =
                org.openjml.ui.Activator.getDefault().getPreferenceStore();
        var args = new java.util.ArrayList<String>();
        for (ToolOption opt : TOOL_OPTIONS) {
            String val = store.getString(opt.prefKey());
            if (val == null) val = "";
            if (ONLY_NON_DEFAULTS && opt.defaultValue().equals(val)) continue;
            if (opt.isBoolean()) {
                if ("true".equals(val)) {
                    args.add(opt.openjmlFlag());
                } else if ("false".equals(val) && !"false".equals(opt.defaultValue())) {
                    // Explicitly disable a default-true boolean flag
                    args.add(opt.openjmlFlag() + "=false");
                }
            } else if (!val.isBlank()) {
                args.add(opt.openjmlFlag());
                args.add(val);
            }
        }
        return args;
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

    /**
     * Collects all settings into a map suitable for LSP
     * {@code initializationOptions} / {@code workspace/didChangeConfiguration}.
     *
     * <p>Tab-1 (plugin/LSP) settings are always sent individually.
     * Tab-2 (tool) options are communicated either as a path to a generated
     * {@code .properties} file ({@link #USE_PROPERTIES_FILE}{@code = true}) or
     * as a flat {@code toolArgs} list of command-line flags
     * ({@link #USE_PROPERTIES_FILE}{@code = false}).
     */
    public static java.util.Map<String, Object> buildInitializationOptions() {
        var opts = new java.util.LinkedHashMap<String, Object>();

        // Tab 1 — plugin / LSP settings (always sent individually)
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

        // Tab 2 — tool options communicated via properties file or args list
        if (USE_PROPERTIES_FILE) {
            java.nio.file.Path propsFile = writePropertiesFile();
            if (propsFile != null) {
                opts.put("generatedPropertiesFile", propsFile.toString());
            }
        } else {
            opts.put("toolArgs", buildToolCommandLineArgs());
        }

        return opts;
    }
}
