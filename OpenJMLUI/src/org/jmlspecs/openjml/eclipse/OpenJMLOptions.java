/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.RGB;

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
    /** When to run --esc: "manual" (default) or "save". */
    public static final String escTriggerOnKey         = "openjml.escTriggerOn";
    /**
     * How ESC behaves when there are dirty (unsaved) editors:
     * "ask" (default) — show a dialog each time,
     * "content" — always run ESC on edited content without asking,
     * "save" — always save first, then run ESC on saved files.
     */
    public static final String escDirtyFilesBehaviorKey = "openjml.escDirtyFilesBehavior";

    /** Path to openjml.properties (blank = auto-discover at workspace root). */
    public static final String propertiesFileKey       = "openjml.propertiesFile";
    /** Path to OpenJML specs directory (blank = use launcher default). */
    public static final String specsPathKey            = "openjml.specsPath";

    /** Source root(s) for -sourcepath (blank = single-file mode). */
    public static final String sourcePathKey           = "openjml.sourcePath";
    /** Classpath for pre-compiled dependencies (blank = none). */
    public static final String classPathKey            = "openjml.classPath";

    /** ESC engine: "fresh" (default) or "concurrent". */
    public static final String escEngineKey            = "openjml.escEngine";
    /** Number of parallel ESC threads (0 = server default). */
    public static final String escThreadsKey           = "openjml.escThreads";

    /** Output directory for RAC-compiled classes (blank = project output). */
    public static final String racOutputDirKey         = "openjml.racOutputDir";
    /**
     * When {@code true}, edited (unsaved) files are saved automatically before
     * RAC without prompting.  When {@code false} (default), a dialog asks the
     * user to save or cancel.
     */
    public static final String racSaveBeforeKey        = "openjml.racSaveBefore";

    /** Whether the outline shows JML-only items (true) or full Java+JML (false). */
    public static final String useIntegratedOutlineKey = "openjml.useIntegratedOutline";

    /** Syntax coloring strategy: "ast" (default) or "regex". */
    public static final String syntaxColoringStrategyKey = "openjml.syntaxColoringStrategy";

    /** Syntax coloring scope: "preserve Java coloring" (default) or "overwrite Java coloring". */
    public static final String syntaxColoringScopeKey = "openjml.syntaxColoringScope";

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
    /** Warning keys to enable, comma-separated (--warn). */
    public static final String warnKey                 = "openjml.warn";
    /** Warning keys to disable, comma-separated (--no-warn). */
    public static final String noWarnKey               = "openjml.noWarn";

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
    // Syntax color token-type descriptors (Tab 2 — Syntax Colors)
    // -----------------------------------------------------------------------

    /**
     * One colorable JML semantic token type.
     *
     * <p>Defaults are close to Eclipse's Java editor theme:
     * keywords purple+bold, backslash tokens green+bold,
     * string literals blue, everything else black.
     *
     * @param id             legend token-type id (matches SemanticTokensProvider)
     * @param label          human-readable label for the preference UI
     * @param r g b          default RGB color components
     * @param bold           default bold
     * @param italic         default italic
     * @param underline      default underline
     * @param strikethrough  default strikethrough
     */
    public record TokenColorEntry(
            String id, String label,
            int r, int g, int b,
            boolean bold, boolean italic, boolean underline, boolean strikethrough) {

        public RGB    defaultRgb()        { return new RGB(r, g, b); }
        public String colorKey()          { return "openjml.color." + id; }
        public String boldKey()           { return "openjml.color." + id + ".bold"; }
        public String italicKey()         { return "openjml.color." + id + ".italic"; }
        public String underlineKey()      { return "openjml.color." + id + ".underline"; }
        public String strikethroughKey()  { return "openjml.color." + id + ".strikethrough"; }

        /** Returns the default TextAttribute style bitmask. */
        public int defaultStyle() {
            int s = SWT.NORMAL;
            if (bold)          s |= SWT.BOLD;
            if (italic)        s |= SWT.ITALIC;
            if (underline)     s |= org.eclipse.jface.text.TextAttribute.UNDERLINE;
            if (strikethrough) s |= org.eclipse.jface.text.TextAttribute.STRIKETHROUGH;
            return s;
        }
    }

    /**
     * The 19 active JML semantic token types in display order.
     * (Types "macro" and "comment" are declared in the legend but never emitted.)
     */
    public static final java.util.List<TokenColorEntry> TOKEN_COLORS = java.util.List.of(
        //                id            label                                       r    g    b  bo  it  ul  st
        new TokenColorEntry("keyword",       "JML keyword (requires, ensures, …)",  127,  0,  85, true,  false, false, false),
        new TokenColorEntry("modifier",      "JML modifier (pure, spec_public, …)", 127,  0,  85, false, false, false, false),
        new TokenColorEntry("function",      "Backslash token (\\result, \\old, …)",  63, 127,  95, true,  false, false, false),
        new TokenColorEntry("type",          "Type (generic)",                         0,   0,   0, false, false, false, false),
        new TokenColorEntry("class",         "Class name",                             0,   0,   0, false, false, false, false),
        new TokenColorEntry("interface",     "Interface name",                         0,   0,   0, false, false, false, false),
        new TokenColorEntry("enum",          "Enum name",                              0,   0,   0, false, false, false, false),
        new TokenColorEntry("struct",        "Struct name",                            0,   0,   0, false, false, false, false),
        new TokenColorEntry("typeParameter", "Type parameter",                         0,   0,   0, false, false, false, false),
        new TokenColorEntry("namespace",     "Namespace / package",                    0,   0, 128, false, false, false, false),
        new TokenColorEntry("enumMember",    "Enum member",                            0,   0,   0, false, false, false, false),
        new TokenColorEntry("method",        "Method name",                            0,   0,   0, false, false, false, false),
        new TokenColorEntry("parameter",     "Parameter name",                         0,   0,   0, false, false, false, false),
        new TokenColorEntry("variable",      "Variable name",                          0,   0,   0, false, false, false, false),
        new TokenColorEntry("property",      "Field name",                             0,   0,   0, false, false, false, false),
        new TokenColorEntry("macro",         "Macro",                                  0,   0,   0, false, false, false, false),
        new TokenColorEntry("decorator",     "Decorator",                            100, 100, 100, false, false, false, false),
        new TokenColorEntry("comment",       "Comment",                              128, 128, 128, false, false, false, false),
        new TokenColorEntry("string",        "String literal",                         42,   0, 255, false, false, false, false),
        new TokenColorEntry("number",        "Number literal",                         25,   0, 134, false, false, false, false),
        new TokenColorEntry("operator",      "Operator",                               0,   0,   0, false, false, false, false)
    );

    /** Returns the stored RGB for a token type, reading from the given preference store. */
    public static RGB getTokenColor(IPreferenceStore store, TokenColorEntry e) {
        return PreferenceConverter.getColor(store, e.colorKey());
    }

    /** Returns the stored style bitmask (SWT.BOLD | SWT.ITALIC | UNDERLINE | STRIKETHROUGH). */
    public static int getTokenStyle(IPreferenceStore store, TokenColorEntry e) {
        int s = SWT.NORMAL;
        if (store.getBoolean(e.boldKey()))          s |= SWT.BOLD;
        if (store.getBoolean(e.italicKey()))        s |= SWT.ITALIC;
        if (store.getBoolean(e.underlineKey()))     s |= org.eclipse.jface.text.TextAttribute.UNDERLINE;
        if (store.getBoolean(e.strikethroughKey())) s |= org.eclipse.jface.text.TextAttribute.STRIKETHROUGH;
        return s;
    }

    /**
     * Registers syntax-color defaults in the preference store.
     * Called from {@link #initializeDefaults}.
     */
    public static void initializeSyntaxColorDefaults(IPreferenceStore store) {
        for (TokenColorEntry e : TOKEN_COLORS) {
            PreferenceConverter.setDefault(store, e.colorKey(), e.defaultRgb());
            store.setDefault(e.boldKey(),          e.bold());
            store.setDefault(e.italicKey(),        e.italic());
            store.setDefault(e.underlineKey(),     e.underline());
            store.setDefault(e.strikethroughKey(), e.strikethrough());
        }
    }

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
        store.setDefault(escDirtyFilesBehaviorKey,    "ask");
        store.setDefault(racSaveBeforeKey,            false);
        store.setDefault(escEngineKey,                "fresh");
        store.setDefault(escThreadsKey,               "0");
        store.setDefault(useIntegratedOutlineKey,     "true");
        store.setDefault(syntaxColoringStrategyKey,   "ast");
        store.setDefault(syntaxColoringScopeKey,      "preserve Java coloring");
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
        store.setDefault(noWarnKey,                   "");
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
        // Syntax color defaults (Tab 2 — Syntax Colors)
        initializeSyntaxColorDefaults(store);
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
        new ToolOption(noWarnKey,                  "--no-warn",                     "",           false),
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

    private static final boolean USE_PROPERTIES_FILE = true; // kept for writePropertiesFile / buildToolCommandLineArgs

    /**
     * Strips all whitespace around commas in a comma-separated list value.
     * For example, {@code "a, b , c"} becomes {@code "a,b,c"}.
     * Returns the value unchanged if it contains no commas.
     */
    private static String stripCommaSpaces(String val) {
        if (val == null || !val.contains(",")) return val;
        return val.replaceAll("\\s*,\\s*", ",").trim();
    }

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
            // Verboseness=0 (quiet) suppresses ESC diagnostics; clamp to minimum 1.
            if (opt.prefKey().equals(verbosityKey) && "0".equals(val)) val = "1";
            // Strip embedded whitespace from comma-separated list options.
            if (opt.prefKey().equals(warnKey) || opt.prefKey().equals(noWarnKey))
                val = stripCommaSpaces(val);
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
            // Strip embedded whitespace from comma-separated list options.
            if (opt.prefKey().equals(warnKey) || opt.prefKey().equals(noWarnKey))
                val = stripCommaSpaces(val);
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
     *
     * <p>Per-project paths (sourcePath, classPath, specsPath, propertiesFile,
     * rootPaths, javaOutputDir, racOutputDir) are now sent inside the {@code projects} list
     * rather than as global top-level fields.  Commands from the Eclipse plugin
     * carry only a {@code projectId}; the server looks up the settings.
     */
    public static java.util.Map<String, Object> buildInitializationOptions() {
        var opts = new java.util.LinkedHashMap<String, Object>();

        // Client identification — always sent so the server applies correct defaults.
        opts.put("client", "eclipse-jdt");
        opts.put("genericMode", false);  // Eclipse pre-assembles paths; server must not overwrite them

        // Tab 1 — plugin / LSP settings (always sent individually)
        opts.put("checkTriggerOn",         nonBlank(value(checkTriggerOnKey),  "edit"));
        opts.put("escTriggerOn",           nonBlank(value(escTriggerOnKey),    "manual"));
        opts.put("specsPath",              value(specsPathKey));

        opts.put("escEngine",              nonBlank(value(escEngineKey), "fresh"));
        opts.put("useIntegratedOutline",   value(useIntegratedOutlineKey));
        opts.put("syntaxColoringStrategy", nonBlank(value(syntaxColoringStrategyKey), "ast"));
        opts.put("syntaxColoringScope",    nonBlank(value(syntaxColoringScopeKey), "preserve Java coloring"));
        String threads = value(escThreadsKey);
        if (threads != null && !threads.isBlank() && !threads.equals("0")) {
            try { opts.put("escThreads", Integer.parseInt(threads.trim())); }
            catch (NumberFormatException ignored) {}
        }

        // Tab 2 — tool options sent as a toolOptions array: ["--properties", "<file>"].
        // This is project-independent; per-project path fields are in the projects list.
        java.nio.file.Path propsFile = writePropertiesFile();
        if (propsFile != null) {
            opts.put("toolOptions",
                    java.util.List.of("--properties", propsFile.toString()));
        }

        // Per-project configs — sourcePath, classPath, specsPath, rootPaths, outputDir.
        java.util.List<java.util.Map<String, Object>> projects = buildProjectsList();
        if (!projects.isEmpty()) opts.put("projects", projects);

        return opts;
    }

    /**
     * Returns a path-separator-separated string of JDT source-folder filesystem
     * paths for all open Eclipse projects that carry the JML nature.
     *
     * @deprecated Use {@link #buildProjectsList} instead.  This method is kept
     *             only for backward compatibility with older code paths that have
     *             not yet been converted to the per-project config protocol.
     */
    @Deprecated
    public static String buildJmlProjectRoots() {
        java.util.List<String> parts = new java.util.ArrayList<>();
        for (IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
            if (!project.isOpen() || !JmlNature.hasNature(project)) continue;
            org.eclipse.jdt.core.IJavaProject jp =
                    org.eclipse.jdt.core.JavaCore.create(project);
            boolean addedSrcFolder = false;
            if (jp != null && jp.exists()) {
                try {
                    for (org.eclipse.jdt.core.IPackageFragmentRoot pfr
                            : jp.getPackageFragmentRoots()) {
                        if (pfr.getKind() != org.eclipse.jdt.core.IPackageFragmentRoot.K_SOURCE)
                            continue;
                        org.eclipse.core.resources.IResource res =
                                pfr.getCorrespondingResource();
                        org.eclipse.core.runtime.IPath loc =
                                res != null ? res.getLocation() : pfr.getPath();
                        if (loc != null) {
                            parts.add(loc.toOSString());
                            addedSrcFolder = true;
                        }
                    }
                } catch (Exception ignored) {}
            }
            if (!addedSrcFolder && project.getLocation() != null) {
                parts.add(project.getLocation().toOSString());
            }
        }
        return String.join(java.io.File.pathSeparator, parts);
    }

    /**
     * Builds a per-project config list for the LSP {@code projects} field.
     *
     * <p>Each entry is a {@code Map<String, Object>} with the following fields:
     * <ul>
     *   <li>{@code id} — Eclipse {@code IProject.getName()}, the server's registry key</li>
     *   <li>{@code sourcePath} — this project's own source folders + transitive dep sources,
     *       path-separator-separated; passed as {@code -sourcepath}</li>
     *   <li>{@code classPath} — JAR libraries (Maven deps, external JARs) + transitive
     *       dep output dirs + user classpath pref + racOutputDir pref,
     *       path-separator-separated; passed as {@code -classpath}</li>
     *   <li>{@code specsPath} — global specs path preference</li>
     *   <li>{@code javaOutputDir} — JDT output folder; goes on classpath and serves as
     *       default RAC {@code -d} when {@code racOutputDir} is empty</li>
     *   <li>{@code racOutputDir} — user {@code openjml.racOutputDir} preference for RAC
     *       {@code -d}; absent when empty (server falls back to {@code javaOutputDir})</li>
     *   <li>{@code rootPaths} — this project's own source folders only (not deps),
     *       as a {@code List<String>}; used by the server for URI→project lookup</li>
     * </ul>
     */
    public static java.util.List<java.util.Map<String, Object>> buildProjectsList() {
        var result = new java.util.ArrayList<java.util.Map<String, Object>>();

        String globalSpecsPath = value(specsPathKey);

        org.eclipse.core.resources.IWorkspaceRoot wsRoot =
                ResourcesPlugin.getWorkspace().getRoot();

        for (IProject project : wsRoot.getProjects()) {
            if (!project.isOpen()) continue;
            org.eclipse.jdt.core.IJavaProject jp =
                    org.eclipse.jdt.core.JavaCore.create(project);
            if (jp == null || !jp.exists()) continue;

            // --- own source folders (for rootPaths) ---
            var ownSrcFolders = new java.util.ArrayList<String>();
            try {
                for (org.eclipse.jdt.core.IPackageFragmentRoot pfr
                        : jp.getPackageFragmentRoots()) {
                    if (pfr.getKind() != org.eclipse.jdt.core.IPackageFragmentRoot.K_SOURCE)
                        continue;
                    org.eclipse.core.resources.IResource res = pfr.getCorrespondingResource();
                    org.eclipse.core.runtime.IPath loc =
                            res != null ? res.getLocation() : pfr.getPath();
                    if (loc != null) ownSrcFolders.add(loc.toOSString());
                }
            } catch (Exception ignored) {}

            // --- all source folders (own + dep) and dep output dirs ---
            var allSrcParts = new java.util.ArrayList<String>();
            var cpParts     = new java.util.ArrayList<String>();

            // User sourcepath additions go first.
            String prefSrc = value(sourcePathKey);
            if (prefSrc != null && !prefSrc.isBlank()) allSrcParts.add(prefSrc);

            // User classpath goes first (highest priority on the path).
            // Raw string is passed; the server expands $VAR tokens uniformly.
            String prefCp = value(classPathKey);
            if (prefCp != null && !prefCp.isBlank()) cpParts.add(prefCp);

            // User racOutputDir also goes on the classpath so already-RAC-compiled classes
            // are visible to subsequent compilations.
            String prefRacOut = value(racOutputDirKey);
            if (prefRacOut != null && !prefRacOut.isBlank()) cpParts.add(prefRacOut);

            try {
                collectJdtPaths(jp, allSrcParts, cpParts, new java.util.HashSet<>(), jreHomeFor(jp));
            } catch (Exception e) {
                Console.log("buildProjectsList: collectJdtPaths failed for "
                        + project.getName() + ": " + e);
            }

            // --- outputDir (for RAC -d) ---
            String outputDir = null;
            try {
                org.eclipse.core.runtime.IPath outPath = jp.getOutputLocation();
                org.eclipse.core.resources.IFolder outFolder = wsRoot.getFolder(outPath);
                org.eclipse.core.runtime.IPath outLoc = outFolder.getLocation();
                if (outLoc != null) outputDir = outLoc.toOSString();
            } catch (Exception ignored) {}

            var cfg = new java.util.LinkedHashMap<String, Object>();
            cfg.put("id",         project.getName());
            cfg.put("sourcePath", String.join(java.io.File.pathSeparator, allSrcParts));
            cfg.put("classPath",  String.join(java.io.File.pathSeparator, cpParts));
            if (globalSpecsPath != null && !globalSpecsPath.isBlank())
                cfg.put("specsPath", globalSpecsPath);
            if (outputDir != null)
                cfg.put("javaOutputDir", outputDir);
            String racOutPref = value(racOutputDirKey);
            if (racOutPref != null && !racOutPref.isBlank()) cfg.put("racOutputDir", racOutPref);
            cfg.put("rootPaths", ownSrcFolders.isEmpty()
                    ? (project.getLocation() != null
                            ? java.util.List.of(project.getLocation().toOSString())
                            : java.util.List.of())
                    : ownSrcFolders);
            result.add(cfg);
        }
        return result;
    }

    /**
     * Returns the OS path prefix of the JVM install used by the given project,
     * or {@code null} if it cannot be determined.  Used to exclude JRE system
     * library JARs from the classpath sent to OpenJML, which ships its own JDK.
     *
     * <p><b>Limitation:</b> if the Eclipse project targets a different Java version
     * than OpenJML's bundled JDK, there may be class-version or API conflicts.
     * The OpenJML JDK version takes precedence at runtime.
     */
    static String jreHomeFor(org.eclipse.jdt.core.IJavaProject jp) {
        // Use getVMInstall(IPath) via the JRE container entry — avoids the
        // getVMInstall(IJavaProject) overload which is not available in all Eclipse versions.
        try {
            for (org.eclipse.jdt.core.IClasspathEntry e : jp.getRawClasspath()) {
                if (e.getEntryKind() == org.eclipse.jdt.core.IClasspathEntry.CPE_CONTAINER) {
                    org.eclipse.core.runtime.IPath p = e.getPath();
                    if (p.segmentCount() > 0 && org.eclipse.jdt.launching.JavaRuntime.JRE_CONTAINER
                            .equals(p.segment(0))) {
                        org.eclipse.jdt.launching.IVMInstall vm =
                                org.eclipse.jdt.launching.JavaRuntime.getVMInstall(p);
                        if (vm != null && vm.getInstallLocation() != null)
                            return vm.getInstallLocation().getAbsolutePath();
                    }
                }
            }
        } catch (Exception ignored) {}
        // Fall back to the workspace default JVM.
        try {
            org.eclipse.jdt.launching.IVMInstall vm =
                    org.eclipse.jdt.launching.JavaRuntime.getDefaultVMInstall();
            if (vm != null && vm.getInstallLocation() != null)
                return vm.getInstallLocation().getAbsolutePath();
        } catch (Exception ignored) {}
        return null;
    }

    /**
     * Recursively collects source folders into {@code srcParts} and dependency
     * output directories and JAR files into {@code cpParts} for {@code jp}.
     *
     * <p>JRE system library JARs are excluded because OpenJML ships its own
     * bundled JDK and must not have a conflicting JRE on its classpath.
     * {@code jreHome} is the install-location prefix used to detect JRE JARs;
     * {@code null} disables the filter (no JARs are excluded).
     */
    static void collectJdtPaths(
            org.eclipse.jdt.core.IJavaProject jp,
            java.util.List<String> srcParts,
            java.util.List<String> cpParts,
            java.util.Set<String> visited,
            String jreHome) throws Exception {

        if (!visited.add(jp.getProject().getName())) return;

        org.eclipse.core.resources.IWorkspaceRoot root =
                ResourcesPlugin.getWorkspace().getRoot();

        // This project's own source folders.
        for (org.eclipse.jdt.core.IPackageFragmentRoot pfr : jp.getPackageFragmentRoots()) {
            if (pfr.getKind() != org.eclipse.jdt.core.IPackageFragmentRoot.K_SOURCE) continue;
            org.eclipse.core.resources.IResource res = pfr.getCorrespondingResource();
            org.eclipse.core.runtime.IPath loc =
                    res != null ? res.getLocation() : pfr.getPath();
            if (loc != null) srcParts.add(loc.toOSString());
        }

        // Walk the resolved classpath: collect JAR libraries and recurse into projects.
        // getResolvedClasspath(true) has already expanded containers (JRE, Maven, etc.)
        // so every CPE_LIBRARY entry is a concrete path.
        for (org.eclipse.jdt.core.IClasspathEntry entry
                : jp.getResolvedClasspath(/* ignoreUnresolvedEntry= */ true)) {

            if (entry.getEntryKind() == org.eclipse.jdt.core.IClasspathEntry.CPE_LIBRARY) {
                org.eclipse.core.runtime.IPath p = entry.getPath();
                if (!p.isAbsolute()) {
                    // Workspace-relative path (JAR inside the workspace).
                    org.eclipse.core.resources.IResource r = root.findMember(p);
                    if (r != null) p = r.getLocation();
                }
                if (p == null) continue;
                // Skip JRE system library JARs — OpenJML uses its own bundled JDK.
                if (jreHome != null && p.toOSString().startsWith(jreHome)) continue;
                cpParts.add(p.toOSString());

            } else if (entry.getEntryKind() == org.eclipse.jdt.core.IClasspathEntry.CPE_PROJECT) {
                String depName = entry.getPath().lastSegment();
                org.eclipse.core.resources.IProject depProject = root.getProject(depName);
                org.eclipse.jdt.core.IJavaProject depJp =
                        org.eclipse.jdt.core.JavaCore.create(depProject);
                if (depJp == null || !depJp.exists()) continue;

                // Dependency output location → classpath.
                org.eclipse.core.runtime.IPath outputPath = depJp.getOutputLocation();
                org.eclipse.core.resources.IFolder outputFolder = root.getFolder(outputPath);
                org.eclipse.core.runtime.IPath outputLoc = outputFolder.getLocation();
                if (outputLoc != null) cpParts.add(outputLoc.toOSString());

                // Recurse so transitive dependency sources and JARs are included.
                collectJdtPaths(depJp, srcParts, cpParts, visited, jreHome);
            }
        }
    }
}
