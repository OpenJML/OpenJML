package org.openjml.lsp;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Runtime settings for the OpenJML language server.
 *
 * <p>This class is <strong>NOT</strong> a Gson deserialization target.
 * The Gson target is {@link ClientSettings}.  After the client sends a
 * settings payload, {@link OpenJMLWorkspaceService#applyUpdate} merges
 * non-null fields from the incoming {@link ClientSettings} into
 * {@link #clientSettings} and recomputes assembled paths.
 *
 * <p>Fields that are used verbatim from the client live only in
 * {@link #clientSettings}; helper methods here delegate to it.
 * Fields that require server-side computation (assembled paths,
 * per-project overrides) are stored directly on this class.
 *
 * <p>Volatile fields are readable on async check-executor threads without
 * additional synchronization.
 *
 * <p>The copy constructor creates a shallow snapshot for a single tool
 * invocation.  {@link #escPool} and {@link #clientSettings} are shared
 * (not copied) so the snapshot uses the same pool and sees the same
 * client-provided values as the global settings.
 */
public class OpenJMLSettings {

    /**
     * The project ID for the synthesized single-project entry created for
     * generic LSP clients (VS Code, bare LSP) that do not send an explicit
     * {@link ClientSettings#projects} list.
     */
    public static final String WORKSPACE_PROJECT_ID = "";

    // -----------------------------------------------------------------------
    // Per-project runtime state (set by server, not received from client)
    // -----------------------------------------------------------------------

    /**
     * Per-project configuration list, copied from
     * {@link ClientSettings#projects} by {@link OpenJMLWorkspaceService#applyUpdate}.
     */
    public volatile List<ProjectConfig> projects;

    /**
     * This instance's own project ID.  Set on <em>per-project</em> copies built
     * by {@link OpenJMLTextDocumentService#updateProjectSettings}; {@code ""}
     * (the {@link #WORKSPACE_PROJECT_ID} sentinel) on {@code globalSettings}.
     */
    public volatile String projectId = WORKSPACE_PROJECT_ID;

    /**
     * This instance's own source-folder roots.  Set on <em>per-project</em>
     * copies built by {@link OpenJMLTextDocumentService#updateProjectSettings};
     * never set on {@code globalSettings}.
     */
    public volatile List<String> rootPaths;

    // -----------------------------------------------------------------------
    // Assembled path settings (written by applyUpdate; read by CheckRunner)
    // For Eclipse clients these are env-var-expanded copies of the client values.
    // For VS Code/generic clients these are assembled from client values +
    // workspaceFolderPaths + javaOutputDir + racOutputDir.
    // -----------------------------------------------------------------------

    /** Assembled source path ({@code -sourcepath}), OS path-separator-delimited. */
    public volatile String sourcePath;

    /** Assembled class path ({@code -classpath}), OS path-separator-delimited. */
    public volatile String classPath;

    /** Assembled specs path ({@code --specs-path}), OS path-separator-delimited. */
    public volatile String specsPath;

    /**
     * The IDE's Java compiler output directory.  Kept here (not in
     * {@link #clientSettings}) because per-project copies carry per-project
     * values sourced from {@link ProjectConfig#javaOutputDir}.
     */
    public volatile String javaOutputDir;

    /**
     * RAC output directory ({@code -d}).  Kept here (not in
     * {@link #clientSettings}) because per-project copies carry per-project
     * values sourced from {@link ProjectConfig#racOutputDir}.
     */
    public volatile String racOutputDir;

    // -----------------------------------------------------------------------
    // Runtime state
    // -----------------------------------------------------------------------

    /**
     * Fixed thread pool shared by all ESC execution paths.  Sized to
     * {@link ClientSettings#escThreads}; recreated by {@link OpenJMLWorkspaceService}
     * whenever {@code escThreads} changes.
     */
    public transient java.util.concurrent.ExecutorService escPool =
            java.util.concurrent.Executors.newFixedThreadPool(5);

    /**
     * Accumulated client settings.  Initialized to {@link ClientSettings#createDefaults()}
     * so helper methods never need to null-check.  Updated incrementally by
     * {@link OpenJMLWorkspaceService#applyUpdate} on every configuration message.
     */
    public volatile ClientSettings clientSettings = ClientSettings.createDefaults();

    // -----------------------------------------------------------------------
    // Constructors
    // -----------------------------------------------------------------------

    /** No-arg constructor — {@link #clientSettings} is pre-populated with defaults. */
    public OpenJMLSettings() {}

    /**
     * Copy constructor for per-invocation snapshots.  Copies assembled path
     * fields and per-project path overrides; shares {@link #escPool} and
     * {@link #clientSettings} with the source (both are safe to share across
     * read-only tool invocations).
     */
    public OpenJMLSettings(OpenJMLSettings src) {
        this.projectId      = src.projectId;
        this.specsPath      = src.specsPath;
        this.sourcePath     = src.sourcePath;
        this.classPath      = src.classPath;
        this.javaOutputDir  = src.javaOutputDir;
        this.racOutputDir   = src.racOutputDir;
        this.escPool        = src.escPool;          // share the pool
        this.clientSettings = src.clientSettings;   // share client values
    }

    // -----------------------------------------------------------------------
    // Helpers delegating to clientSettings
    // -----------------------------------------------------------------------

    /** Returns {@code true} if --check should fire on every edit (debounced). */
    public boolean isCheckOnEdit()  { return "edit".equalsIgnoreCase(clientSettings.checkTriggerOn); }

    /** Returns {@code true} if --check should fire on save and open. */
    public boolean isCheckOnSave()  { return "save".equalsIgnoreCase(clientSettings.checkTriggerOn); }

    /** Returns {@code true} if --check fires only on explicit command. */
    public boolean isCheckManual()  { return "manual".equalsIgnoreCase(clientSettings.checkTriggerOn); }

    /** Returns {@code true} if --esc fires on save. */
    public boolean isEscOnSave()    { return "save".equalsIgnoreCase(clientSettings.escTriggerOn); }

    /** Returns {@code true} if --esc fires only on explicit command. */
    public boolean isEscManual()    { return "manual".equalsIgnoreCase(clientSettings.escTriggerOn); }

    /** Returns {@code true} when OpenJML should emit tokens for all Java constructs. */
    public boolean isOverwriteJavaColoring() {
        return "overwrite Java coloring".equalsIgnoreCase(clientSettings.syntaxColoringScope);
    }

    /** Returns {@code true} if the regex-only coloring strategy is selected. */
    public boolean isRegexColoring() { return "regex".equalsIgnoreCase(clientSettings.syntaxColoringStrategy); }

    /** Returns {@code true} if the concurrent in-process ESC engine is selected. */
    public boolean isEscApiMode() { return "concurrent".equalsIgnoreCase(clientSettings.escEngine); }

    /**
     * Returns the effective {@code javaMode}.  Explicit client setting takes
     * priority; otherwise {@code "eclipse-jdt"}, {@code "vscode-java"}, and
     * {@code "intellij"} default to {@code "jml-only"}, everything else to
     * {@code "full"}.
     */
    public String effectiveJavaMode() {
        String jm = clientSettings.javaMode;
        if (jm != null && !jm.isEmpty()) return jm;
        String c = clientSettings.client;
        if ("eclipse-jdt".equals(c) || "vscode-java".equals(c) || "intellij".equals(c))
            return "jml-only";
        return "full";
    }

    /** Returns {@code true} when Java-overlapping capabilities should be suppressed. */
    public boolean isJmlOnly() { return "jml-only".equals(effectiveJavaMode()); }

    // -----------------------------------------------------------------------
    // Derived queries
    // -----------------------------------------------------------------------

    /**
     * Returns the effective list of root paths for JML work.
     */
    public List<String> effectiveRoots() {
        if (projects != null && !projects.isEmpty()) {
            return projects.stream()
                    .filter(p -> p.rootPaths != null)
                    .flatMap(p -> p.rootPaths.stream())
                    .filter(r -> r != null && !r.isBlank())
                    .collect(Collectors.toList());
        }
        if (rootPaths != null && !rootPaths.isEmpty())
            return rootPaths;
        return List.of();
    }

    // -----------------------------------------------------------------------
    // Utilities
    // -----------------------------------------------------------------------

    /**
     * Expands environment-variable tokens in {@code s} treating it as an
     * OS path-separator-delimited list.
     *
     * <p>Recognised token forms: {@code $VARNAME}, {@code ${VARNAME}},
     * {@code $(VARNAME)}.  Unknown variables are replaced with the empty
     * string and a warning is written to the server log.  Components that
     * are empty or blank after expansion are dropped.
     *
     * <p>Returns {@code s} unchanged when it is {@code null} or contains
     * no {@code $} character (fast path).
     */
    public static String expandEnvVarsInPath(String s) {
        if (s == null || !s.contains("$")) return s;
        String sep = java.io.File.pathSeparator;
        java.util.regex.Pattern VAR = java.util.regex.Pattern.compile(
                "\\$\\{([A-Za-z_][A-Za-z0-9_]*)\\}" +
                "|\\$\\(([A-Za-z_][A-Za-z0-9_]*)\\)" +
                "|\\$([A-Za-z_][A-Za-z0-9_]*)");
        String[] parts = s.split(java.util.regex.Pattern.quote(sep), -1);
        StringBuilder sb = new StringBuilder();
        for (String part : parts) {
            if (!part.contains("$")) {
                if (!part.isBlank()) { if (sb.length() > 0) sb.append(sep); sb.append(part); }
                continue;
            }
            String expanded = VAR.matcher(part).replaceAll(mr -> {
                String name = mr.group(1) != null ? mr.group(1)
                            : mr.group(2) != null ? mr.group(2) : mr.group(3);
                String v = System.getenv(name);
                if (v != null) return java.util.regex.Matcher.quoteReplacement(v);
                CheckRunner.log("[settings] Unknown environment variable $" + name
                        + " in path \"" + s + "\" — omitted.");
                return "";
            });
            if (!expanded.isBlank()) { if (sb.length() > 0) sb.append(sep); sb.append(expanded); }
        }
        return sb.toString();
    }

    // -----------------------------------------------------------------------
    // Logging
    // -----------------------------------------------------------------------

    /**
     * Logs the current effective settings to the server log.
     *
     * @param projectSettings per-project registry; pass {@code null} to log
     *        global settings only
     */
    public void logConfiguration(java.util.Map<String, OpenJMLSettings> projectSettings) {
        StringBuilder sb = new StringBuilder("[configuration]\n");

        ClientSettings cs = clientSettings;
        sb.append("  [from client]\n");
        sb.append("    client=").append(cs.client).append('\n');
        sb.append("    javaMode=").append(cs.javaMode)
          .append(" (effective=").append(effectiveJavaMode()).append(")\n");
        sb.append("    checkTriggerOn=").append(cs.checkTriggerOn).append('\n');
        sb.append("    escTriggerOn=").append(cs.escTriggerOn).append('\n');
        sb.append("    escEngine=").append(cs.escEngine)
          .append("  escThreads=").append(cs.escThreads).append('\n');
        sb.append("    syntaxColoringScope=").append(cs.syntaxColoringScope).append('\n');
        sb.append("    syntaxColoringStrategy=").append(cs.syntaxColoringStrategy).append('\n');
        sb.append("    useIntegratedOutline=").append(cs.useIntegratedOutline).append('\n');
        sb.append("    incrementalSync=").append(cs.incrementalSync).append('\n');
        sb.append("    supportsActionMessages=").append(cs.supportsActionMessages).append('\n');
        sb.append("    sourcePath=").append(cs.sourcePath).append('\n');
        sb.append("    classPath=").append(cs.classPath).append('\n');
        sb.append("    specsPath=").append(cs.specsPath).append('\n');
        sb.append("    javaOutputDir=").append(cs.javaOutputDir).append('\n');
        sb.append("    racOutputDir=").append(cs.racOutputDir).append('\n');
        sb.append("    toolOptions=").append(cs.toolOptions).append('\n');
        sb.append("    workspaceFolderPaths=").append(cs.workspaceFolderPaths).append('\n');

        sb.append("  [assembled by server]\n");
        sb.append("    sourcePath=").append(sourcePath).append('\n');
        sb.append("    classPath=").append(classPath).append('\n');
        sb.append("    specsPath=").append(specsPath).append('\n');

        if (projectSettings == null || projectSettings.isEmpty()) {
            sb.append("  [projects] (none)\n");
        } else {
            sb.append("  [projects] (").append(projectSettings.size()).append("):\n");
            for (java.util.Map.Entry<String, OpenJMLSettings> e :
                    new java.util.TreeMap<>(projectSettings).entrySet()) {
                String id = e.getKey().isEmpty() ? "(workspace)" : e.getKey();
                OpenJMLSettings ps = e.getValue();
                sb.append("    [").append(id).append("]\n");
                sb.append("      rootPaths=").append(ps.rootPaths).append('\n');
                sb.append("      sourcePath=").append(ps.sourcePath).append('\n');
                sb.append("      classPath=").append(ps.classPath).append('\n');
                sb.append("      specsPath=").append(ps.specsPath).append('\n');
                sb.append("      racOutputDir=").append(ps.racOutputDir).append('\n');
                sb.append("      javaOutputDir=").append(ps.javaOutputDir).append('\n');
            }
        }
        ServerLog.serverLog(sb.toString());
    }
}
