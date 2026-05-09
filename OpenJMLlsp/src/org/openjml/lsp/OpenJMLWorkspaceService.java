package org.openjml.lsp;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.FileChangeType;
import org.eclipse.lsp4j.FileEvent;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.WorkspaceSymbolParams;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.WorkspaceService;

import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Handles LSP workspace-level notifications.
 *
 * <p>{@code workspace/didChangeConfiguration} applies updated settings.
 * Only non-null fields in the incoming JSON overwrite current settings.
 *
 * <p>{@code workspace/executeCommand} dispatches to the {@link CommandRegistry}
 * supplied at construction time.  Command names and their handlers are registered
 * by the caller (see {@link OpenJMLLanguageServer}).
 */
public class OpenJMLWorkspaceService implements WorkspaceService {

    private static final Gson GSON = new Gson();

    private final OpenJMLSettings globalSettings;
    private final CommandRegistry commands;
    private final Function<String, List<org.eclipse.lsp4j.WorkspaceSymbol>> symbolsRequester;
    private final BiConsumer<String, FileChangeType> jmlFileChangeHandler;
    private final BiConsumer<String, FileChangeType> javaFileChangeHandler;
    private final Runnable watcherReregistrar;
    private final Consumer<List<ProjectConfig>> projectConfigUpdater;

    /**
     * @param globalSettings        shared settings object (mutated by didChangeConfiguration)
     * @param commands              registry of command-name → handler mappings
     * @param symbolsRequester      called with a query string for {@code workspace/symbol} requests;
     *                              returns matching {@link org.eclipse.lsp4j.WorkspaceSymbol} list
     * @param jmlFileChangeHandler  called when a watched {@code .jml} file changes on disk
     * @param javaFileChangeHandler called when a watched {@code .java} file is created/deleted on disk
     * @param watcherReregistrar    called when the effective roots change so file watchers
     *                              are re-registered with the updated scope
     * @param projectConfigUpdater  called with the parsed project list whenever
     *                              {@code didChangeConfiguration} carries a {@code projects} entry
     */
    public OpenJMLWorkspaceService(OpenJMLSettings globalSettings,
                                   CommandRegistry commands,
                                   Function<String, List<org.eclipse.lsp4j.WorkspaceSymbol>> symbolsRequester,
                                   BiConsumer<String, FileChangeType> jmlFileChangeHandler,
                                   BiConsumer<String, FileChangeType> javaFileChangeHandler,
                                   Runnable watcherReregistrar,
                                   Consumer<List<ProjectConfig>> projectConfigUpdater) {
        this.globalSettings         = globalSettings;
        this.commands               = commands;
        this.symbolsRequester       = symbolsRequester;
        this.jmlFileChangeHandler   = jmlFileChangeHandler;
        this.javaFileChangeHandler  = javaFileChangeHandler;
        this.watcherReregistrar     = watcherReregistrar;
        this.projectConfigUpdater   = projectConfigUpdater;
    }

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {
        ServerLog.serverLog("[OpenJML] didChangeConfiguration received");
        Object raw = params.getSettings();
        if (raw == null) return;
        JsonElement element = toJsonElement(raw);
        if (!element.isJsonObject()) return;
        JsonObject obj = element.getAsJsonObject();

        // VS Code sends the configurationSection value directly (fields at top level).
        // Manual/test clients wrap them under an "openjml" key.  Handle both.
        JsonElement nested = obj.get("openjml");
        try {
            ClientSettings src = (nested != null && nested.isJsonObject())
                    ? GSON.fromJson(nested, ClientSettings.class)
                    : GSON.fromJson(obj,    ClientSettings.class);
            applyUpdate(src);
            // Log updated configuration.  Eclipse sends src.projects (non-null), which
            // already triggers logConfiguration via updateProjectSettings → skip here to
            // avoid a redundant "projects: (none)" entry.  VS Code sends src.projects=null.
            if (src.projects == null) globalSettings.logConfiguration(null);
        } catch (Exception e) {
            ServerLog.serverLog("[OpenJML] Failed to parse settings: " + e);
        }
    }

    @Override
    public CompletableFuture<Object> executeCommand(ExecuteCommandParams params) {
        ServerLog.serverLog("[workspace/executeCommand] command=" + params.getCommand()
                + " args=" + params.getArguments());
        Object result = commands.dispatch(params.getCommand(), params.getArguments());
        return CompletableFuture.completedFuture(result);
    }

    /**
     * Apply settings from a raw object (used by {@code initializationOptions}).
     */
    void applyRaw(Object raw) {
        if (raw == null) return;
        JsonElement element = toJsonElement(raw);
        if (!element.isJsonObject()) return;
        try {
            applyUpdate(GSON.fromJson(element, ClientSettings.class));
        } catch (Exception e) {
            ServerLog.serverLog("[OpenJML] Failed to parse settings: " + e);
        }
    }

    private static JsonElement toJsonElement(Object raw) {
        return (raw instanceof JsonElement) ? (JsonElement) raw : GSON.toJsonTree(raw);
    }

    private void applyUpdate(ClientSettings src) {
        // Merge non-null fields from src into the accumulated clientSettings.
        ClientSettings cs = globalSettings.clientSettings;  // never null (initialized to defaults)
        if (src.toolOptions            != null) cs.toolOptions            = src.toolOptions;
        if (src.sourcePath             != null) cs.sourcePath             = src.sourcePath;
        if (src.classPath              != null) cs.classPath              = src.classPath;
        if (src.specsPath              != null) cs.specsPath              = src.specsPath;
        if (src.javaOutputDir          != null) cs.javaOutputDir          = src.javaOutputDir;
        if (src.racOutputDir           != null) cs.racOutputDir           = src.racOutputDir;
        if (src.genericMode            != null) cs.genericMode            = src.genericMode;
        if (src.workspaceFolderPaths   != null) cs.workspaceFolderPaths   = src.workspaceFolderPaths;
        if (src.checkTriggerOn         != null) cs.checkTriggerOn         = src.checkTriggerOn;
        if (src.escTriggerOn           != null) cs.escTriggerOn           = src.escTriggerOn;
        if (src.syntaxColoringStrategy != null) cs.syntaxColoringStrategy = src.syntaxColoringStrategy;
        if (src.syntaxColoringScope    != null) cs.syntaxColoringScope    = src.syntaxColoringScope;
        if (src.escEngine              != null) cs.escEngine              = src.escEngine;
        if (src.escThreads             != null) cs.escThreads             = src.escThreads;
        if (src.useIntegratedOutline   != null) cs.useIntegratedOutline   = src.useIntegratedOutline;
        if (src.incrementalSync        != null) cs.incrementalSync        = src.incrementalSync;
        if (src.javaMode               != null) cs.javaMode               = src.javaMode;
        if (src.client                 != null) cs.client                 = src.client;
        if (src.supportsActionMessages != null) cs.supportsActionMessages = src.supportsActionMessages;
        if (src.projects               != null) cs.projects               = src.projects;

        // Per-project path overrides (javaOutputDir/racOutputDir kept on globalSettings
        // because per-project copies carry per-project values from ProjectConfig).
        if (src.javaOutputDir != null) globalSettings.javaOutputDir = src.javaOutputDir;
        if (src.racOutputDir  != null) globalSettings.racOutputDir  = src.racOutputDir;

        // Resize the ESC thread pool when the thread count changes.
        // Resize in-place: no threads are interrupted; reducing the limit just
        // prevents new threads from starting until the active count falls below it.
        int newPoolSize = (cs.escThreads != null && cs.escThreads > 0)
                ? cs.escThreads : ClientSettings.DEFAULT_ESC_THREADS;
        if (globalSettings.escPool instanceof java.util.concurrent.ThreadPoolExecutor tpe
                && newPoolSize != tpe.getCorePoolSize()) {
            if (newPoolSize > tpe.getMaximumPoolSize()) {
                tpe.setMaximumPoolSize(newPoolSize);
            }
            tpe.setCorePoolSize(newPoolSize);
        }

        // Per-project configs: update the project registry and re-register file watchers.
        if (src.projects != null) {
            globalSettings.projects = src.projects;
            if (projectConfigUpdater != null) projectConfigUpdater.accept(src.projects);
            if (watcherReregistrar != null) watcherReregistrar.run();
        }

        // Assemble effective paths.
        // genericMode==true  → generic/VS Code client: server assembles paths from components.
        // genericMode==false → non-generic client (e.g. Eclipse): paths are pre-assembled.
        String sep = java.io.File.pathSeparator;
        String wfp = cs.workspaceFolderPaths != null ? cs.workspaceFolderPaths : "";
        if (cs.genericMode) {
            // sourcePath = user additions + workspace folder roots
            String userSrc = expandEnvVarsInPath(cs.sourcePath != null ? cs.sourcePath : "");
            var srcParts = new java.util.ArrayList<String>();
            if (!userSrc.isBlank()) srcParts.add(userSrc);
            if (!wfp.isBlank()) srcParts.add(wfp);
            globalSettings.sourcePath = String.join(sep, srcParts);
            // classPath = user additions + javaOutputDir + racOutputDir (if different)
            String userCp  = expandEnvVarsInPath(cs.classPath != null ? cs.classPath : "");
            String javaOut = globalSettings.javaOutputDir != null ? globalSettings.javaOutputDir : "";
            String racOut  = (globalSettings.racOutputDir != null && !globalSettings.racOutputDir.isBlank())
                    ? globalSettings.racOutputDir : javaOut;
            var cpParts = new java.util.ArrayList<String>();
            if (!userCp.isBlank()) cpParts.add(userCp);
            if (!javaOut.isBlank()) cpParts.add(javaOut);
            if (!racOut.isBlank() && !racOut.equals(javaOut)) cpParts.add(racOut);
            globalSettings.classPath = String.join(sep, cpParts);
            // specsPath = user specsPath prepended to assembled sourcePath (if non-empty)
            String userSpec = expandEnvVarsInPath(cs.specsPath != null ? cs.specsPath : "");
            if (!userSpec.isBlank()) {
                String sp = globalSettings.sourcePath;
                globalSettings.specsPath = sp.isBlank() ? userSpec : userSpec + sep + sp;
            }
        } else {
            // Eclipse: paths are pre-assembled; just expand env vars.
            if (src.sourcePath != null)
                globalSettings.sourcePath = expandEnvVarsInPath(src.sourcePath);
            if (src.classPath  != null)
                globalSettings.classPath  = expandEnvVarsInPath(src.classPath);
            if (src.specsPath  != null)
                globalSettings.specsPath  = expandEnvVarsInPath(src.specsPath);
        }
    }

    private static String expandEnvVarsInPath(String s) {
        return OpenJMLSettings.expandEnvVarsInPath(s);
    }

    /**
     * Handle {@code workspace/didChangeWorkspaceFolders} notifications.
     *
     * <p>For standard LSP clients (VS Code, bare LSP) the server synthesizes a
     * {@code "__workspace__"} project at initialization time.  This handler keeps
     * that project's {@code rootPaths} in sync as the user opens and closes folders.
     *
     * <p>For multi-project Eclipse clients the project list is managed via
     * {@code didChangeConfiguration}, so this notification is a no-op.
     */
    @Override
    public void didChangeWorkspaceFolders(
            org.eclipse.lsp4j.DidChangeWorkspaceFoldersParams params) {
        if (params == null || params.getEvent() == null) return;

        // Find the synthesized __workspace__ project.
        ProjectConfig wp = null;
        if (globalSettings.projects != null) {
            for (ProjectConfig p : globalSettings.projects) {
                if (OpenJMLSettings.WORKSPACE_PROJECT_ID.equals(p.id)) { wp = p; break; }
            }
        }
        if (wp == null) return;   // Eclipse client — ignore.

        List<String> roots = wp.rootPaths != null
                ? new java.util.ArrayList<>(wp.rootPaths)
                : new java.util.ArrayList<>();

        var event = params.getEvent();
        if (event.getAdded() != null) {
            for (var folder : event.getAdded()) {
                String path = uriToOsPath(folder.getUri());
                if (path != null && !roots.contains(path)) roots.add(path);
            }
        }
        if (event.getRemoved() != null) {
            for (var folder : event.getRemoved()) {
                String path = uriToOsPath(folder.getUri());
                if (path != null) roots.remove(path);
            }
        }

        wp.rootPaths = roots;
        // Sync sourcePath from rootPaths so per-project settings reflect new roots.
        wp.sourcePath = String.join(java.io.File.pathSeparator, roots);
        globalSettings.sourcePath = wp.sourcePath;
        if (projectConfigUpdater != null) projectConfigUpdater.accept(globalSettings.projects);
        if (watcherReregistrar != null) watcherReregistrar.run();
        ServerLog.serverLog("[workspace/didChangeWorkspaceFolders] rootPaths now: " + roots);
    }

    private static String uriToOsPath(String uri) {
        if (uri == null || !uri.startsWith("file:")) return null;
        try { return java.nio.file.Path.of(java.net.URI.create(uri)).toString(); }
        catch (Exception e) { return null; }
    }

    /**
     * Handle {@code workspace/symbol} requests (Cmd+T / Ctrl+T in VS Code).
     *
     * <p>Delegates to the text document service's indexed declarations, filtered
     * by a case-insensitive substring match on the symbol name.
     */
    @Override
    public CompletableFuture<Either<List<? extends SymbolInformation>, List<? extends org.eclipse.lsp4j.WorkspaceSymbol>>>
            symbol(WorkspaceSymbolParams params) {
        String query = params.getQuery() != null ? params.getQuery() : "";
        ServerLog.serverLog("[workspace/symbol] request: query=\"" + query + "\"");
        List<org.eclipse.lsp4j.WorkspaceSymbol> results =
                symbolsRequester != null ? symbolsRequester.apply(query) : List.of();
        ServerLog.serverLog("[workspace/symbol] response: " + results.size() + " result(s)"
                + (results.isEmpty() ? "" : ", first=" + results.get(0).getName()));
        return CompletableFuture.completedFuture(Either.forRight(results));
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {
        ServerLog.serverLog("[workspace/didChangeWatchedFiles]");
        for (FileEvent event : params.getChanges()) {
            String uri  = event.getUri();
            FileChangeType type = event.getType();
            if (!isUnderEffectiveRoot(uri)) continue;
            if (uri.endsWith(".jml") && jmlFileChangeHandler != null) {
                jmlFileChangeHandler.accept(uri, type);
            } else if (uri.endsWith(".java") && javaFileChangeHandler != null) {
                javaFileChangeHandler.accept(uri, type);
            }
        }
    }

    /** Returns {@code true} if {@code uri} falls under one of the effective workspace roots. */
    private boolean isUnderEffectiveRoot(String uri) {
        List<String> roots = globalSettings.effectiveRoots();
        if (roots.isEmpty()) return true;   // no filter configured — accept everything
        String path = CheckRunner.uriToPath(uri);
        if (path == null) return false;
        for (String root : roots) {
            if (path.startsWith(root)) return true;
        }
        return false;
    }
}
