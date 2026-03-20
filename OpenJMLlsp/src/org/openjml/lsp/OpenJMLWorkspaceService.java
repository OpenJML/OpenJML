package org.openjml.lsp;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.WorkspaceSymbolParams;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.WorkspaceService;

import java.util.List;
import java.util.concurrent.CompletableFuture;
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

    private final OpenJMLSettings settings;
    private final CommandRegistry commands;
    private final Function<String, List<SymbolInformation>> symbolsRequester;

    /**
     * @param settings         shared settings object (mutated by didChangeConfiguration)
     * @param commands         registry of command-name → handler mappings
     * @param symbolsRequester called with a query string for {@code workspace/symbol} requests;
     *                         returns matching {@link SymbolInformation} list
     */
    public OpenJMLWorkspaceService(OpenJMLSettings settings,
                                   CommandRegistry commands,
                                   Function<String, List<SymbolInformation>> symbolsRequester) {
        this.settings          = settings;
        this.commands          = commands;
        this.symbolsRequester  = symbolsRequester;
    }

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {
        Object raw = params.getSettings();
        if (raw == null) return;
        JsonElement element = toJsonElement(raw);
        if (!element.isJsonObject()) return;
        JsonObject obj = element.getAsJsonObject();

        // VS Code sends the configurationSection value directly (fields at top level).
        // Manual/test clients wrap them under an "openjml" key.  Handle both.
        JsonElement nested = obj.get("openjml");
        try {
            OpenJMLSettings src = (nested != null && nested.isJsonObject())
                    ? GSON.fromJson(nested, OpenJMLSettings.class)
                    : GSON.fromJson(obj,    OpenJMLSettings.class);
            applyUpdate(src);
        } catch (Exception e) {
            System.err.println("[OpenJML] Failed to parse settings: " + e);
        }
    }

    @Override
    public CompletableFuture<Object> executeCommand(ExecuteCommandParams params) {
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
            applyUpdate(GSON.fromJson(element, OpenJMLSettings.class));
        } catch (Exception e) {
            System.err.println("[OpenJML] Failed to parse settings: " + e);
        }
    }

    private static JsonElement toJsonElement(Object raw) {
        return (raw instanceof JsonElement) ? (JsonElement) raw : GSON.toJsonTree(raw);
    }

    private void applyUpdate(OpenJMLSettings src) {
        if (src.propertiesFile  != null) settings.propertiesFile  = src.propertiesFile;
        if (src.specsPath       != null) settings.specsPath       = src.specsPath;
        if (src.solversPath     != null) settings.solversPath     = src.solversPath;
        if (src.sourcePath      != null) settings.sourcePath      = src.sourcePath;
        if (src.classPath       != null) settings.classPath       = src.classPath;
        if (src.checkTriggerOn         != null) settings.checkTriggerOn         = src.checkTriggerOn;
        if (src.escTriggerOn           != null) settings.escTriggerOn           = src.escTriggerOn;
        if (src.syntaxColoringStrategy != null) settings.syntaxColoringStrategy = src.syntaxColoringStrategy;
        if (src.escEngine              != null) settings.escEngine              = src.escEngine;
        if (src.racOutputDir         != null) settings.racOutputDir         = src.racOutputDir;
        if (src.useIntegratedOutline != null) settings.useIntegratedOutline = src.useIntegratedOutline;
        if (src.escThreads > 0 && src.escThreads != settings.escThreads) {
            settings.escThreads = src.escThreads;
            var old = settings.escPool;
            settings.escPool = java.util.concurrent.Executors.newFixedThreadPool(src.escThreads);
            old.shutdown();
        }
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
        List<SymbolInformation> results =
                symbolsRequester != null ? symbolsRequester.apply(query) : List.of();
        return CompletableFuture.completedFuture(Either.forLeft(results));
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {}
}
