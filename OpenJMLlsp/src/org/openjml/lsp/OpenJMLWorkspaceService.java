package org.openjml.lsp;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.WorkspaceSymbolParams;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.WorkspaceService;

import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Handles LSP workspace-level notifications.
 *
 * <p>{@code workspace/didChangeConfiguration} applies updated settings.
 * Only non-null fields in the incoming JSON overwrite current settings.
 *
 * <p>{@code workspace/executeCommand} with the configured ESC command name
 * and a single URI argument triggers an immediate ESC check on that file.
 * With the configured ESC-for-method command name and arguments {@code [uri, methodName]},
 * triggers ESC on a single method.
 *
 * <p>Command names are supplied by the caller; they are not hardcoded here.
 * Use {@code org.openjml.vscode.VsCodeCommands} for the VS Code command names.
 */
public class OpenJMLWorkspaceService implements WorkspaceService {

    private static final Gson GSON = new Gson();

    private final OpenJMLSettings settings;
    private final Consumer<String>           escRequester;
    private final BiConsumer<String, String> escMethodRequester;
    private final Consumer<List<String>>     escDirRequester;
    private final Consumer<String>           checkRequester;
    private final Function<String, List<Integer>> semanticTokensRequester;
    private final Function<String, List<SymbolInformation>> symbolsRequester;
    private final String escCommand;
    private final String escForMethodCommand;
    private final String escDirCommand;
    private final String focusFileCommand;
    private final String getSemanticTokensCommand;

    /**
     * @param settings                 shared settings object
     * @param escRequester             called with the URI when the ESC command is requested
     * @param escMethodRequester       called with (uri, methodName) when the ESC-for-method command is requested
     * @param escDirRequester          called with a list of paths when the ESC-dir command is requested
     * @param checkRequester           called with the URI when a focus-triggered recheck is requested
     * @param semanticTokensRequester  called with a URI; returns the flat semantic token integer data
     * @param symbolsRequester         called with a query string; returns matching {@link SymbolInformation} list
     * @param escCommand               command name for full-file ESC
     * @param escForMethodCommand      command name for per-method ESC
     * @param escDirCommand            command name for multi-path ESC via {@code --dirs}
     * @param focusFileCommand         command name for focus-triggered recheck
     * @param getSemanticTokensCommand command name for semantic tokens
     */
    public OpenJMLWorkspaceService(OpenJMLSettings settings,
                                   Consumer<String>             escRequester,
                                   BiConsumer<String, String>   escMethodRequester,
                                   Consumer<List<String>>       escDirRequester,
                                   Consumer<String>             checkRequester,
                                   Function<String, List<Integer>> semanticTokensRequester,
                                   Function<String, List<SymbolInformation>> symbolsRequester,
                                   String escCommand,
                                   String escForMethodCommand,
                                   String escDirCommand,
                                   String focusFileCommand,
                                   String getSemanticTokensCommand) {
        this.settings                  = settings;
        this.escRequester              = escRequester;
        this.escMethodRequester        = escMethodRequester;
        this.escDirRequester           = escDirRequester;
        this.checkRequester            = checkRequester;
        this.semanticTokensRequester   = semanticTokensRequester;
        this.symbolsRequester          = symbolsRequester;
        this.escCommand                = escCommand;
        this.escForMethodCommand       = escForMethodCommand;
        this.escDirCommand             = escDirCommand;
        this.focusFileCommand          = focusFileCommand;
        this.getSemanticTokensCommand  = getSemanticTokensCommand;
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
        OpenJMLSettings src = (nested != null && nested.isJsonObject())
                ? GSON.fromJson(nested, OpenJMLSettings.class)
                : GSON.fromJson(obj,    OpenJMLSettings.class);
        applyUpdate(src);
    }

    @Override
    public CompletableFuture<Object> executeCommand(ExecuteCommandParams params) {
        String cmd = params.getCommand();
        List<?> args = params.getArguments();

        if (escCommand.equals(cmd) && escRequester != null) {
            if (args != null && !args.isEmpty()) {
                String uri = extractString(args.get(0));
                if (uri != null) escRequester.accept(uri);
            }
        } else if (escForMethodCommand.equals(cmd) && escMethodRequester != null) {
            if (args != null && args.size() >= 2) {
                String uri        = extractString(args.get(0));
                String methodName = extractString(args.get(1));
                if (uri != null && methodName != null) {
                    escMethodRequester.accept(uri, methodName);
                }
            }
        } else if (escDirCommand != null && escDirCommand.equals(cmd) && escDirRequester != null) {
            if (args != null && !args.isEmpty()) {
                List<String> paths = args.stream()
                        .map(OpenJMLWorkspaceService::extractString)
                        .filter(s -> s != null && !s.isEmpty())
                        .collect(Collectors.toList());
                if (!paths.isEmpty()) escDirRequester.accept(paths);
            }
        } else if (focusFileCommand != null && focusFileCommand.equals(cmd)
                && checkRequester != null) {
            if (args != null && !args.isEmpty()) {
                String uri = extractString(args.get(0));
                if (uri != null) checkRequester.accept(uri);
            }
        } else if (getSemanticTokensCommand != null && getSemanticTokensCommand.equals(cmd)
                && semanticTokensRequester != null) {
            if (args != null && !args.isEmpty()) {
                String uri = extractString(args.get(0));
                if (uri != null) {
                    return CompletableFuture.completedFuture(
                            (Object) semanticTokensRequester.apply(uri));
                }
            }
        }
        return CompletableFuture.completedFuture(null);
    }

    private static String extractString(Object arg) {
        if (arg instanceof JsonPrimitive jp) return jp.getAsString();
        if (arg != null) return String.valueOf(arg);
        return null;
    }

    /**
     * Apply settings from a raw object (used by {@code initializationOptions}).
     */
    void applyRaw(Object raw) {
        if (raw == null) return;
        JsonElement element = toJsonElement(raw);
        if (!element.isJsonObject()) return;
        applyUpdate(GSON.fromJson(element, OpenJMLSettings.class));
    }

    private static JsonElement toJsonElement(Object raw) {
        return (raw instanceof JsonElement) ? (JsonElement) raw : GSON.toJsonTree(raw);
    }

    private void applyUpdate(OpenJMLSettings src) {
        if (src.specsPath       != null) settings.specsPath       = src.specsPath;
        if (src.solversPath     != null) settings.solversPath     = src.solversPath;
        if (src.sourcePath      != null) settings.sourcePath      = src.sourcePath;
        if (src.classPath       != null) settings.classPath       = src.classPath;
        if (src.checkTriggerOn  != null) settings.checkTriggerOn  = src.checkTriggerOn;
        if (src.escTriggerOn    != null) settings.escTriggerOn    = src.escTriggerOn;
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
