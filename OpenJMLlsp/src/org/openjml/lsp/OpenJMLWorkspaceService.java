package org.openjml.lsp;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonElement;
import com.google.gson.JsonPrimitive;
import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.services.WorkspaceService;

import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.function.Consumer;

/**
 * Handles LSP workspace-level notifications.
 *
 * <p>{@code workspace/didChangeConfiguration} applies updated settings.
 * Only non-null fields in the incoming JSON overwrite current settings.
 *
 * <p>{@code workspace/executeCommand} with command {@code "openjml.runEsc"}
 * and a single URI argument triggers an immediate ESC check on that file.
 */
public class OpenJMLWorkspaceService implements WorkspaceService {

    private static final Gson GSON = new Gson();

    private final OpenJMLSettings settings;
    private final Consumer<String> escRequester;

    /**
     * @param settings      shared settings object
     * @param escRequester  called with the URI when {@code openjml.runEsc} is requested
     */
    public OpenJMLWorkspaceService(OpenJMLSettings settings, Consumer<String> escRequester) {
        this.settings     = settings;
        this.escRequester = escRequester;
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
        if ("openjml.runEsc".equals(params.getCommand()) && escRequester != null) {
            List<?> args = params.getArguments();
            if (args != null && !args.isEmpty()) {
                // LSP4J deserializes arguments as JsonElement; extract string value.
                Object arg = args.get(0);
                String uri = (arg instanceof JsonPrimitive)
                        ? ((JsonPrimitive) arg).getAsString()
                        : String.valueOf(arg);
                escRequester.accept(uri);
            }
        }
        return CompletableFuture.completedFuture(null);
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

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {}
}
