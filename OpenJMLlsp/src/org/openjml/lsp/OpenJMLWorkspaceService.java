package org.openjml.lsp;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.services.WorkspaceService;

/**
 * Handles LSP workspace-level notifications.
 *
 * {@code workspace/didChangeConfiguration} is handled: the settings object
 * is expected to have an {@code "openjml"} key whose value maps to
 * {@link OpenJMLSettings} fields.  Example VS Code settings.json fragment:
 * <pre>
 * {
 *   "openjml": {
 *     "specsPath":   "/path/to/Specs/specs",
 *     "solversPath": "/path/to/Solvers",
 *     "mode":        "check"
 *   }
 * }
 * </pre>
 *
 * Only non-null fields in the incoming JSON object overwrite the current
 * settings, so a partial update (e.g., just {@code mode}) is safe.
 */
public class OpenJMLWorkspaceService implements WorkspaceService {

    private static final Gson GSON = new Gson();

    private final OpenJMLSettings settings;

    public OpenJMLWorkspaceService(OpenJMLSettings settings) {
        this.settings = settings;
    }

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {
        Object raw = params.getSettings();
        if (raw == null) return;
        // LSP4J deserializes JSON payloads as JsonElement; handle both cases.
        JsonElement element = (raw instanceof JsonElement)
                ? (JsonElement) raw
                : GSON.toJsonTree(raw);
        if (!element.isJsonObject()) return;
        JsonElement openjml = element.getAsJsonObject().get("openjml");
        if (openjml == null || !openjml.isJsonObject()) return;
        applyUpdate(GSON.fromJson(openjml, OpenJMLSettings.class));
    }

    /**
     * Apply settings from a raw JSON object (used by {@code initializationOptions}).
     * The object is deserialized directly as {@link OpenJMLSettings} — no
     * enclosing {@code "openjml"} key is expected.
     */
    void applyRaw(Object raw) {
        if (raw == null) return;
        JsonElement element = (raw instanceof JsonElement)
                ? (JsonElement) raw
                : GSON.toJsonTree(raw);
        if (!element.isJsonObject()) return;
        applyUpdate(GSON.fromJson(element, OpenJMLSettings.class));
    }

    private void applyUpdate(OpenJMLSettings src) {
        if (src.specsPath   != null) settings.specsPath   = src.specsPath;
        if (src.solversPath != null) settings.solversPath = src.solversPath;
        if (src.mode        != null) settings.mode        = src.mode;
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {}
}
