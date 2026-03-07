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
        JsonElement element = toJsonElement(raw);
        if (!element.isJsonObject()) return;
        JsonObject obj = element.getAsJsonObject();

        // VS Code sends the configurationSection value directly, so the object
        // contains the settings fields (triggerOn, mode, …) at the top level.
        // Manual/test clients wrap them under an "openjml" key.  Handle both.
        JsonElement nested = obj.get("openjml");
        OpenJMLSettings src = (nested != null && nested.isJsonObject())
                ? GSON.fromJson(nested, OpenJMLSettings.class)
                : GSON.fromJson(obj,    OpenJMLSettings.class);
        applyUpdate(src);
    }

    /**
     * Apply settings from a raw object (used by {@code initializationOptions}).
     * The object is deserialized directly as {@link OpenJMLSettings} — no
     * enclosing {@code "openjml"} key is expected.
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
        if (src.specsPath   != null) settings.specsPath   = src.specsPath;
        if (src.solversPath != null) settings.solversPath = src.solversPath;
        if (src.mode        != null) settings.mode        = src.mode;
        if (src.triggerOn   != null) settings.triggerOn   = src.triggerOn;
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {}
}
