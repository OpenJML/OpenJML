/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.IOException;
import java.net.URI;
import java.net.URL;
import java.util.Arrays;
import java.util.Map;

import org.eclipse.core.runtime.Platform;
import org.eclipse.lsp4e.server.ProcessStreamConnectionProvider;

/**
 * Launches the openjml-lsp server process and connects to it via
 * stdin/stdout using the LSP4E framework.
 *
 * The server executable path is taken from the preference
 * {@link Options#lspServerPathKey} if set; otherwise it defaults to
 * an {@code openjml-lsp} script in the same directory as the Eclipse
 * installation.
 */
public class OpenJMLStreamConnectionProvider extends ProcessStreamConnectionProvider {

    static {
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider class loaded");
    }

    public OpenJMLStreamConnectionProvider() {
        String path = findServerPath();
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider created, path=" + path);
        setCommands(Arrays.asList(path));
        setWorkingDirectory(System.getProperty("user.dir"));
    }

    /**
     * Resolves the path to the openjml-lsp launcher script.
     * Priority:
     *   1. User preference (Options.lspServerPathKey)
     *   2. Directory of the Eclipse install (Platform.getInstallLocation)
     */
    private static String findServerPath() {
        String pref = OpenJMLOptions.value(OpenJMLOptions.lspServerPathKey);
        if (pref != null && !pref.isBlank()) {
            return pref;
        }
        try {
            URL installUrl = Platform.getInstallLocation().getURL();
            String installDir = installUrl.getPath();
            if (!installDir.endsWith("/")) installDir += "/";
            return installDir + "openjml-lsp";
        } catch (Exception e) {
            // Fall back to expecting it on PATH
            return "openjml-lsp";
        }
    }

    /**
     * Sends OpenJML analysis settings to the server as initialization options,
     * matching the fields in {@link org.openjml.lsp.OpenJMLSettings}.
     */
    @Override
    public void start() throws IOException {
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider.start() called");
        super.start();
        System.err.println("[OpenJML] OpenJMLStreamConnectionProvider.start() completed");
    }

    @Override
    public Object getInitializationOptions(URI rootUri) {
        Map<String, Object> opts = OpenJMLOptions.buildInitializationOptions();
        Console.log("[OpenJML] Sending initializationOptions: checkTriggerOn="
                + opts.get("checkTriggerOn") + ", escEngine=" + opts.get("escEngine"));
        return opts;
    }

    @Override
    public String toString() {
        return "OpenJML LSP Server " + super.toString();
    }
}
