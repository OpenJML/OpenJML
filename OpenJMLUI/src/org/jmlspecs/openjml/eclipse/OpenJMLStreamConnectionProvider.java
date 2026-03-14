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
import java.util.LinkedHashMap;
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

    public OpenJMLStreamConnectionProvider() {
        setCommands(Arrays.asList(findServerPath()));
        setWorkingDirectory(System.getProperty("user.dir"));
    }

    /**
     * Resolves the path to the openjml-lsp launcher script.
     * Priority:
     *   1. User preference (Options.lspServerPathKey)
     *   2. Directory of the Eclipse install (Platform.getInstallLocation)
     */
    private static String findServerPath() {
        String pref = Options.value(Options.lspServerPathKey);
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
    public Object getInitializationOptions(URI rootUri) {
        Map<String, Object> opts = new LinkedHashMap<>();
        opts.put("checkTriggerOn",      nonBlank(Options.value(Options.checkTriggerOnKey), "edit"));
        opts.put("escTriggerOn",        nonBlank(Options.value(Options.escTriggerOnKey),   "manual"));
        opts.put("specsPath",           Options.value(Options.specsPathKey));
        opts.put("sourcePath",          Options.value(Options.sourcePathKey));
        opts.put("classPath",           Options.value(Options.classPathKey));
        opts.put("solversPath",         Options.value(Options.solversPathKey));
        opts.put("propertiesFile",      Options.value(Options.propertiesFileKey));
        opts.put("racOutputDir",        Options.value(Options.racOutputDirKey));
        opts.put("escEngine",           nonBlank(Options.value(Options.escEngineKey), "subprocess"));
        opts.put("useIntegratedOutline",Options.value(Options.useIntegratedOutlineKey));
        String threads = Options.value(Options.escThreadsKey);
        if (threads != null && !threads.isBlank() && !threads.equals("0")) {
            try { opts.put("escThreads", Integer.parseInt(threads.trim())); }
            catch (NumberFormatException ignored) {}
        }
        LspConsole.log("[OpenJML] Sending initializationOptions: checkTriggerOn="
                + opts.get("checkTriggerOn") + ", escEngine=" + opts.get("escEngine"));
        return opts;
    }

    private static String nonBlank(String s, String fallback) {
        return (s == null || s.isBlank()) ? fallback : s;
    }

    @Override
    public String toString() {
        return "OpenJML LSP Server " + super.toString();
    }
}
