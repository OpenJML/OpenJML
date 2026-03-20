package org.openjml.vscode;

import org.openjml.lsp.ServerLauncher;

import java.util.concurrent.ExecutionException;

/**
 * Alias entry point for the OpenJML LSP server.
 *
 * <p>Delegates to {@link ServerLauncher}, which contains the actual launch logic.
 * Kept for backward compatibility; prefer {@code ServerLauncher} directly.
 */
public class VsCodeServerLauncher {

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        ServerLauncher.main(args);
    }
}
