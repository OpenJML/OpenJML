package org.openjml.lsp;

import org.openjml.vscode.VsCodeServerLauncher;

import java.util.concurrent.ExecutionException;

/**
 * Entry point for the OpenJML LSP server jar.
 *
 * Delegates to {@link VsCodeServerLauncher}, which wires up the VS Code-specific
 * command names.  The main-class of the jar points here so that the launcher
 * script ({@code openjml-lsp}) does not need to change.
 */
public class ServerLauncher {

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        VsCodeServerLauncher.main(args);
    }
}
