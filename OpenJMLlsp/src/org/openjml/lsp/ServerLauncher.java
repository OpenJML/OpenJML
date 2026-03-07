package org.openjml.lsp;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;

import java.util.concurrent.ExecutionException;

/**
 * Entry point for the OpenJML LSP server.
 *
 * Communicates with the editor client via stdin/stdout using the LSP
 * JSON-RPC framing protocol.  Invoke via the {@code openjml-lsp} script,
 * which sets the required JVM module-system flags.
 */
public class ServerLauncher {

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        var server   = new OpenJMLLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, System.in, System.out);

        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        // Block until the connection is closed.
        launcher.startListening().get();
    }
}
