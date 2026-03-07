package org.openjml.lsp;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;

import java.io.PrintStream;
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
        // OpenJML (javac) writes diagnostics and other output to System.out.
        // Capture the real stdout for the LSP stream BEFORE redirecting System.out
        // to stderr, so that OpenJML output never corrupts the LSP wire protocol.
        PrintStream lspOut = System.out;
        System.setOut(System.err);

        var server   = new OpenJMLLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, System.in, lspOut);

        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        // Block until the connection is closed.
        launcher.startListening().get();
    }
}
