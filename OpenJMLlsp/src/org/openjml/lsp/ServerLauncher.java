package org.openjml.lsp;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.concurrent.ExecutionException;

/**
 * Entry point for the OpenJML LSP server jar.
 *
 * <p>Wires up {@link OpenJMLLanguageServer} with the standard VS Code command names,
 * redirects {@code System.out} to {@code stderr} so that OpenJML's compiler output
 * never corrupts the LSP wire stream, then blocks until the connection closes.
 *
 * <p>{@link org.openjml.vscode.VsCodeServerLauncher} is kept as a thin alias for
 * backward compatibility but delegates here.
 */
public class ServerLauncher {

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        // Capture real stdout for the LSP stream BEFORE redirecting System.out,
        // so that OpenJML (javac) output does not corrupt the LSP wire protocol.
        PrintStream lspOut = System.out;
        System.setOut(System.err);

        var server = new OpenJMLLanguageServer();

        // Trace all JSON-RPC messages to stderr so we can see what LSP4E is sending.
        var tracer = new PrintWriter(System.err, true);
        var launcher = LSPLauncher.createServerLauncher(server, System.in, lspOut, false, tracer);
        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        launcher.startListening().get();
    }
}
