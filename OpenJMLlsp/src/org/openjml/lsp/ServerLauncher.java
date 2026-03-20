package org.openjml.lsp;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;
import org.openjml.vscode.VsCodeCommands;

import java.io.PrintStream;
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

        var server = new OpenJMLLanguageServer(
                VsCodeCommands.RUN_ESC,
                VsCodeCommands.RUN_ESC_FOR_METHOD,
                VsCodeCommands.RUN_ESC_DIR,
                VsCodeCommands.FOCUS_FILE,
                VsCodeCommands.GET_SEMANTIC_TOKENS,
                VsCodeCommands.RUN_RAC,
                VsCodeCommands.CLEAR_AND_REINDEX,
                VsCodeCommands.CLEAR_MARKERS);

        var launcher = LSPLauncher.createServerLauncher(server, System.in, lspOut);
        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        launcher.startListening().get();
    }
}
