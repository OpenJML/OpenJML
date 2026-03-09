package org.openjml.vscode;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PrintStream;
import java.util.concurrent.ExecutionException;

/**
 * Entry point for the OpenJML LSP server when used with VS Code.
 *
 * <p>Communicates with the editor client via stdin/stdout using the LSP
 * JSON-RPC framing protocol.  Invoke via the {@code openjml-lsp} script,
 * which sets the required JVM module-system flags.
 *
 * <p>Uses {@link VsCodeCommands} to configure the language server with the
 * VS Code-specific command names.  Note: the server does <em>not</em> advertise
 * these commands in {@code executeCommandProvider} because
 * {@code vscode-languageclient}'s {@code ExecuteCommandFeature} would otherwise
 * auto-register the VS Code command client-side and invoke it with no arguments,
 * preventing the URI from being passed.  The extension registers the commands
 * manually and sends {@code workspace/executeCommand} with the URI explicitly.
 */
public class VsCodeServerLauncher {

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        // OpenJML (javac) writes diagnostics and other output to System.out.
        // Capture the real stdout for the LSP stream BEFORE redirecting System.out
        // to stderr, so that OpenJML output never corrupts the LSP wire protocol.
        PrintStream lspOut = System.out;
        System.setOut(System.err);

        var server   = new OpenJMLLanguageServer(VsCodeCommands.RUN_ESC,
                                                  VsCodeCommands.RUN_ESC_FOR_METHOD,
                                                  VsCodeCommands.RUN_ESC_DIR);
        var launcher = LSPLauncher.createServerLauncher(server, System.in, lspOut);

        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        // Block until the connection is closed.
        launcher.startListening().get();
    }
}
