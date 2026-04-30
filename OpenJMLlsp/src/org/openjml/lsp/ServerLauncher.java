package org.openjml.lsp;

import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.services.LanguageClient;
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

    private static final String HELP =
            "openjml-lsp " + LspVersion.VERSION + "\n"
            + "Usage: openjml-lsp [--version] [--help]\n"
            + "  Starts the OpenJML LSP server communicating via stdin/stdout.\n"
            + "  Intended to be launched by an LSP client (VS Code, Eclipse, etc.).\n"
            + "  No other options are recognized.";

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        for (String arg : args) {
            switch (arg) {
                case "--version" -> { System.out.println("openjml-lsp " + LspVersion.VERSION); return; }
                case "--help"    -> { System.out.println(HELP); return; }
                default -> {
                    if (arg.startsWith("-"))
                        System.err.println("openjml-lsp: unknown option '" + arg + "' (ignored)");
                }
            }
        }

        // Capture real stdout for the LSP stream BEFORE redirecting System.out,
        // so that OpenJML (javac) output does not corrupt the LSP wire protocol.
        PrintStream lspOut = System.out;
        System.setOut(System.err);

        var server = new OpenJMLLanguageServer();

        var launcher = LSPLauncher.createServerLauncher(server, System.in, lspOut, false, null);
        LanguageClient client = launcher.getRemoteProxy();
        server.connect(client);

        launcher.startListening().get();
    }
}
