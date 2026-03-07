package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.openjml.lsp.CheckRunner;

import java.util.List;

/**
 * Base class for LSP diagnostic tests.
 *
 * Note on test architecture: the full in-process LSP4J {@code Launcher}
 * approach (piped stdin/stdout, JSON-RPC handshake) cannot currently be used
 * because jdk.compiler bundles Gson 2.11.0 internally while LSP4J 0.21.1
 * requires an older Gson API — the two are incompatible in the same JVM.
 *
 * Instead, tests call {@link CheckRunner#check} directly.  This exercises all
 * the meaningful parts of the stack:
 * <ul>
 *   <li>OpenJML API invocation ({@code IAPI.execute("--check", ...)})</li>
 *   <li>Diagnostic collection ({@link org.openjml.lsp.LspDiagnosticListener})</li>
 *   <li>Conversion to LSP format ({@link org.openjml.lsp.DiagnosticConverter})</li>
 * </ul>
 * The LSP4J protocol layer (JSON-RPC framing, stdio transport) is tested
 * separately via the {@code openjml-lsp} launcher script.
 */
public abstract class LspTestBase {

    /**
     * Run an OpenJML {@code --check} pass on the given source content and
     * return the resulting LSP diagnostics.
     *
     * @param uri     a document URI, e.g. {@code "file:///com/example/MyClass.java"}
     * @param content Java/JML source text
     * @return the list of LSP Diagnostics reported by OpenJML
     */
    protected List<Diagnostic> checkContent(String uri, String content) {
        return CheckRunner.check(uri, content);
    }
}
