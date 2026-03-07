package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.openjml.lsp.CheckRunner;

import java.util.List;

/**
 * Base class for LSP diagnostic tests.
 *
 * Tests call {@link CheckRunner#check} directly, exercising:
 * <ul>
 *   <li>OpenJML API invocation ({@code IAPI.execute("--check", ...)})</li>
 *   <li>Diagnostic collection ({@link org.openjml.lsp.LspDiagnosticListener})</li>
 *   <li>Conversion to LSP format ({@link org.openjml.lsp.DiagnosticConverter})</li>
 * </ul>
 * The LSP4J protocol layer (JSON-RPC framing, stdio transport) is exercised
 * end-to-end via the {@code openjml-lsp} launcher script.
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
