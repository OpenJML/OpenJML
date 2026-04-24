package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.util.List;
import java.util.Map;

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
     * Convert a {@link File} to a {@code file://} URI string using the three-slash
     * form ({@code file:///path}) that the LSP server uses internally.
     *
     * <p>Use this in preference to {@link File#toURI()} which may produce a
     * single-slash form ({@code file:/path}) that fails {@code equals} comparisons
     * against server-side URI keys.
     */
    protected static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    /**
     * Run an OpenJML {@code --check} pass on the given source content and
     * return the resulting LSP diagnostics.
     */
    protected List<Diagnostic> checkContent(String uri, String content) {
        return CheckRunner.check(uri, content).diagnostics();
    }

    /**
     * Run an OpenJML {@code --esc} pass on the given source content and
     * return the full {@link CheckRunner.CheckResult} (diagnostics + proof results + exit code).
     */
    protected CheckRunner.CheckResult runEscResult(String uri, String content) {
        return CheckRunner.runEsc(uri, content);
    }

    /**
     * Run an OpenJML {@code --esc} pass on the given source content and
     * return the resulting LSP diagnostics.
     */
    protected List<Diagnostic> runEscContent(String uri, String content) {
        return CheckRunner.runEsc(uri, content).diagnostics();
    }

    /**
     * Run an OpenJML {@code --esc} pass on a primary file together with
     * additional context source files (e.g. dependencies), and return the
     * full {@link CheckRunner.CheckResult}.  Only diagnostics from the
     * primary file are included; type errors in the extra files cause
     * exit code 1 and prevent ESC from running.
     */
    protected CheckRunner.CheckResult runEscWithSources(String primaryUri,
                                                         String primaryContent,
                                                         Map<String, String> extraSources) {
        return CheckRunner.runEscWithSources(primaryUri, primaryContent, extraSources);
    }

    /**
     * Run an OpenJML {@code --esc} pass restricted to a single method and
     * return the full {@link CheckRunner.CheckResult}.
     */
    protected CheckRunner.CheckResult runEscMethodResult(String uri, String content,
                                                          String methodName) {
        return CheckRunner.runEscMethod(uri, content, methodName);
    }

    /**
     * Run an OpenJML {@code --esc} pass restricted to a single method and
     * return the resulting LSP diagnostics.
     *
     * @param methodName fully-qualified method name for {@code --method}
     *                   (e.g. {@code "ClassName.methodName"})
     */
    protected List<Diagnostic> runEscContentMethod(String uri, String content, String methodName) {
        return CheckRunner.runEscMethod(uri, content, methodName).diagnostics();
    }

    // --- doESC API path helpers ---

    /**
     * Run {@code --check} on the given content, populating the AST cache with an IAPI,
     * then run in-process doESC on all methods via {@link CheckRunner#runDoEscFile}.
     */
    protected CheckRunner.CheckResult runDoEscFileResult(String uri, String content) {
        // --check must succeed first so the IAPI is stored in the cache.
        CheckRunner.CheckResult check = CheckRunner.check(uri, content);
        if (check.exitCode() != 0) return check;
        return CheckRunner.runDoEscFile(uri, new OpenJMLSettings());
    }

    /**
     * Run {@code --check} on the given content, then run in-process doESC on a
     * single method via {@link CheckRunner#runDoEscMethod}.
     *
     * @param methodName simple or fully-qualified method name
     */
    protected CheckRunner.CheckResult runDoEscMethodResult(String uri, String content,
                                                            String methodName) {
        CheckRunner.CheckResult check = CheckRunner.check(uri, content);
        if (check.exitCode() != 0) return check;
        return CheckRunner.runDoEscMethod(uri, methodName, new OpenJMLSettings());
    }

}
