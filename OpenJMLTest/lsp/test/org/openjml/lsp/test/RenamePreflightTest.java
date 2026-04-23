package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Direct-API tests for {@link CheckRunner#checkModifiedFiles} and
 * {@link CheckRunner#checkModifiedFilesAndGetCache}.
 *
 * <p>These methods are used by the rename flow to validate modified source
 * before applying the rename across the workspace.  Each test calls them
 * directly — no server or JSON-RPC stack needed — so they run fast despite
 * performing a full OpenJML {@code --check} pass.
 *
 * <p>Tests in this class are registered in {@link AllLspTests} and the Makefile
 * as a slow test because they invoke the OpenJML compiler.  They do NOT invoke
 * ESC or z3 and are therefore safe to run in the same process as other
 * {@code --check} tests.
 */
public class RenamePreflightTest extends LspTestBase {

    // -----------------------------------------------------------------------
    // checkModifiedFiles — no errors
    // -----------------------------------------------------------------------

    /**
     * {@code checkModifiedFiles} on a clean file must return an empty diagnostic
     * list (no errors, no warnings).
     */
    @Test
    public void testCheckModifiedFilesClean() {
        String uri    = "file:///PreflightClean.java";
        String source = "public class PreflightClean {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "}\n";
        Map<String, String> modified = Map.of(uri, source);
        List<Diagnostic> diags = CheckRunner.checkModifiedFiles(modified, new OpenJMLSettings());
        assertTrue("Expected no diagnostics for clean source; got: " + diags, diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // checkModifiedFiles — type error in modified content
    // -----------------------------------------------------------------------

    /**
     * {@code checkModifiedFiles} on a file with a type error must return at
     * least one Error-severity diagnostic.
     */
    @Test
    public void testCheckModifiedFilesWithTypeError() {
        String uri    = "file:///PreflightError.java";
        String source = "public class PreflightError {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n";
        Map<String, String> modified = Map.of(uri, source);
        List<Diagnostic> diags = CheckRunner.checkModifiedFiles(modified, new OpenJMLSettings());
        assertFalse("Expected at least one diagnostic for type error", diags.isEmpty());
        boolean hasError = diags.stream()
                .anyMatch(d -> DiagnosticSeverity.Error.equals(d.getSeverity()));
        assertTrue("Expected at least one Error-severity diagnostic", hasError);
    }

    // -----------------------------------------------------------------------
    // checkModifiedFiles — JML annotation error
    // -----------------------------------------------------------------------

    /**
     * {@code checkModifiedFiles} on a file with an invalid JML annotation must
     * return at least one Error-severity diagnostic at the annotation site.
     */
    @Test
    public void testCheckModifiedFilesWithJmlError() {
        String uri    = "file:///PreflightJmlError.java";
        String source = "public class PreflightJmlError {\n"
                + "    //@ ensures undeclaredVar >= 0;\n"
                + "    public int m() { return 1; }\n"
                + "}\n";
        Map<String, String> modified = Map.of(uri, source);
        List<Diagnostic> diags = CheckRunner.checkModifiedFiles(modified, new OpenJMLSettings());
        assertFalse("Expected diagnostics for undeclared variable in JML", diags.isEmpty());
        boolean hasError = diags.stream()
                .anyMatch(d -> DiagnosticSeverity.Error.equals(d.getSeverity()));
        assertTrue("Expected Error-severity diagnostic for JML annotation error", hasError);
    }

    // -----------------------------------------------------------------------
    // checkModifiedFilesAndGetCache — cache is populated after check
    // -----------------------------------------------------------------------

    /**
     * {@code checkModifiedFilesAndGetCache} must return a non-null result whose
     * {@link ASTCache} has at least one entry accessible via the
     * {@code tempPathToRealUri} map returned in the same result.
     *
     * <p>The cache is keyed by internal temp/mock paths, not by the original URI.
     * Callers (e.g., {@link org.openjml.lsp.Renamer}) traverse {@code tempPathToRealUri}
     * to obtain valid cache keys.
     */
    @Test
    public void testCheckModifiedFilesAndGetCachePopulated() {
        String uri    = "file:///PreflightCache.java";
        String source = "public class PreflightCache {\n"
                + "    public int identity(int x) { return x; }\n"
                + "}\n";
        Map<String, String> modified = Map.of(uri, source);
        CheckRunner.CheckAndCacheResult result =
                CheckRunner.checkModifiedFilesAndGetCache(modified, new OpenJMLSettings());
        assertNotNull("checkModifiedFilesAndGetCache must return a non-null result", result);
        assertNotNull("Result must carry a non-null ASTCache", result.cache());
        assertFalse("tempPathToRealUri must be non-empty (at least one file was processed)",
                result.tempPathToRealUri().isEmpty());
        // The AST cache is keyed by realUri (e.g. "file:///PreflightCache.java"), not by the
        // internal temp/mock-file path.  tempPathToRealUri() maps tempPath → realUri, so look
        // up the cache via the value side of the map.
        String realUri = result.tempPathToRealUri().values().iterator().next();
        assertEquals("realUri must match the original URI", uri, realUri);
        assertNotNull("ASTCache must have an entry for the processed URI", result.cache().get(realUri));
    }

    // -----------------------------------------------------------------------
    // checkModifiedFilesAndGetCache — errors present in modified content
    // -----------------------------------------------------------------------

    /**
     * {@code checkModifiedFilesAndGetCache} on a file with a type error must
     * still return a result (non-null), and that result's diagnostic list must
     * contain at least one Error-severity entry.
     */
    @Test
    public void testCheckModifiedFilesAndGetCacheWithErrors() {
        String uri    = "file:///PreflightCacheErr.java";
        String source = "public class PreflightCacheErr {\n"
                + "    public int m() { return \"wrong\"; }\n"
                + "}\n";
        Map<String, String> modified = Map.of(uri, source);
        CheckRunner.CheckAndCacheResult result =
                CheckRunner.checkModifiedFilesAndGetCache(modified, new OpenJMLSettings());
        assertNotNull("checkModifiedFilesAndGetCache must return a non-null result", result);
        List<Diagnostic> diags = result.diagnostics();
        assertFalse("Expected diagnostics for type error", diags.isEmpty());
        boolean hasError = diags.stream()
                .anyMatch(d -> DiagnosticSeverity.Error.equals(d.getSeverity()));
        assertTrue("Expected Error-severity diagnostic", hasError);
    }
}
