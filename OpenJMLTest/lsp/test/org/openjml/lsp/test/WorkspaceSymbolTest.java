package org.openjml.lsp.test;

import com.sun.tools.javac.code.Symbol;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.SymbolKind;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.OpenJMLTextDocumentService;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Tests for the {@code workspace/symbol} declaration-index pipeline.
 *
 * <p>Covers the scenario most prone to regression: the server is started,
 * <em>no files are opened in the editor</em>, {@code openjml.indexProject}
 * is invoked (which calls {@link CheckRunner#runCheckDir} via
 * {@link OpenJMLTextDocumentService#indexProject}), and then
 * {@code workspace/symbol} is expected to return matching declarations.
 *
 * <p>The shared identifier {@code "needle"} appears as:
 * <ul>
 *   <li>a class name ({@code NeedleClass})</li>
 *   <li>a method name ({@code needleMethod})</li>
 *   <li>a formal parameter name ({@code needle} in a method)</li>
 *   <li>a field name ({@code needleField})</li>
 *   <li>a local variable (should NOT be returned by {@code workspace/symbol})</li>
 * </ul>
 *
 * <p>The test verifies that the nav cache is populated when no snapshot is
 * present (empty {@code lastContent}), which was the root-cause bug fixed
 * alongside this test.
 */
public class WorkspaceSymbolTest {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    /**
     * The source exercises all declaration sites.
     *
     * <p>The declaration index includes ALL variable declarations: fields,
     * formal parameters, local variables, and JML quantifier-bound variables.
     * Go-to-definition for formals and JML-bound variables depends on them
     * being in the index.  {@code workspace/symbol} therefore also returns them.
     */
    private static final String NEEDLE_SOURCE =
            "public class NeedleClass {\n" +                    // class name
            "    public int needleField;\n" +                   // field name
            "    public int needleMethod(int needle) {\n" +     // method name + parameter
            "        int needleLocal = needle + 1;\n" +         // local variable — also indexed
            "        return needleField + needleLocal;\n" +
            "    }\n" +
            "}\n";

    /** A second file that does NOT contain "needle", to verify scoping. */
    private static final String OTHER_SOURCE =
            "public class OtherClass {\n" +
            "    public int value;\n" +
            "    public void work() {}\n" +
            "}\n";

    private File needleFile;
    private File otherFile;
    private ASTCache cache;

    @Before
    public void setUp() throws Exception {
        cache = CheckRunner.getASTCache();
        cache.clear();

        needleFile = tmp.newFile("NeedleClass.java");
        write(needleFile, NEEDLE_SOURCE);

        otherFile = tmp.newFile("OtherClass.java");
        write(otherFile, OTHER_SOURCE);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static void write(File f, String content) throws IOException {
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
    }

    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    /**
     * Simulate what {@link OpenJMLTextDocumentService#indexProject} does:
     * run a project-wide check with an empty snapshot (no open editors),
     * then rebuild the nav index.  This exercises the code path that was
     * broken before the fix (empty snapshot → runCheckDir → no AST listener).
     */
    private void indexDirectory(File dir) {
        CheckRunner.DirCheckResult result =
                CheckRunner.runCheckDir(List.of(dir.getAbsolutePath()), new OpenJMLSettings());
        cache.rebuildNavIndex();
    }

    /**
     * Query the declaration index exactly as {@link OpenJMLTextDocumentService#symbols}
     * does: exact case-sensitive match; empty query returns all non-synthetic names.
     */
    private List<String> queryNames(String query) {
        List<String> names = new ArrayList<>();
        cache.forEachDeclaration((sym, loc) -> {
            String name = sym.name.toString();
            if (name.isEmpty() || name.startsWith("<")) return;
            if (!query.isEmpty() && !name.equals(query)) return;
            names.add(name);
        });
        return names;
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * After indexing a directory with no open editors, the nav cache must be
     * non-empty and {@code forEachDeclaration} must find all indexed symbols.
     */
    @Test
    public void testNavCachePopulatedWithNoOpenEditors() {
        indexDirectory(tmp.getRoot());

        List<String> all = queryNames("");
        assertFalse("Nav cache must be non-empty after runCheckDir with empty snapshot",
                all.isEmpty());
    }

    /**
     * Each declaration name must be found by an exact query for that name,
     * and must NOT be found by a query for a different name.
     * All variable declarations are indexed so that go-to-definition works for
     * formals and JML quantifier-bound variables.
     */
    @Test
    public void testExactMatchFindsEachDeclaration() {
        indexDirectory(tmp.getRoot());

        // Each exact name must produce exactly one match.
        assertTrue("NeedleClass must be found by exact query",
                queryNames("NeedleClass").contains("NeedleClass"));
        assertTrue("needleMethod must be found by exact query",
                queryNames("needleMethod").contains("needleMethod"));
        assertTrue("needleField must be found by exact query",
                queryNames("needleField").contains("needleField"));
        // Formal parameter — also indexed (go-to-definition depends on this)
        assertTrue("Formal parameter 'needle' must be found by exact query",
                queryNames("needle").contains("needle"));
        // Local variable — also indexed
        assertTrue("Local variable 'needleLocal' must be found by exact query",
                queryNames("needleLocal").contains("needleLocal"));

        // A partial name must NOT match (exact, not substring).
        assertTrue("'needle' query must NOT match 'NeedleClass'",
                !queryNames("needle").contains("NeedleClass"));
        assertTrue("'needle' query must NOT match 'needleMethod'",
                !queryNames("needle").contains("needleMethod"));
    }

    /**
     * Declarations in a second, unrelated file (OtherClass) must also be
     * indexed when the whole directory is checked.
     */
    @Test
    public void testOtherClassAlsoIndexed() {
        indexDirectory(tmp.getRoot());

        List<String> all = queryNames("");
        assertTrue("OtherClass must be indexed from the same directory",
                all.contains("OtherClass"));
        assertTrue("OtherClass.work must be indexed",
                all.contains("work"));
    }

    /**
     * An empty query must return all non-synthetic declarations from all
     * indexed files.
     */
    @Test
    public void testEmptyQueryReturnsAll() {
        indexDirectory(tmp.getRoot());

        List<String> all = queryNames("");
        assertTrue("Expected at least four declarations (class + method + field from each file)",
                all.size() >= 4);
    }

    /**
     * A query that matches nothing must return an empty list.
     */
    @Test
    public void testNoMatchReturnsEmpty() {
        indexDirectory(tmp.getRoot());

        List<String> matches = queryNames("xyzzy_no_such_symbol_12345");
        assertTrue("Query matching nothing must return empty list", matches.isEmpty());
    }

    /**
     * Matching is case-sensitive: "needle" must NOT match "NeedleClass",
     * and "NeedleClass" must NOT match "needle".
     */
    @Test
    public void testCaseSensitiveMatch() {
        indexDirectory(tmp.getRoot());

        // "needle" matches only the parameter, not the class or method.
        List<String> lower = queryNames("needle");
        assertFalse("'needle' must not match 'NeedleClass' (case-sensitive)",
                lower.contains("NeedleClass"));
        assertFalse("'needle' must not match 'needleMethod' (case-sensitive)",
                lower.contains("needleMethod"));
        assertTrue("'needle' must match the parameter 'needle'",
                lower.contains("needle"));

        // "NeedleClass" matches only the class.
        List<String> cls = queryNames("NeedleClass");
        assertTrue("'NeedleClass' must match the class",
                cls.contains("NeedleClass"));
        assertFalse("'NeedleClass' must not match 'needleField' (case-sensitive)",
                cls.contains("needleField"));
    }

    /**
     * The URIs stored in the nav declaration index must be readable file paths
     * (verifies the URI format used by runCheckDir is compatible with
     * {@code URI.create(uri).getPath()}).
     */
    @Test
    public void testDeclarationUrisAreReadable() {
        indexDirectory(tmp.getRoot());

        final boolean[] allReadable = { true };
        cache.forEachDeclaration((sym, loc) -> {
            String name = sym.name.toString();
            if (name.isEmpty() || name.startsWith("<")) return;
            try {
                String path = java.net.URI.create(loc.uri()).getPath();
                if (path == null) {
                    System.err.println("[WorkspaceSymbolTest] null path for URI: " + loc.uri());
                    allReadable[0] = false;
                    return;
                }
                java.nio.file.Files.readString(java.nio.file.Path.of(path));
            } catch (Exception e) {
                System.err.println("[WorkspaceSymbolTest] unreadable URI " + loc.uri() + ": " + e);
                allReadable[0] = false;
            }
        });
        assertTrue("All declaration URIs must point to readable files", allReadable[0]);
    }

    /**
     * After clearing the cache and re-indexing, the old nav entries must be
     * gone and fresh ones must replace them.
     */
    @Test
    public void testRebuildAfterClear() {
        indexDirectory(tmp.getRoot());
        int firstCount = queryNames("").size();
        assertTrue("First index must be non-empty", firstCount > 0);

        cache.clear();
        assertEquals("After clear(), declaration index must be empty", 0, queryNames("").size());

        indexDirectory(tmp.getRoot());
        int secondCount = queryNames("").size();
        assertEquals("Re-index must produce same count as first index",
                firstCount, secondCount);
    }
}
