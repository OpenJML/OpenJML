package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Corner-case tests for the mock-file path in {@link CheckRunner#runCheckDirWithContext}.
 *
 * <p>Each test exercises a scenario that is not covered by the main
 * {@link CheckRunnerDirTest} suite:
 * <ul>
 *   <li>A file that exists only in the snapshot with no on-disk counterpart.</li>
 *   <li>A dirty {@code .jml} companion alongside a clean {@code .java} on disk.</li>
 *   <li>Two dirty {@code .java} files in the same check invocation.</li>
 * </ul>
 *
 * <p>All tests run with {@link CheckRunner#useMockFiles} {@code = true} (the default).
 */
public class MockFileCornerCasesTest extends LspTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    /** Write {@code content} to a new file named {@code filename} in the temp folder. */
    private File writeFile(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    /** Three-slash {@code file:///} URI that matches the form CheckRunner uses internally. */
    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    /** Build a {@code file:///} URI for an arbitrary absolute path (may not exist on disk). */
    private static String fileUri(Path p) {
        return p.toUri().toString();
    }

    // -----------------------------------------------------------------------
    // Mock-only file: snapshot entry whose path does not exist on disk
    // -----------------------------------------------------------------------

    /**
     * When a snapshot entry's path does not exist on disk,
     * {@link CheckRunner#runCheckDirWithContext} must still compile the
     * in-memory content via the mock-file interception path.
     *
     * <p>This validates that the {@code JmlArguments} URI-matching logic
     * intercepts the path argument before {@code Option.SOURCEFILE.process()}
     * attempts a {@code Files.exists()} check on the non-existent path.
     */
    @Test
    public void testMockOnlyFile_NoCounterpartOnDisk() {
        // Construct a path that does not exist on disk.
        Path nonExistentPath = tmp.getRoot().toPath().resolve("MockOnly.java");
        assertFalse("Precondition: path must not exist on disk",
                nonExistentPath.toFile().exists());

        // Content with a type error - so we can detect it was compiled.
        String mockContent =
                "public class MockOnly {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";

        Map<String, String> snapshot = Map.of(fileUri(nonExistentPath), mockContent);

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(nonExistentPath.toString()), snapshot, new OpenJMLSettings());

        // The mock content has a type error - expect at least one diagnostic.
        boolean hasError = result.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertTrue("Expected diagnostics from mock-only file content", hasError);

        // Diagnostic keys must not reference temp paths.
        for (String key : result.diagnosticsByUri().keySet()) {
            assertFalse("Diagnostic key must not be a temp-dir path: " + key,
                    key.contains("openjml-lsp-check-"));
        }
    }

    // -----------------------------------------------------------------------
    // Dirty .jml companion alongside a clean .java on disk
    // -----------------------------------------------------------------------

    /**
     * When the snapshot contains a dirty {@code .jml} companion file while the
     * corresponding {@code .java} is clean on disk, the mock-file path must
     * substitute the dirty {@code .jml} content.
     *
     * <p>A {@code .jml} file with an undefined identifier in a {@code requires}
     * clause will produce a type-check error when used; the clean on-disk
     * {@code .jml} (empty spec) would produce no error.  Seeing a diagnostic
     * confirms the dirty {@code .jml} was used rather than the clean disk version.
     */
    @Test
    public void testDirtyJmlCompanion_AlongCleanJava() throws IOException {
        // Clean .java file on disk.
        File javaFile = writeFile("DirtyJmlCompanion.java",
                "public class DirtyJmlCompanion {\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n");

        // Clean .jml file on disk (no JML content - produces no diagnostics).
        File jmlFile = writeFile("DirtyJmlCompanion.jml",
                "public class DirtyJmlCompanion {\n" +
                "}\n");

        // Dirty .jml in snapshot: introduces an undefined identifier error.
        String dirtyJml =
                "public class DirtyJmlCompanion {\n" +
                "    //@ requires unknownIdentifier > 0;\n" +
                "    public int m(int x);\n" +
                "}\n";

        // Snapshot only contains the dirty .jml; the .java is clean on disk.
        Map<String, String> snapshot = Map.of(fileUri(jmlFile), dirtyJml);

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(javaFile.getAbsolutePath()), snapshot, new OpenJMLSettings());

        // The dirty .jml has an undefined identifier - expect a diagnostic.
        boolean hasError = result.diagnosticsByUri().values().stream()
                .anyMatch(d -> !d.isEmpty());
        assertTrue("Expected diagnostic from dirty .jml companion content", hasError);
    }

    // -----------------------------------------------------------------------
    // Two dirty .java files in the same check invocation
    // -----------------------------------------------------------------------

    /**
     * When the snapshot contains two dirty {@code .java} files and both are
     * passed to {@link CheckRunner#runCheckDirWithContext}, both must be compiled
     * from the snapshot rather than disk.
     *
     * <p>Both disk files are clean; both snapshot versions introduce type errors.
     * We verify that diagnostics appear for both files.
     */
    @Test
    public void testMultipleDirtyFiles_BothSubstituted() throws IOException {
        // Both disk files are clean.
        File fileA = writeFile("MultiDirtyA.java",
                "public class MultiDirtyA {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n");
        File fileB = writeFile("MultiDirtyB.java",
                "public class MultiDirtyB {\n" +
                "    public int sub(int a, int b) { return a - b; }\n" +
                "}\n");

        // Both snapshot versions have type errors.
        String dirtyA =
                "public class MultiDirtyA {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";
        String dirtyB =
                "public class MultiDirtyB {\n" +
                "    public int m() { return \"also not an int\"; }\n" +
                "}\n";

        Map<String, String> snapshot = Map.of(
                fileUri(fileA), dirtyA,
                fileUri(fileB), dirtyB);

        CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(
                List.of(fileA.getAbsolutePath(), fileB.getAbsolutePath()),
                snapshot, new OpenJMLSettings());

        boolean aHasError = false, bHasError = false;
        for (Map.Entry<String, List<Diagnostic>> e : result.diagnosticsByUri().entrySet()) {
            if (e.getKey().contains("MultiDirtyA") && !e.getValue().isEmpty()) aHasError = true;
            if (e.getKey().contains("MultiDirtyB") && !e.getValue().isEmpty()) bHasError = true;
        }
        assertTrue("Expected error in MultiDirtyA.java from dirty snapshot", aHasError);
        assertTrue("Expected error in MultiDirtyB.java from dirty snapshot", bHasError);
    }
}
