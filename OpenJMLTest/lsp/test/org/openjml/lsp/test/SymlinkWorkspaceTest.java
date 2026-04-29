package org.openjml.lsp.test;

import com.google.gson.JsonObject;
import org.junit.*;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;

import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests that the LSP server correctly handles workspace directories that
 * contain or are OS-level symlinks, specifically when the file-based mock
 * path ({@code runCheckDirWithContext}) is active.
 *
 * <p>The mock path is used when the edit snapshot is non-empty (at least one
 * file has unsaved edits).  In that case the server calls {@code Files.walk}
 * to collect all project source files.  Without {@code FOLLOW_LINKS},
 * {@code Files.walk} silently skips symlinked directories and misses the files
 * inside them.
 *
 * <p>Each test uses {@code checkTriggerOn:"manual"} to suppress automatic
 * single-file checks, then sends a {@code didChange} notification to make the
 * snapshot non-empty, then triggers {@code openjml.indexProject} which calls
 * {@code runCheckDirWithContext} (the code path under test).
 *
 * <p>Exercises:
 * <ul>
 *   <li>Files inside a symlink subdirectory are found during project check</li>
 *   <li>A symlink cycle does not cause an infinite loop</li>
 *   <li>A workspace root that is itself a symlink is entered correctly</li>
 *   <li>Multiple disjoint roots (linked-folder simulation) are all checked</li>
 * </ul>
 */
public class SymlinkWorkspaceTest extends ProtocolTestBase {

    // Source with a type error so OpenJML reports a diagnostic we can detect.
    private static final String TYPE_ERROR_SOURCE =
            "public class %s {\n    public int m() { return \"not an int\"; }\n}\n";
    // Source that is syntactically valid (no errors).
    private static final String VALID_SOURCE = "public class %s { }\n";

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    @After
    @Override
    public void tearDown() {
        super.tearDown();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String escapeContent(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"")
                .replace("\n", "\\n").replace("\r", "");
    }

    /**
     * Configure the project with {@code checkTriggerOn:"manual"} so that
     * automatic single-file checks do not fire on {@code didChange}.  The
     * only check that runs is the explicit {@code openjml.indexProject} command.
     */
    private void configureRoots(String... osPaths) throws Exception {
        StringBuilder sb = new StringBuilder("[");
        for (int i = 0; i < osPaths.length; i++) {
            if (i > 0) sb.append(",");
            sb.append("\"").append(jsonEscape(osPaths[i])).append("\"");
        }
        sb.append("]");
        String settings = "{\"openjml\":{\"checkTriggerOn\":\"manual\","
                + "\"projects\":[{\"id\":\"__workspace__\","
                + "\"rootPaths\":" + sb + "}]}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settings + "}");
        Thread.sleep(200);
    }

    /** Send {@code textDocument/didChange} to mark a file as dirty (non-empty snapshot). */
    private void didChange(String uri, String content) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":2},"
                + "\"contentChanges\":[{\"text\":\"" + escapeContent(content) + "\"}]}";
        client.sendNotification("textDocument/didChange", params);
        Thread.sleep(100);
    }

    private static void trySymlink(Path link, Path target) {
        try {
            Files.createSymbolicLink(link, target);
        } catch (UnsupportedOperationException | java.io.IOException e) {
            Assume.assumeNoException("Filesystem does not support symlinks — test skipped", e);
        }
    }

    private static String fileUri(Path p) {
        return p.toUri().toString();
    }

    /**
     * Wait until non-empty diagnostics have arrived for ALL of the given
     * URI fragments.  Consumes notifications until all fragments are satisfied
     * or the timeout expires.
     */
    private void waitForAllNonEmptyDiags(long timeout, TimeUnit unit, String... fragments)
            throws InterruptedException {
        java.util.Set<String> remaining = new java.util.HashSet<>(java.util.Arrays.asList(fragments));
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (!remaining.isEmpty()) {
            long r = deadline - System.nanoTime();
            if (r <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", r, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject p = msg.getAsJsonObject("params");
            String uri = p.get("uri").getAsString();
            if (p.getAsJsonArray("diagnostics").isEmpty()) continue;
            remaining.removeIf(uri::contains);
        }
        assertTrue("Expected diagnostics not received for: " + remaining, remaining.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * Files inside a symlink subdirectory of the workspace root must be found
     * and compiled during a project-wide {@code openjml.indexProject} run when
     * the edit snapshot is non-empty.
     *
     * <p>Without {@code FileVisitOption.FOLLOW_LINKS} in {@code Files.walk},
     * symlink directories are not entered and the files inside them are silently
     * missed, producing no diagnostics.
     *
     * <p>Layout:
     * <pre>
     *   projDir/
     *     Sentinel.java  (valid — makes snapshot non-empty when dirty)
     *     link  ->  realSrc/
     *   realSrc/
     *     LinkedError.java  (type error — must be diagnosed)
     * </pre>
     */
    @Test
    public void testFilesInSymlinkSubdirAreChecked() throws Exception {
        Path rootDir = tmp.getRoot().toPath().toRealPath();

        // realSrc/LinkedError.java has a type error — the file to detect.
        Path realSrc = rootDir.resolve("realSrc");
        Files.createDirectories(realSrc);
        Files.writeString(realSrc.resolve("LinkedError.java"),
                String.format(TYPE_ERROR_SOURCE, "LinkedError"), StandardCharsets.UTF_8);

        // projDir/ is the workspace root with a sentinel file and a symlink subdir.
        Path projDir = rootDir.resolve("proj");
        Files.createDirectories(projDir);
        Files.writeString(projDir.resolve("Sentinel.java"),
                String.format(VALID_SOURCE, "Sentinel"), StandardCharsets.UTF_8);
        trySymlink(projDir.resolve("link"), realSrc);

        configureRoots(projDir.toString());

        // Make the snapshot non-empty: Sentinel.java is dirty.
        // checkTriggerOn:"manual" means no automatic single-file check fires.
        didChange(fileUri(projDir.resolve("Sentinel.java")),
                String.format(VALID_SOURCE, "Sentinel"));

        // Trigger the project-wide check that uses Files.walk.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT + "\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // LinkedError.java is inside the symlink subdir — must be found and checked.
        assertNotNull("Files inside a symlink subdirectory must be checked",
                nextNonEmptyDiagsFor("LinkedError", TIMEOUT_SECONDS, TimeUnit.SECONDS));
    }

    /**
     * A symlink cycle inside the workspace must not cause an infinite loop.
     * The check must complete within the timeout and files discovered before
     * the cycle must produce diagnostics.
     *
     * <p>Layout:
     * <pre>
     *   projDir/
     *     Sentinel.java  (valid — makes snapshot non-empty)
     *     sub  ->  cycleDir/
     *   cycleDir/
     *     CycleMarker.java  (type error)
     *     loop  ->  cycleDir/  (self-referential cycle)
     * </pre>
     */
    @Test
    public void testSymlinkCycleDoesNotHang() throws Exception {
        Path rootDir = tmp.getRoot().toPath().toRealPath();

        // cycleDir contains CycleMarker.java and a self-referential cycle.
        Path cycleDir = rootDir.resolve("cycleDir");
        Files.createDirectories(cycleDir);
        Files.writeString(cycleDir.resolve("CycleMarker.java"),
                String.format(TYPE_ERROR_SOURCE, "CycleMarker"), StandardCharsets.UTF_8);
        trySymlink(cycleDir.resolve("loop"), cycleDir);

        // projDir/ is the workspace root: Sentinel.java (real) + sub -> cycleDir/.
        Path projDir = rootDir.resolve("proj2");
        Files.createDirectories(projDir);
        Files.writeString(projDir.resolve("Sentinel.java"),
                String.format(VALID_SOURCE, "Sentinel"), StandardCharsets.UTF_8);
        trySymlink(projDir.resolve("sub"), cycleDir);

        configureRoots(projDir.toString());

        // Make the snapshot non-empty.
        didChange(fileUri(projDir.resolve("Sentinel.java")),
                String.format(VALID_SOURCE, "Sentinel"));

        // Trigger the project-wide check.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT + "\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Must complete within TIMEOUT_SECONDS (no infinite loop).
        // CycleMarker.java must be found before the cycle is hit.
        assertNotNull("Check must complete despite symlink cycle — CycleMarker.java not found",
                nextNonEmptyDiagsFor("CycleMarker", TIMEOUT_SECONDS, TimeUnit.SECONDS));
    }

    /**
     * A workspace root that is itself a symlink must be entered correctly.
     *
     * <p>Without {@code FOLLOW_LINKS}, {@code Files.walk(symlinkRoot)} returns
     * only the directory entry for the symlink itself and does not recurse into
     * it, so all files inside the workspace are missed.
     *
     * <p>Layout:
     * <pre>
     *   realRoot/
     *     RootError.java  (type error — must be diagnosed)
     *   linkRoot  ->  realRoot/  (workspace root is a symlink)
     * </pre>
     */
    @Test
    public void testSymlinkWorkspaceRoot() throws Exception {
        Path rootDir = tmp.getRoot().toPath().toRealPath();

        Path realRoot = rootDir.resolve("realRoot");
        Files.createDirectories(realRoot);
        Files.writeString(realRoot.resolve("RootError.java"),
                String.format(TYPE_ERROR_SOURCE, "RootError"), StandardCharsets.UTF_8);

        // linkRoot -> realRoot/  (the workspace root itself is a symlink)
        Path linkRoot = rootDir.resolve("linkRoot");
        trySymlink(linkRoot, realRoot);

        // Configure root as the symlink path.
        configureRoots(linkRoot.toString());

        // Make the snapshot non-empty using the file accessed via the symlink path.
        didChange(fileUri(linkRoot.resolve("RootError.java")),
                String.format(TYPE_ERROR_SOURCE, "RootError"));

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT + "\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        assertNotNull("Files under a symlink workspace root must be found and checked",
                nextNonEmptyDiagsFor("RootError", TIMEOUT_SECONDS, TimeUnit.SECONDS));
    }

    /**
     * Multiple disjoint workspace roots (simulating Eclipse linked folders
     * configured as separate source roots) must all be checked in a single
     * {@code openjml.indexProject} run.
     *
     * <p>This test uses only real directories (no OS symlinks) and verifies
     * that the multi-root walk works correctly when the snapshot is non-empty.
     */
    @Test
    public void testMultipleDisjointRootsAreAllChecked() throws Exception {
        Path rootDir = tmp.getRoot().toPath().toRealPath();

        Path root1 = rootDir.resolve("root1");
        Path root2 = rootDir.resolve("root2");
        Files.createDirectories(root1);
        Files.createDirectories(root2);

        Files.writeString(root1.resolve("Alpha.java"),
                String.format(TYPE_ERROR_SOURCE, "Alpha"), StandardCharsets.UTF_8);
        Files.writeString(root2.resolve("Beta.java"),
                String.format(TYPE_ERROR_SOURCE, "Beta"), StandardCharsets.UTF_8);

        configureRoots(root1.toString(), root2.toString());

        // Make the snapshot non-empty by marking Alpha.java as dirty.
        didChange(fileUri(root1.resolve("Alpha.java")),
                String.format(TYPE_ERROR_SOURCE, "Alpha"));

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT + "\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        waitForAllNonEmptyDiags(TIMEOUT_SECONDS, TimeUnit.SECONDS, "Alpha", "Beta");
    }
}
