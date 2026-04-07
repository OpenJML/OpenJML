package org.openjml.lsp.test;

import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.FileChangeType;
import org.eclipse.lsp4j.FileEvent;
import org.junit.Test;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.OpenJMLWorkspaceService;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.Assert.*;

/**
 * Tests for the {@code workspace/didChangeWatchedFiles} infrastructure:
 * <ul>
 *   <li>{@link OpenJMLSettings#effectiveRoots()} — picks {@code jmlWorkspaceRoots}
 *       over {@code workspaceFolderPaths}, falls back gracefully.</li>
 *   <li>{@link OpenJMLSettings} copy constructor includes {@code jmlWorkspaceRoots}.</li>
 *   <li>{@link OpenJMLWorkspaceService#didChangeConfiguration} — {@code jmlWorkspaceRoots}
 *       change triggers the watcher-reregistrar; unchanged value does not.</li>
 *   <li>{@link OpenJMLWorkspaceService#didChangeWatchedFiles} — routes {@code .jml} and
 *       {@code .java} events to the correct handlers, and filters events outside the
 *       effective roots.</li>
 * </ul>
 */
public class WatchedFilesTest {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Path separator used to join roots. */
    private static final String SEP = File.pathSeparator;

    /**
     * Build an {@link OpenJMLWorkspaceService} wired to simple lambda counters.
     * Returned lists capture every (uri, type) pair received by each handler.
     */
    private static class TestSetup {
        final OpenJMLSettings settings = new OpenJMLSettings();
        final List<String[]> jmlCalls  = new ArrayList<>();
        final List<String[]> javaCalls = new ArrayList<>();
        final AtomicInteger reregistrations = new AtomicInteger();
        final OpenJMLWorkspaceService svc;

        TestSetup() {
            svc = new OpenJMLWorkspaceService(settings, null, null,
                    (uri, type) -> jmlCalls.add(new String[]{uri, type.toString()}),
                    (uri, type) -> javaCalls.add(new String[]{uri, type.toString()}),
                    reregistrations::incrementAndGet);
        }
    }

    /** Fire a single {@code didChangeWatchedFiles} event. */
    private static void fireEvent(OpenJMLWorkspaceService svc,
                                   String uri, FileChangeType type) {
        FileEvent event = new FileEvent(uri, type);
        DidChangeWatchedFilesParams params = new DidChangeWatchedFilesParams(List.of(event));
        svc.didChangeWatchedFiles(params);
    }

    // -----------------------------------------------------------------------
    // effectiveRoots()
    // -----------------------------------------------------------------------

    @Test
    public void effectiveRootsUsesJmlWorkspaceRootsWhenSet() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.jmlWorkspaceRoots    = "/a" + SEP + "/b";
        s.workspaceFolderPaths = "/c";
        List<String> roots = s.effectiveRoots();
        assertEquals(2, roots.size());
        assertEquals("/a", roots.get(0));
        assertEquals("/b", roots.get(1));
    }

    @Test
    public void effectiveRootsFallsBackToWorkspaceFolderPaths() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.jmlWorkspaceRoots    = null;
        s.workspaceFolderPaths = "/x" + SEP + "/y";
        List<String> roots = s.effectiveRoots();
        assertEquals(2, roots.size());
        assertEquals("/x", roots.get(0));
        assertEquals("/y", roots.get(1));
    }

    @Test
    public void effectiveRootsEmptyWhenBothNull() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.jmlWorkspaceRoots    = null;
        s.workspaceFolderPaths = null;
        assertTrue(s.effectiveRoots().isEmpty());
    }

    @Test
    public void effectiveRootsIgnoresBlankJmlWorkspaceRoots() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.jmlWorkspaceRoots    = "   ";
        s.workspaceFolderPaths = "/fallback";
        List<String> roots = s.effectiveRoots();
        assertEquals(1, roots.size());
        assertEquals("/fallback", roots.get(0));
    }

    // -----------------------------------------------------------------------
    // Copy constructor includes jmlWorkspaceRoots
    // -----------------------------------------------------------------------

    @Test
    public void copyConstructorCopiesJmlWorkspaceRoots() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.jmlWorkspaceRoots = "/proj/a" + SEP + "/proj/b";

        OpenJMLSettings copy = new OpenJMLSettings(orig);
        assertEquals(orig.jmlWorkspaceRoots, copy.jmlWorkspaceRoots);

        // Mutation of copy must not affect original.
        copy.jmlWorkspaceRoots = "/other";
        assertEquals("/proj/a" + SEP + "/proj/b", orig.jmlWorkspaceRoots);
    }

    // -----------------------------------------------------------------------
    // applyUpdate() — watcher reregistrar
    // -----------------------------------------------------------------------

    @Test
    public void applyUpdateTriggersReregistrarOnRootsChange() {
        TestSetup ts = new TestSetup();
        ts.settings.jmlWorkspaceRoots = "/old";

        // Send didChangeConfiguration with a new jmlWorkspaceRoots value.
        String json = "{\"openjml\":{\"jmlWorkspaceRoots\":\"/new\"}}";
        org.eclipse.lsp4j.DidChangeConfigurationParams params =
                new org.eclipse.lsp4j.DidChangeConfigurationParams(
                        com.google.gson.JsonParser.parseString(json));
        ts.svc.didChangeConfiguration(params);

        assertEquals("Reregistrar must be called once when roots change",
                1, ts.reregistrations.get());
        assertEquals("/new", ts.settings.jmlWorkspaceRoots);
    }

    @Test
    public void applyUpdateDoesNotTriggerReregistrarWhenRootsUnchanged() {
        TestSetup ts = new TestSetup();
        ts.settings.jmlWorkspaceRoots = "/same";

        String json = "{\"openjml\":{\"jmlWorkspaceRoots\":\"/same\"}}";
        org.eclipse.lsp4j.DidChangeConfigurationParams params =
                new org.eclipse.lsp4j.DidChangeConfigurationParams(
                        com.google.gson.JsonParser.parseString(json));
        ts.svc.didChangeConfiguration(params);

        assertEquals("Reregistrar must NOT be called when roots are unchanged",
                0, ts.reregistrations.get());
    }

    @Test
    public void applyUpdateDoesNotTriggerReregistrarWhenRootsAbsent() {
        TestSetup ts = new TestSetup();
        ts.settings.jmlWorkspaceRoots = "/existing";

        // JSON that does NOT include jmlWorkspaceRoots.
        String json = "{\"openjml\":{\"specsPath\":\"/specs\"}}";
        org.eclipse.lsp4j.DidChangeConfigurationParams params =
                new org.eclipse.lsp4j.DidChangeConfigurationParams(
                        com.google.gson.JsonParser.parseString(json));
        ts.svc.didChangeConfiguration(params);

        assertEquals("Reregistrar must NOT be called when jmlWorkspaceRoots is absent from update",
                0, ts.reregistrations.get());
    }

    // -----------------------------------------------------------------------
    // didChangeWatchedFiles — routing and filtering
    // -----------------------------------------------------------------------

    @Test
    public void didChangeWatchedFilesRoutesJmlUri() {
        TestSetup ts = new TestSetup();
        fireEvent(ts.svc, "file:///Foo.jml", FileChangeType.Changed);

        assertEquals("jml handler must be called once", 1, ts.jmlCalls.size());
        assertEquals("file:///Foo.jml", ts.jmlCalls.get(0)[0]);
        assertEquals("Changed", ts.jmlCalls.get(0)[1]);
        assertEquals("java handler must not be called", 0, ts.javaCalls.size());
    }

    @Test
    public void didChangeWatchedFilesRoutesJavaUri() {
        TestSetup ts = new TestSetup();
        fireEvent(ts.svc, "file:///Bar.java", FileChangeType.Created);

        assertEquals("java handler must be called once", 1, ts.javaCalls.size());
        assertEquals("file:///Bar.java", ts.javaCalls.get(0)[0]);
        assertEquals("Created", ts.javaCalls.get(0)[1]);
        assertEquals("jml handler must not be called", 0, ts.jmlCalls.size());
    }

    @Test
    public void didChangeWatchedFilesIgnoresNonJmlNonJava() {
        TestSetup ts = new TestSetup();
        fireEvent(ts.svc, "file:///readme.txt", FileChangeType.Changed);

        assertEquals("jml handler must not be called",  0, ts.jmlCalls.size());
        assertEquals("java handler must not be called", 0, ts.javaCalls.size());
    }

    @Test
    public void didChangeWatchedFilesFiltersOutOfRootFile() {
        TestSetup ts = new TestSetup();
        // Root is /proj; file is outside /proj.
        ts.settings.jmlWorkspaceRoots = File.separator + "proj";

        fireEvent(ts.svc, "file:///other/Foo.java", FileChangeType.Created);

        assertEquals("handler must not be called for out-of-root file",
                0, ts.javaCalls.size());
    }

    @Test
    public void didChangeWatchedFilesAcceptsAllWhenRootsEmpty() {
        TestSetup ts = new TestSetup();
        // No roots configured — all files accepted.
        ts.settings.jmlWorkspaceRoots    = null;
        ts.settings.workspaceFolderPaths = null;

        fireEvent(ts.svc, "file:///anywhere/Foo.java", FileChangeType.Deleted);

        assertEquals("handler must be called when no root filter is configured",
                1, ts.javaCalls.size());
    }
}
