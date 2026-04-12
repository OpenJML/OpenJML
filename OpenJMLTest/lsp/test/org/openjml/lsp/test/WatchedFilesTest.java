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
 *   <li>{@link OpenJMLSettings#effectiveRoots()} — uses the {@code projects}
 *       list ({@code "__workspace__"} synthesized project), falls back gracefully
 *       when absent.</li>
 *   <li>{@link OpenJMLWorkspaceService#didChangeConfiguration} — a {@code projects}
 *       update triggers the watcher-reregistrar; an unrelated setting does not.</li>
 *   <li>{@link OpenJMLWorkspaceService#didChangeWatchedFiles} — routes {@code .jml} and
 *       {@code .java} events to the correct handlers, and filters events outside the
 *       effective roots.</li>
 * </ul>
 */
public class WatchedFilesTest {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

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
                    reregistrations::incrementAndGet,
                    null);
        }
    }

    /** Fire a single {@code didChangeWatchedFiles} event. */
    private static void fireEvent(OpenJMLWorkspaceService svc,
                                   String uri, FileChangeType type) {
        FileEvent event = new FileEvent(uri, type);
        DidChangeWatchedFilesParams params = new DidChangeWatchedFilesParams(List.of(event));
        svc.didChangeWatchedFiles(params);
    }

    /** Create a synthesized {@code "__workspace__"} project with the given root paths. */
    private static OpenJMLSettings.ProjectConfig workspaceProject(String... paths) {
        OpenJMLSettings.ProjectConfig cfg = new OpenJMLSettings.ProjectConfig();
        cfg.id = "__workspace__";
        cfg.rootPaths = new ArrayList<>(List.of(paths));
        return cfg;
    }

    // -----------------------------------------------------------------------
    // effectiveRoots()
    // -----------------------------------------------------------------------

    @Test
    public void effectiveRootsUsesProjectRootPaths() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.projects = List.of(workspaceProject("/a", "/b"));
        List<String> roots = s.effectiveRoots();
        assertEquals(2, roots.size());
        assertEquals("/a", roots.get(0));
        assertEquals("/b", roots.get(1));
    }

    @Test
    public void effectiveRootsEmptyWhenNoProjects() {
        OpenJMLSettings s = new OpenJMLSettings();
        assertTrue(s.effectiveRoots().isEmpty());
    }

    @Test
    public void effectiveRootsEmptyWhenProjectsListEmpty() {
        OpenJMLSettings s = new OpenJMLSettings();
        s.projects = List.of();
        assertTrue(s.effectiveRoots().isEmpty());
    }

    @Test
    public void effectiveRootsSkipsBlankPaths() {
        OpenJMLSettings s = new OpenJMLSettings();
        OpenJMLSettings.ProjectConfig cfg = new OpenJMLSettings.ProjectConfig();
        cfg.id = "__workspace__";
        cfg.rootPaths = List.of("/a", "   ", "/b");
        s.projects = List.of(cfg);
        List<String> roots = s.effectiveRoots();
        assertEquals(2, roots.size());
        assertTrue(roots.contains("/a"));
        assertTrue(roots.contains("/b"));
    }

    // -----------------------------------------------------------------------
    // Copy constructor does not copy projects (per-project instances don't nest)
    // -----------------------------------------------------------------------

    @Test
    public void copyConstructorDoesNotCopyProjects() {
        OpenJMLSettings orig = new OpenJMLSettings();
        orig.projects = new ArrayList<>(List.of(workspaceProject("/proj/a", "/proj/b")));

        OpenJMLSettings copy = new OpenJMLSettings(orig);
        // The copy constructor intentionally leaves projects null so per-project
        // settings instances do not accidentally carry the global project list.
        assertNull("Copy constructor must not copy the projects list", copy.projects);
    }

    // -----------------------------------------------------------------------
    // applyUpdate() — watcher reregistrar
    // -----------------------------------------------------------------------

    @Test
    public void applyUpdateTriggersReregistrarOnProjectsChange() {
        TestSetup ts = new TestSetup();

        // Send didChangeConfiguration with a projects array.
        String json = "{\"openjml\":{\"projects\":[{\"id\":\"__workspace__\","
                + "\"rootPaths\":[\"/new\"]}]}}";
        org.eclipse.lsp4j.DidChangeConfigurationParams params =
                new org.eclipse.lsp4j.DidChangeConfigurationParams(
                        com.google.gson.JsonParser.parseString(json));
        ts.svc.didChangeConfiguration(params);

        assertEquals("Reregistrar must be called once when projects change",
                1, ts.reregistrations.get());
        assertNotNull(ts.settings.projects);
        assertEquals(1, ts.settings.projects.size());
        assertEquals("__workspace__", ts.settings.projects.get(0).id);
    }

    @Test
    public void applyUpdateDoesNotTriggerReregistrarWhenProjectsAbsent() {
        TestSetup ts = new TestSetup();
        ts.settings.projects = List.of(workspaceProject("/existing"));

        // JSON that does NOT include a projects key — only an unrelated setting.
        String json = "{\"openjml\":{\"specsPath\":\"/specs\"}}";
        org.eclipse.lsp4j.DidChangeConfigurationParams params =
                new org.eclipse.lsp4j.DidChangeConfigurationParams(
                        com.google.gson.JsonParser.parseString(json));
        ts.svc.didChangeConfiguration(params);

        assertEquals("Reregistrar must NOT be called when projects is absent from update",
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
        ts.settings.projects = List.of(workspaceProject(File.separator + "proj"));

        fireEvent(ts.svc, "file:///other/Foo.java", FileChangeType.Created);

        assertEquals("handler must not be called for out-of-root file",
                0, ts.javaCalls.size());
    }

    @Test
    public void didChangeWatchedFilesAcceptsAllWhenRootsEmpty() {
        TestSetup ts = new TestSetup();
        // No projects configured — all files accepted.

        fireEvent(ts.svc, "file:///anywhere/Foo.java", FileChangeType.Deleted);

        assertEquals("handler must be called when no root filter is configured",
                1, ts.javaCalls.size());
    }
}
