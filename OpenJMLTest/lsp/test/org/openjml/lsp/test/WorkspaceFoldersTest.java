package org.openjml.lsp.test;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.ProjectConfig;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for {@code workspace/didChangeWorkspaceFolders} handling.
 *
 * <p>When no explicit project configuration is supplied at initialize time the server
 * synthesizes a single {@code "__workspace__"} project whose {@code rootPaths} list
 * mirrors the LSP workspace folders.  The {@code didChangeWorkspaceFolders} handler
 * ({@link org.openjml.lsp.OpenJMLWorkspaceService#didChangeWorkspaceFolders}) must
 * keep that list in sync as the client adds and removes folders.
 *
 * <p>Coverage targets:
 * <ul>
 *   <li>{@link #testAddFolder} — adding a folder appends its OS path to
 *       {@code __workspace__.rootPaths}.</li>
 *   <li>{@link #testRemoveFolder} — removing a folder prunes its OS path from
 *       {@code __workspace__.rootPaths}.</li>
 *   <li>{@link #testAddAndRemoveInSameEvent} — both sides of the event object
 *       are applied in a single notification.</li>
 *   <li>{@link #testAddDuplicateFolderIsIdempotent} — adding a folder that is
 *       already present does not duplicate the path.</li>
 *   <li>{@link #testNullEventIsIgnored} — a null event payload does not crash
 *       the server.</li>
 * </ul>
 *
 * <p>Tests access {@code __workspace__.rootPaths} directly via
 * {@link org.openjml.lsp.OpenJMLLanguageServer#globalSettingsForTest()} to
 * avoid round-tripping through a full {@code --check} invocation.
 */
public class WorkspaceFoldersTest extends ProtocolTestBase {

    private static final long LOCAL_TIMEOUT = 10;

    /** URI of the initial workspace folder supplied at initialization. */
    private static final String FOLDER_A_URI  = "file:///tmp/wftest-folderA";
    private static final String FOLDER_B_URI  = "file:///tmp/wftest-folderB";
    private static final String FOLDER_A_PATH = "/tmp/wftest-folderA";
    private static final String FOLDER_B_PATH = "/tmp/wftest-folderB";

    @Before
    @Override
    public void setUp() throws Exception {
        // Each test controls the initialize handshake itself.
        createServerAndClient();
    }

    @After
    @Override
    public void tearDown() {
        super.tearDown();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Initialize the server with folderA as the only workspace folder. */
    private void initWithFolderA() throws Exception {
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,"
                + "\"workspaceFolders\":[{\"uri\":\"" + FOLDER_A_URI + "\",\"name\":\"folderA\"}],"
                + "\"capabilities\":{}}");
        assertNotNull("Server must respond to initialize",
                client.nextResponse(LOCAL_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");
    }

    /** Find the synthesized {@code __workspace__} project, or {@code null}. */
    private ProjectConfig workspaceProject() {
        OpenJMLSettings gs = server.globalSettingsForTest();
        if (gs.projects == null) return null;
        for (ProjectConfig p : gs.projects) {
            if (OpenJMLSettings.WORKSPACE_PROJECT_ID.equals(p.id)) return p;
        }
        return null;
    }

    /** Send {@code workspace/didChangeWorkspaceFolders} and wait briefly for processing. */
    private void sendFolderChange(String addedJson, String removedJson) throws Exception {
        client.sendNotification("workspace/didChangeWorkspaceFolders",
                "{\"event\":{\"added\":" + addedJson + ",\"removed\":" + removedJson + "}}");
        Thread.sleep(100);
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * Adding a workspace folder appends its OS path to the
     * {@code __workspace__} project's {@code rootPaths}.
     */
    @Test
    public void testAddFolder() throws Exception {
        initWithFolderA();
        ProjectConfig wp = workspaceProject();
        assertNotNull("__workspace__ project must be synthesized", wp);
        assertTrue("rootPaths must contain folderA after init",
                wp.rootPaths != null && wp.rootPaths.contains(FOLDER_A_PATH));

        sendFolderChange(
                "[{\"uri\":\"" + FOLDER_B_URI + "\",\"name\":\"folderB\"}]",
                "[]");

        wp = workspaceProject();
        assertNotNull("rootPaths must be non-null after add", wp.rootPaths);
        assertTrue("rootPaths must still contain folderA", wp.rootPaths.contains(FOLDER_A_PATH));
        assertTrue("rootPaths must contain folderB after add", wp.rootPaths.contains(FOLDER_B_PATH));
    }

    /**
     * Removing a workspace folder prunes its OS path from
     * {@code __workspace__.rootPaths}.
     */
    @Test
    public void testRemoveFolder() throws Exception {
        initWithFolderA();

        // First add folderB so we can remove folderA and still have a non-empty list.
        sendFolderChange(
                "[{\"uri\":\"" + FOLDER_B_URI + "\",\"name\":\"folderB\"}]",
                "[]");

        sendFolderChange(
                "[]",
                "[{\"uri\":\"" + FOLDER_A_URI + "\",\"name\":\"folderA\"}]");

        ProjectConfig wp = workspaceProject();
        assertNotNull("rootPaths must be non-null after remove", wp.rootPaths);
        assertFalse("rootPaths must not contain folderA after remove",
                wp.rootPaths.contains(FOLDER_A_PATH));
        assertTrue("rootPaths must still contain folderB after remove",
                wp.rootPaths.contains(FOLDER_B_PATH));
    }

    /**
     * A single {@code didChangeWorkspaceFolders} event may carry both added and
     * removed entries; both sides must be applied atomically.
     */
    @Test
    public void testAddAndRemoveInSameEvent() throws Exception {
        initWithFolderA();

        // Swap folderA for folderB in one event.
        sendFolderChange(
                "[{\"uri\":\"" + FOLDER_B_URI + "\",\"name\":\"folderB\"}]",
                "[{\"uri\":\"" + FOLDER_A_URI + "\",\"name\":\"folderA\"}]");

        ProjectConfig wp = workspaceProject();
        assertNotNull("rootPaths must be non-null after swap", wp.rootPaths);
        assertTrue("rootPaths must contain folderB after swap",
                wp.rootPaths.contains(FOLDER_B_PATH));
        assertFalse("rootPaths must not contain folderA after swap",
                wp.rootPaths.contains(FOLDER_A_PATH));
    }

    /**
     * Adding a folder that is already present must not duplicate the path in
     * {@code rootPaths}.
     */
    @Test
    public void testAddDuplicateFolderIsIdempotent() throws Exception {
        initWithFolderA();

        // Add folderA again.
        sendFolderChange(
                "[{\"uri\":\"" + FOLDER_A_URI + "\",\"name\":\"folderA\"}]",
                "[]");

        ProjectConfig wp = workspaceProject();
        assertNotNull("rootPaths must be non-null", wp.rootPaths);
        long count = wp.rootPaths.stream()
                .filter(FOLDER_A_PATH::equals).count();
        assertEquals("folderA must appear exactly once after duplicate add", 1, count);
    }

    /**
     * A {@code didChangeWorkspaceFolders} notification with a null event must
     * be silently ignored — the server must remain responsive afterward.
     */
    @Test
    public void testNullEventIsIgnored() throws Exception {
        initWithFolderA();

        client.sendNotification("workspace/didChangeWorkspaceFolders",
                "{\"event\":null}");
        Thread.sleep(100);

        // Server must still respond to a subsequent request.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"openjml.getRunningEscTasks\",\"arguments\":[]}");
        assertNotNull("Server must remain responsive after null-event notification",
                client.nextResponse(LOCAL_TIMEOUT, TimeUnit.SECONDS));
    }
}
