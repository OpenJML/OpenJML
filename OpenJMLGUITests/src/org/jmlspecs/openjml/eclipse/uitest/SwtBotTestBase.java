package org.jmlspecs.openjml.eclipse.uitest;

import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;

/**
 * Base class for all OpenJMLUI SWTBot tests.
 *
 * <p>Sets up a shared {@link SWTWorkbenchBot}, configures timeouts, and
 * closes any welcome/tip-of-the-day popups that would otherwise block
 * menu access.  Subclasses annotated with
 * {@code @RunWith(SWTBotJunit4ClassRunner.class)} inherit the runner
 * through the {@code @RunWith} on this class; subclasses that need a
 * different runner must redeclare it.
 *
 * <p>Usage: extend this class and call {@link #baseSetUp()} from your
 * own {@code @BeforeClass} (or rely on this class's {@code @BeforeClass}
 * if your subclass has none).
 */
@RunWith(SWTBotJunit4ClassRunner.class)
public abstract class SwtBotTestBase {

    /** Shared bot — one instance per JVM/test run. */
    protected static SWTWorkbenchBot bot;

    @BeforeClass
    public static void baseSetUp() {
        SWTBotPreferences.TIMEOUT         = 20_000;   // default widget-wait timeout (ms)
        SWTBotPreferences.KEYBOARD_LAYOUT = "EN_US";
        bot = new SWTWorkbenchBot();
        configureLspServerPath();
        closeWelcomeAndTipViews();
    }

    /**
     * Logs the LSP server path that will be used.
     * {@code OpenJMLStreamConnectionProvider.findServerPath()} reads the
     * {@code openjml.lsp.server.path} system property directly (set by the
     * Makefile), so no preference-store manipulation is needed here.
     */
    protected static void configureLspServerPath() {
        String path = System.getProperty("openjml.lsp.server.path");
        if (path != null && !path.isBlank()) {
            System.out.println("[GUITest] LSP server path (system property): " + path);
        } else {
            System.out.println("[GUITest] openjml.lsp.server.path not set; "
                    + "LSP server will be sought at Eclipse install dir");
        }
    }

    @AfterClass
    public static void baseTearDown() {
        bot.resetWorkbench();
    }

    // -----------------------------------------------------------------------
    // LSP server lifecycle (for use by LSP-dependent test classes)
    // -----------------------------------------------------------------------

    /**
     * Cleanly stop the OpenJML LSP server via LSP4E's
     * {@code LanguageServerWrapper.stop()} (sends {@code shutdown} +
     * {@code exit}).  Falls back to killing the {@code openjml-lsp} process
     * after a timeout so stale server processes don't interfere with the
     * next test class.
     *
     * <p>Call this from {@code @AfterClass} in test classes that start the
     * LSP server (by opening a Java file in an editor).
     *
     * @param timeoutMs  max time to wait for clean shutdown before force-killing
     */
    protected static void stopLspServer(long timeoutMs) {
        try {
            Class<?> wrapperClass = Class.forName(
                    "org.eclipse.lsp4e.LanguageServerWrapper");
            Class<?> listenerClass = Class.forName(
                    "org.jmlspecs.openjml.eclipse.LspPartListener");
            java.lang.reflect.Field wrapperField =
                    listenerClass.getDeclaredField("cachedWrapper");
            wrapperField.setAccessible(true);
            Object wrapper = wrapperField.get(null);
            if (wrapper != null) {
                java.lang.reflect.Method stopMethod =
                        wrapperClass.getMethod("stop");
                Thread stopThread = new Thread(() -> {
                    try { stopMethod.invoke(wrapper); }
                    catch (Exception e) {
                        System.err.println("[GUITest] LSP wrapper.stop() failed: " + e);
                    }
                }, "lsp-stop");
                stopThread.start();
                stopThread.join(timeoutMs);
                if (stopThread.isAlive()) {
                    System.err.println("[GUITest] WARNING: LSP server did not stop "
                            + "within " + timeoutMs + "ms — killing openjml-lsp");
                    killOpenjmlLspProcesses();
                } else {
                    System.out.println("[GUITest] LSP server stopped cleanly.");
                }
                return;
            }
        } catch (ClassNotFoundException ignored) {
            return;  // OpenJMLUI bundle not loaded — no server to stop
        } catch (Exception e) {
            System.err.println("[GUITest] Could not invoke wrapper.stop(): " + e);
        }
        killOpenjmlLspProcesses();
    }

    /** Kill any running openjml-lsp processes (best-effort). */
    private static void killOpenjmlLspProcesses() {
        try {
            ProcessBuilder pb = new ProcessBuilder("pkill", "-f", "openjml-lsp");
            pb.redirectErrorStream(true);
            Process p = pb.start();
            p.waitFor(3, java.util.concurrent.TimeUnit.SECONDS);
        } catch (Exception e) {
            System.err.println("[GUITest] pkill openjml-lsp failed: " + e);
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Close the Welcome and "Tip of the Day" views/dialogs if open, and
     * dismiss the OpenJML "Server Not Configured" warning if it appears.
     *
     * <p>The LSP warning should not appear in a correctly configured test
     * instance (the Makefile copies {@code openjml-lsp} to the test Eclipse
     * install directory).  This dismiss is a safety net only.
     */
    protected static void closeWelcomeAndTipViews() {
        try {
            bot.viewByTitle("Welcome").close();
        } catch (WidgetNotFoundException ignored) {}

        try {
            bot.shell("Tip of the Day").bot().button("Close").click();
        } catch (WidgetNotFoundException ignored) {}

        // Safety net: if the LSP server was not found, dismiss the warning.
        // In a correctly prepared test instance this dialog should not appear.
        try {
            bot.shell("OpenJML: Server Not Configured").bot().button("Dismiss").click();
        } catch (WidgetNotFoundException ignored) {}

        // Dismiss the Eclipse Marketplace / recommendation dialogs that
        // sometimes appear on first launch of a fresh workspace.
        for (String title : new String[]{
                "Eclipse Marketplace", "Discover",
                "Eclipse IDE Marketplace", "Software Updates"}) {
            try {
                bot.shell(title).close();
            } catch (WidgetNotFoundException ignored) {}
        }
    }

    /**
     * Dismiss a modal shell by title (e.g. an unexpected error dialog).
     * No-op if no such shell is open.
     */
    protected static void dismissShellIfPresent(String title) {
        try {
            bot.shell(title).bot().button("OK").click();
        } catch (WidgetNotFoundException ignored) {}
    }
}
