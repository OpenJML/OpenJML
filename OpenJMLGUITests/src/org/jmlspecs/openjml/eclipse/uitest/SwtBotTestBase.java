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
        closeWelcomeAndTipViews();
    }

    @AfterClass
    public static void baseTearDown() {
        bot.resetWorkbench();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Close the Welcome and "Tip of the Day" views/dialogs if open.
     * These pop up on first launch and block menu access.
     */
    protected static void closeWelcomeAndTipViews() {
        try {
            bot.viewByTitle("Welcome").close();
        } catch (WidgetNotFoundException ignored) {}

        try {
            bot.shell("Tip of the Day").bot().button("Close").click();
        } catch (WidgetNotFoundException ignored) {}
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
