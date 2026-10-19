package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.JmlTestSuite;
import org.junit.*;

/** Fixture for OpenJMLTestRunner's timeout handling and counting, checked by unittests/runner-selftest.
 * The tests do nothing unless the environment variable RUNNERSELFTEST is set. With RUNNERSELFTEST set and -s=4,
 * the expected outcome is 4 successes, 1 timeout, 1 failure: aHang times out (it ignores interrupts, as an
 * ESC run does) and fails only after the later tests have run; bQuick must not queue behind it. */
public class testrunner extends JmlTestSuite {

    static boolean run = System.getenv("RUNNERSELFTEST") != null;

    /** Sleeps for the given time, ignoring interrupts */
    static void busy(long millis) {
        long end = System.currentTimeMillis() + millis;
        long left;
        while ((left = end - System.currentTimeMillis()) > 0) {
            try { Thread.sleep(left); } catch (InterruptedException e) { /* ignore, like a running proof */ }
        }
    }

    @Test
    public void aHang() {
        if (!run) return;
        busy(10000);
        Assert.fail("late failure of a timed-out test");
    }

    @Test
    public void bQuick() {
    }

    @Test
    public void cFail() {
        if (run) Assert.fail("expected failure");
    }

    @Test
    public void dSlow() {
        if (run) busy(3000);
    }

    @Test
    public void eSlow() {
        if (run) busy(3000);
    }

    @Test
    public void fSlow() {
        if (run) busy(3000);
    }
}
