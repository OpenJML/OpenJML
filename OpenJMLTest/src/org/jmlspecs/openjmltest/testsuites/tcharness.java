package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;

import static org.junit.Assert.*;
import org.junit.Test;

/** Does some simple tests of the TCBase test harness */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class tcharness extends TCBase {
    
    // FIXME - there are no tests of whether any options added via addOptions are invalide

    // Used to check the test system itself
    public void helpFailure(String failureMessage, String s, Object ... expectedErrors) {
        noExtraPrinting = true;
        boolean failed = false;
        try {
            helpTCText(null, s, expectedErrors);
        } catch (AssertionError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test Harness failed to report an error");
    }

    // When a test fails because there is unexpected error output, the test infrastructure
    // will dump the actual errors. for convenience. For these harness tests we override the
    // printing of diagnostics on failure to avoid expected output on stdout
    @Override
    public void printDiagnostics() {
    }

    // These test that the harness fails gracefully
    
    /** Test that harness reports a missing error */
    @Test
    public void testHarness() {
        helpFailure("Fewer errors observed (0) than expected. First extra: X",
                " class A {}","X",1);
    }

    /** Test that harness reports an unexpected error */
    @Test
    public void testHarness1() {
        helpFailure("More errors observed (1) than expected. First extra: /TEST.java:1: error: <identifier> expected line=1 col=14 start=13 pos=13 end=13",
        " class A { QQ }");
    }

    /** Test that harness reports a missing argument */
    @Test
    public void testHarness2() {
        helpFailure("Failed to match diagnostic 0 (col): /TEST.java:1: error: <identifier> expected line=1 col=14 start=13 pos=13 end=13",
                " class A { QQ }","/TEST.java:1: error: <identifier> expected");
    }

    /** Test that harness reports a missing argument */
    @Test
    public void testHarness2a() {
        helpFailure("Failed to match diagnostic 0 (col): /TEST.java:1: error: <identifier> expected line=1 col=14 start=13 pos=13 end=13",
                " class A { QQ }","/TEST.java:1: error: <identifier> expected", -1);
    }

    /** Test that harness reports a wrong column */
    @Test
    public void testHarness3() {
        helpFailure("Failed to match diagnostic 0 (col): /TEST.java:1: error: <identifier> expected line=1 col=14 start=13 pos=13 end=13",
                " class A { QQ }","/TEST.java:1: error: <identifier> expected",1);
    }

    /** Test that harness reports a wrong start */
    @Test
    public void testHarness4() {
        helpFailure("Failed to match diagnostic 0 (start): /TEST.java:1: error: <identifier> expected line=1 col=14 start=13 pos=13 end=13",
                " class A { QQ }","/TEST.java:1: error: <identifier> expected", 14, 4,4,4);
    }

    /** Test that harness reports a mismatched message */
    @Test
    public void testHarness5() {
        helpFailure("Failed to match diagnostic 0 (text): /TEST.java:1: error: <identifier> expected line=1 col=14 start=13 pos=13 end=13",
                " class A { QQ }","X");
    }
}
