package tests;

/** Does some rough tests of the TCBase test harness */
public class harnesstests extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    // These test that the harness fails gracefully
    /** Test that harness reports a missing error */
    public void testHarness() {
        helpFailure("Wrong number of messages seen expected:<1> but was:<0>",
                " class A {}","X");
    }

    /** Test that harness reports an unexpected error */
    public void testHarness1() {
        helpFailure("Wrong number of messages seen expected:<0> but was:<6>",
        " class A { QQ }");
    }

    /** Test that harness reports a missing argument */
    public void testHarness2() {
        helpFailure("Wrong number of messages seen expected:<1> but was:<6>",
                " class A { QQ }",":1: <identifier> expected");
    }

    /** Test that harness reports a wrong column */
    public void testHarness3() {
        helpFailure("Column for message 0 expected:<-1> but was:<14>",
                " class A { QQ }","/TEST.java:1: <identifier> expected",-1,"",0,"",0);
    }

    /** Test that harness reports a mismatched message */
    public void testHarness4() {
        helpFailure("Message 0 mismatch expected:<X> but was:</TEST.java:1: <identifier> expected>",
                " class A { QQ }","X",0,"",0,"",0);
    }

}
