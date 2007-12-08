package tests;

public class weakly extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }
 
    public void testWeakly() {
        helpTCF("A.java",
                " class A extends Object /*@ weakly */ implements B /*@ weakly */, C/*@ weakly */ {" +
                "} interface B{} interface C{}"
        );
    }

    // FIXME - this should not be allowed but is
    public void testWeakly2() {
        helpTCF("A.java",
                " class A {\n" +
                "  Object /*@ weakly */ o; " + 
                "} "
        );
    }

}
