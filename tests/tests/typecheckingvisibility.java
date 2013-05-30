package tests;

import org.junit.Test;

public class typecheckingvisibility extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        options.put("-noPurityCheck", "");
    }

    @Test public void testLocalVisibility() {
        helpTCF("TestJava.java","public class TestJava { /*@ private invariant (\\forall int i; i>0; i!= 0); */ }");
    }

    @Test public void testLocalVisibility2() {
        helpTCF("TestJava.java","public class TestJava { /*@ public invariant (\\forall int i; i>0; i!= 0); */ }");
    }

    @Test public void testLocalVisibility3() {
        helpTCF("TestJava.java","public class TestJava { /*@ public invariant 0 == (\\let int i = 0; i); */ }");
    }

    
}
