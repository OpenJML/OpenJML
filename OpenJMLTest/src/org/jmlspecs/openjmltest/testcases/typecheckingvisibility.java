package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

public class typecheckingvisibility extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
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

    @Test public void testVisibility1() {
        helpTCF("TestJava.java","public class TestJava { public int i; \n/*@  invariant i == 0; */ }"
                ,"/TestJava.java:2: An identifier with public visibility may not be used in a invariant clause with package visibility",16
                );
    }

    @Test public void testVisibility2() {
        helpTCF("TestJava.java","public class TestJava { public int i; \n/*@  invariant this.i == 0; */ }"
        ,"/TestJava.java:2: An identifier with public visibility may not be used in a invariant clause with package visibility",20
        );
    }

    
}
