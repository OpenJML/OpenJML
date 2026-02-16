package org.jmlspecs.openjmltest.testsuites;

/** This tests that extensions are prohibited by -strict. 
 *  (I suppose we should test that every non-extension is allowed by -strict, but we don't.) */

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class strict extends TCBase {

    String opt = JmlOption.LANG.optionName();
    String optjml = opt + "=" + JmlOption.langJML;
    String optjmlp = opt + "=" + JmlOption.langOpenJML;
    
    @Override
    public void setUp() throws Exception {
        super.setUp();
        setDeprecation();
        addOptions(optjml);
        expectedExit = 0;
    }

    @Test
    public void testLbl() {
        helpTCText("A.java","public class A {\n" +
                " //@ ghost int i = (\\lbl A 0);\n }"
                ,"/A.java:2: warning: [strict-jml] The \\lbl construct is an OpenJML extension to JML and not allowed under " + optjml,21
                );
    }

    @Test
    public void testLblB() {
        addOptions(optjmlp);
        helpTCText("A.java","public class A {\n" +
                " //@ ghost int i = (\\lbl A 0);\n }"
                );
    }

    // \count is now standard JML
    @Test
    public void testIndex() {
        helpTCText("A.java","public class A {\n" +
                " void m(int[] a) { for (int i: a) {\n" +
                "    //@ assert \\count == i; \n" +
                " }}}"
                );
    }


    @Test
    public void testValues() {
        helpTCText("A.java","public class A {\n" +
                " void m(int[] a) { for (int i: a) {\n" +
                "    //@ assert \\values.size() >= 0; \n" +
                " }}}"
                ,"/A.java:3: warning: [strict-jml] The \\values construct is an OpenJML extension to JML and not allowed under " + optjml,16
                );
    }

    @Test
    public void testValuesB() {
        addOptions(optjmlp);
        helpTCText("A.java","public class A {\n" +
                " void m(int[] a) { for (int i: a) {\n" +
                "    //@ assert \\values.size() >= 0; \n" +
                " }}}"
                );
    }

    @Test
    public void testExceptionB() {
        addOptions(optjmlp);
        helpTCText("A.java","public class A {\n" +
                " //@ signals (Exception) \\exception != null;\n" +
                " void m(int[] a) {\n" +
                " }}"
                );
    }

    @Test
    public void testException() {
        helpTCText("A.java","public class A {\n" +
                " //@ signals (Exception) \\exception != null;\n" +
                " void m(int[] a) {\n" +
                " }}"
                ,"/A.java:2: warning: [strict-jml] The \\exception construct is an OpenJML extension to JML and not allowed under " + optjml,26
                );
    }

    @Test
    public void testSecret() {
        helpTCText("A.java","public class A {\n" +
                " /*@ secret */ private int i;\n" +
                " void m(int[] a) {\n" +
                " }}"
                ,"/A.java:2: warning: [strict-jml] The secret construct is an OpenJML extension to JML and not allowed under " + optjml,6
                );
    }

    @Test
    public void testSecretB() {
        addOptions(optjmlp);
        helpTCText("A.java","public class A {\n" +
                " /*@ secret */ private int i;\n" +
                " void m(int[] a) {\n" +
                " }}"
                );
    }

    @Test
    public void testQuery() {
        helpTCText("A.java","public class A {\n" +
                " //@ query\n" +
                " int m() { return 0; \n" +
                " }}"
                ,"/A.java:2: warning: [strict-jml] The query construct is an OpenJML extension to JML and not allowed under " + optjml,6
                );
    }

    @Test
    public void testQueryB() {
        addOptions(optjmlp);
        helpTCText("A.java","public class A {\n" +
                " //@ query\n" +
                " int m() { return 0; \n" +
                " }}"
                );
    }

    @Test
    public void testStoreRef() {
        helpTCText("A.java","public class A {\n" +
                " //@ assignable a[0..];\n" +
                " int m(int[] a) { return 0; \n" +
                " }}"
                ,"/A.java:2: warning: [strict-jml] The storeref with implied end-of-range construct is an OpenJML extension to JML and not allowed under " + optjml,22
                );
    }

    @Test
    public void testStoreRefB() {
        addOptions(optjmlp);
        helpTCText("A.java","public class A {\n" +
                " //@ assignable a[0..];\n" +
                " int m(int[] a) { return 0; \n" +
                " }}"
                );
    }
    
    @Test
    public void testRepresents() {
        helpTCText("A.java","public class A {\n static int j; //@ in i;\n//@  model static int i; static represents i <- j;\n}"
                );
    }
    
    @Test
    public void testRepresentsB() {
        expectedExit = 0;
        addOptions(optjmlp);
        helpTCText("A.java","public class A {\n static int j; //@ in i;\n//@  model static int i; static represents i <- j;\n}"
                ,"/A.java:3: warning: [deprecated] The left arrow is deprecated in represents clauses, use = instead",46
                );
    }
    
    @Test
    public void testClauseGroup() {
        helpTCText("A.java",
            """
            public class A {
                //@ requires true;
                //@ {|
                //@    ensures true;
                //@ also
                //@    ensures true;
                //@ |}
                //@ signals (Exception) true;
                public void m() {}
            }
            """
            ,"/A.java:8: warning: [strict-jml] The clauses following a clause group construct is an OpenJML extension to JML and not allowed under --lang=jml", 9
        );
    }
    
    @Test
    public void testClauseGroupA() {
        helpTCText("A.java",
            """
            public class A {
                //@ requires true;
                //@ {|
                //@    ensures true;
                //@ also
                //@    ensures true;
                //@ |}
                //@ signals_only \\nothing;
                public void m() {}
            }
            """
            ,"/A.java:8: warning: [strict-jml] The clauses following a clause group construct is an OpenJML extension to JML and not allowed under --lang=jml", 9
        );
    }
}
