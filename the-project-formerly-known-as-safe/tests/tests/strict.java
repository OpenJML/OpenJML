package tests;

/** This tests that extensions are prohibited by -strict. 
 *  (I suppose we should test that every non-extension is allowed by -strict, but we don't.) */

import org.jmlspecs.openjml.JmlOption;
import org.junit.Test;

public class strict extends TCBase {

    String opt = JmlOption.STRICT.optionName();
    
    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        main.addOptions(opt);
        expectedExit = 0;
    }

    @Test
    public void testLbl() {
        helpTCF("A.java","public class A {\n" +
                " //@ ghost int i = (\\lbl A 0);\n }"
                ,"/A.java:2: warning: The \\lbl construct is an OpenJML extension to JML and not allowed under " + opt,21
                );
    }

    @Test
    public void testLblB() {
        main.addOptions(opt + "=false");
        helpTCF("A.java","public class A {\n" +
                " //@ ghost int i = (\\lbl A 0);\n }"
                );
    }

    @Test
    public void testIndex() {
        helpTCF("A.java","public class A {\n" +
                " void m(int[] a) { for (int i: a) {\n" +
                "    //@ assert \\index == i; \n" +
                " }}}"
                ,"/A.java:3: warning: The \\index construct is an OpenJML extension to JML and not allowed under " + opt,16
                );
    }

    @Test
    public void testIndexB() {
        main.addOptions(opt + "=false");
        helpTCF("A.java","public class A {\n" +
                " void m(int[] a) { for (int i: a) {\n" +
                "    //@ assert \\index == i; \n" +
                " }}}"
                );
    }

    @Test
    public void testValues() {
        helpTCF("A.java","public class A {\n" +
                " void m(int[] a) { for (int i: a) {\n" +
                "    //@ assert \\values.size() >= 0; \n" +
                " }}}"
                ,"/A.java:3: warning: The \\values construct is an OpenJML extension to JML and not allowed under " + opt,16
                );
    }

    @Test
    public void testValuesB() {
        main.addOptions(opt + "=false");
        helpTCF("A.java","public class A {\n" +
                " void m(int[] a) { for (int i: a) {\n" +
                "    //@ assert \\values.size() >= 0; \n" +
                " }}}"
                );
    }

    @Test
    public void testExceptionB() {
        main.addOptions(opt + "=false");
        helpTCF("A.java","public class A {\n" +
                " //@ signals (Exception) \\exception != null;\n" +
                " void m(int[] a) {\n" +
                " }}"
                );
    }

    @Test
    public void testException() {
        helpTCF("A.java","public class A {\n" +
                " //@ signals (Exception) \\exception != null;\n" +
                " void m(int[] a) {\n" +
                " }}"
                ,"/A.java:2: warning: The \\exception construct is an OpenJML extension to JML and not allowed under " + opt,26
                );
    }

    @Test
    public void testSecret() {
        helpTCF("A.java","public class A {\n" +
                " /*@ secret */ private int i;\n" +
                " void m(int[] a) {\n" +
                " }}"
                ,"/A.java:2: warning: The secret construct is an OpenJML extension to JML and not allowed under " + opt,6
                );
    }

    @Test
    public void testSecretB() {
        main.addOptions(opt + "=false");
        helpTCF("A.java","public class A {\n" +
                " /*@ secret */ private int i;\n" +
                " void m(int[] a) {\n" +
                " }}"
                );
    }

    @Test
    public void testQuery() {
        helpTCF("A.java","public class A {\n" +
                " //@ query\n" +
                " int m() { return 0; \n" +
                " }}"
                ,"/A.java:2: warning: The query construct is an OpenJML extension to JML and not allowed under " + opt,6
                );
    }

    @Test
    public void testQueryB() {
        main.addOptions(opt + "=false");
        helpTCF("A.java","public class A {\n" +
                " //@ query\n" +
                " int m() { return 0; \n" +
                " }}"
                );
    }

    @Test
    public void testStoreRef() {
        helpTCF("A.java","public class A {\n" +
                " //@ assignable a[0..];\n" +
                " int m(int[] a) { return 0; \n" +
                " }}"
                ,"/A.java:2: warning: The storeref with implied end-of-range (a[i..]) construct is an OpenJML extension to JML and not allowed under " + opt,22
                );
    }

    @Test
    public void testStoreRefB() {
        main.addOptions(opt + "=false");
        helpTCF("A.java","public class A {\n" +
                " //@ assignable a[0..];\n" +
                " int m(int[] a) { return 0; \n" +
                " }}"
                );
    }
    
    @Test
    public void testRepresents() {
        expectedExit = 0;
        helpTCF("A.java","public class A {\n static int j; //@  model static int i; static represents i <- j;\n}"
                ,"/A.java:2: warning: The left arrow is deprecated in represents clauses, use = instead",61
                );
    }
    


}
