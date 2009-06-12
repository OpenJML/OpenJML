package tests;

public class flow extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    /** Forward reference from invariant is OK */
    public void testForwardReference() {
        helpTC("public class TEST { \n//@ invariant b;\n  boolean b;}");
    }

    /** Flow checks for model methods*/
    public void testModelMethod() {
        addMockFile("$A/A.spec","public class A { \n//@ model int m() {} \n}");
        helpTCF("A.java","public class A { }"
        ,"/$A/A.spec:2: missing return statement",20
        );
    }

    /** Check on name of file  - not particularly a flow check */
    public void testFileName() {
        helpTCF("A.java","public class B { }"
        ,"/A.java:1: class B is public, should be declared in a file named B.java",8
        );
    }

    /** Flow checks for ghost fields */
    public void testGhostForwardReference() {
        addMockFile("$A/A.spec","public class A { \n//@ ghost int i = j; ghost int j; \n}");
        helpTCF("A.java","public class A { }"
        ,"/$A/A.spec:2: illegal forward reference",19
        );
    }



}
