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

    /** Forward reference in model class */
    public void testForwardReference2() {
        addMockFile("$A/A.spec","public class A { }\n//@ model class B { int b = c; int c = 0; }\n\n");
        helpTCF("A.java","public class A { }"
        ,"/$A/A.spec:2: illegal forward reference",29
        );
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

    /** Check on name of file */
    public void testFileName3() {
        helpTCF("A.java","public class A { } //@ model public class B {}"
        ,"/A.java:1: class B is public, should be declared in a file named B.java",37
        );
    }

    /** Check on name of file  - not particularly a flow check */
    public void testFileNameModel() {
        helpTCF("A.java","/*@ model public class B { } */"
        ,"/A.java:1: class B is public, should be declared in a file named B.java",18
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
