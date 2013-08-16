package tests;

import org.junit.Test;

public class purity extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        main.addOptions("-noPurityCheck=false");
    }

    /** Test scanning something very simple */
    @Test
    public void testPure() {
        helpTC(" class A { /*@ pure */ boolean m() { return true; }  \n //@ invariant m(); \n}"
                );
    }

    /** Test scanning something very simple */
    @Test
    public void testPure2() {
        expectedExit = 0;
        helpTC(" class A {  boolean m() { return true; }  \n //@ invariant m(); \n}"
               ,"/TEST.java:2: warning: A non-pure method is being called where it is not permitted: m()",17
               );
    }
    
    @Test
    public void testSpecFile() {
        addMockFile("$A/A.jml","public class A { /*@pure*/ int m();  //@ invariant m() == 0; \n}");
        helpTCF("A.java","public class A {  int m() { return 0; }  \n }"
                );
        
    }

    @Test
    public void testSpecFile2() {
        expectedExit = 0;
        addMockFile("$A/A.jml","public class A {  int m();  //@ invariant m() == 0; \n}");
        helpTCF("A.java","public class A {  int m() { return 0; }  \n }"
                ,"/$A/A.jml:1: warning: A non-pure method is being called where it is not permitted: m()",44
                );
        
    }
    
    @Test
    public void testSpecFile3() {
        expectedExit = 0;
        addMockFile("$A/A.jml","public class A {  /*@ pure */ int m();  //@ invariant m() == 0; \n}");
        helpTCF("A.java","public class A {  int m() { return 0; }  \n }"
                );
        
    }
    
    @Test
    public void testSpecFile3a() {
        expectedExit = 0;
        addMockFile("$A/A.jml","public class A {  int m();  //@ invariant m() == 0; \n}");
        helpTCF("A.java","public class A {  int m() { return 0; }  \n }"
                ,"/$A/A.jml:1: warning: A non-pure method is being called where it is not permitted: m()",44
                );
        
    }
    
    @Test
    public void testPureAssign() {
        helpTC(" class A {  boolean b,bb;  \n //@ invariant (b=bb); \n}"
                ,"/TEST.java:2: Assignments are not allowed where pure expressions are expected",18
                );
    }

    @Test
    public void testPureAssignOp() {
        helpTC(" class A {  int b,bb;  \n //@ invariant (b+=bb)==0; \n}"
                ,"/TEST.java:2: Assignments are not allowed where pure expressions are expected",18
                );
    }

    @Test
    public void testPureIncrement() {
        helpTC(" class A {  int b,bb;  \n //@ invariant 0==(++b); \n}"
                ,"/TEST.java:2: Increment and decrement operators are not allowed where pure expressions are expected",20
                );
    }

    @Test
    public void testPureIncrement2() {
        helpTC(" class A {  int b,bb;  \n //@ invariant 0==(b++); \n}"
                ,"/TEST.java:2: Increment and decrement operators are not allowed where pure expressions are expected",21
                );
    }

    @Test
    public void testPureDecrement() {
        helpTC(" class A {  int b,bb;  \n //@ invariant 0==(--b); \n}"
                ,"/TEST.java:2: Increment and decrement operators are not allowed where pure expressions are expected",20
                );
    }

    @Test
    public void testPureDecrement2() {
        helpTC(" class A {  int b,bb;  \n //@ invariant 0==(b--); \n}"
                ,"/TEST.java:2: Increment and decrement operators are not allowed where pure expressions are expected",21
                );
    }

    /** Test a method in a pure class */
    @Test
    public void testPureClass() {
        helpTC(" class A extends B {  \n //@ invariant mm(); \n} /*@ pure */ class B { boolean mm() { return true; } }"
                );
    }

    /** Test that pure is not inherited */
    @Test
    public void testPureClass2() {
        expectedExit = 0;
        helpTC(" class A extends B { boolean mm() { return true; } \n //@ invariant mm(); \n} /*@ pure */ class B { boolean mm() { return true; } }"
                ,"/TEST.java:2: warning: A non-pure method is being called where it is not permitted: mm()",18
                );
    }

    /** Test that pure from enclosing class does not apply */  // FIXME - this is a question for JML
    @Test
    public void testPureClass3() {
        expectedExit = 0;
        helpTC(" /*@ pure */ class A  {  static class B { //@ invariant mm(); \n boolean mm() { return true; } }\n } "
                ,"/TEST.java:1: warning: A non-pure method is being called where it is not permitted: mm()",59
                );
    }


}
