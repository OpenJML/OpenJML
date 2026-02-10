package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class purity extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        addOptions("--no-require-white-space");
    }

    /** Test scanning something very simple */
    @Test
    public void testPure() {
        helpTCText(null, " class A { /*@ pure */ boolean m() { return true; }  \n //@ invariant m(); \n}"
                );
    }

    /** Test scanning something very simple */
    @Test
    public void testSpecPure() {
        helpTCText(null, " class A { /*@ spec_pure */ boolean m() { return true; }  \n //@ invariant m(); \n}"
                );
    }

    /** Test scanning something very simple */
    @Test
    public void testStrictlyPure() {
        helpTCText(null, " class A { /*@ strictly_pure */ boolean m() { return true; }  \n //@ invariant m(); \n}"
                );
    }

    /** Test scanning something very simple */
    @Test
    public void testPure2() {
        expectedExit = 0;
        helpTCText(null, " class A {  boolean m() { return true; }  \n //@ invariant m(); \n}"
               ,"/TEST.java:2: warning: A non-pure method is being called where it is not permitted: A.m()",17
               );
    }
    
    @Test
    public void testSpecFile() {
        addMockFile("$A/A.jml","public class A { /*@pure*/ int m();  //@ invariant m() == 0; \n}");
        helpTCText("A.java","public class A {  int m() { return 0; }  \n }"
                );
        
    }

    @Test
    public void testSpecFile2() {
        expectedExit = 0;
        addMockFile("$A/A.jml","public class A {  int m();  //@ invariant m() == 0; \n}");
        helpTCText("A.java","public class A {  int m() { return 0; }  \n }"
                ,"/$A/A.jml:1: warning: A non-pure method is being called where it is not permitted: A.m()",44
                );
        
    }
    
    @Test
    public void testSpecFile3() {
        expectedExit = 0;
        addMockFile("$A/A.jml","public class A {  /*@ pure */ int m();  //@ invariant m() == 0; \n}");
        helpTCText("A.java","public class A {  int m() { return 0; }  \n }"
                );
        
    }
    
    @Test
    public void testSpecFile3a() {
        expectedExit = 0;
        addMockFile("$A/A.jml","public class A {  int m();  //@ invariant m() == 0; \n}");
        helpTCText("A.java","public class A {  int m() { return 0; }  \n }"
                ,"/$A/A.jml:1: warning: A non-pure method is being called where it is not permitted: A.m()",44
                );
        
    }
    
    @Test
    public void testPureAssign() {
        helpTCText(null, " class A {  boolean b,bb;  \n //@ invariant (b=bb); \n}"
                ,"/TEST.java:2: error: Assignments are not allowed where pure expressions are expected",18
                );
    }

    @Test
    public void testPureAssignOp() {
        helpTCText(null, " class A {  int b,bb;  \n //@ invariant (b+=bb)==0; \n}"
                ,"/TEST.java:2: error: Assignments are not allowed where pure expressions are expected",18
                );
    }

    @Test
    public void testModelMethodIncDec() {
        expectedExit = 6; // Doing an esc run so the assignable clause is checked
        addOptions("--esc", "--spec-math=java"); // FIXME - : `THIS.b should be a non-translated expression
        helpTCText(null, " class A {  int b;  \n //@ pure model boolean m() { return (b++)==(++b) && (b--) == (--b); } \n}"
                ,anyorder(
                seq("/TEST.java:2: verify: The prover cannot establish an assertion (Assignable: /TEST.java:2:) in method m: `THIS.b",46
                ,"/TEST.java:2: verify: Associated declaration: /TEST.java:2:",6
                )
                ,seq("/TEST.java:2: verify: The prover cannot establish an assertion (Assignable: /TEST.java:2:) in method m: `THIS.b",40
                ,"/TEST.java:2: verify: Associated declaration: /TEST.java:2:",6
                )
                )
                );
    }

    @Test
    public void testMethodIncDec() {
        expectedExit = 6; // Doing an esc run so the assignable clause is checked
        addOptions("--esc", "--code-math=java");
        helpTCText(null, " class A {  int b;  \n //@ pure \n boolean m() { return (b++)==(++b) && (b--) == (--b); } \n}"
                ,anyorder(
                seq("/TEST.java:3: verify: The prover cannot establish an assertion (Assignable: /TEST.java:2:) in method m: `THIS.b",31
                ,"/TEST.java:2: verify: Associated declaration: /TEST.java:3:",6
                )
                ,seq("/TEST.java:3: verify: The prover cannot establish an assertion (Assignable: /TEST.java:2:) in method m: `THIS.b",25
                ,"/TEST.java:2: verify: Associated declaration: /TEST.java:3:",6
                )
                )
                );
    }

    @Test
    public void testPureIncrement() {
        helpTCText(null, " class A {  int b;  \n //@ invariant 0==(++b); \n}"
                ,"/TEST.java:2: error: Increment and decrement operators are not allowed where pure expressions are expected",20
                );
    }

    @Test
    public void testPureIncrement2() {
        helpTCText(null, " class A {  int b,bb;  \n //@ invariant 0==(b++); \n}"
                ,"/TEST.java:2: error: Increment and decrement operators are not allowed where pure expressions are expected",21
                );
    }

    @Test
    public void testPureDecrement() {
        helpTCText(null, " class A {  int b,bb;  \n //@ invariant 0==(--b); \n}"
                ,"/TEST.java:2: error: Increment and decrement operators are not allowed where pure expressions are expected",20
                );
    }

    @Test
    public void testPureDecrement2() {
        helpTCText(null, " class A {  int b,bb;  \n //@ invariant 0==(b--); \n}"
                ,"/TEST.java:2: error: Increment and decrement operators are not allowed where pure expressions are expected",21
                );
    }

    @Test
    public void testPureArrayAllocation() {
        helpTCText(null, " class A {  /*@ strictly_pure */ void m() { var a = new int[5]; }}"
                ,"/TEST.java:1: error: Array allocations are not permitted in strictly_pure methods",53
                ,"/TEST.java:1: error: Associated declaration: /TEST.java:1:",17
                );
    }

    @Test
    public void testPureObjectAllocation() {
        helpTCText(null, " class A {  /*@ strictly_pure */ void m() { var a = new Object(); }}"
                ,"/TEST.java:1: error: Object allocations are not permitted in strictly_pure methods",53
                ,"/TEST.java:1: error: Associated declaration: /TEST.java:1:",17
                );
    }

    /** Test a method in a pure class */
    @Test
    public void testPureClass() {
        helpTCText(null, " class A extends B {  \n //@ invariant mm(); \n} /*@ pure */ class B { boolean mm() { return true; } }"
                );
    }

    /** Test that pure is inherited by method */
    @Test
    public void testPureClass2() {
        expectedExit = 0;
        helpTCText(null, " class A extends B { boolean mm() { return true; } \n //@ invariant mm(); \n} /*@ pure */ class B { boolean mm() { return true; } }"
                );
    }

    /** Test that pure is not inherited by class */
    @Test
    public void testPureClass2a() {
        expectedExit = 0;
        helpTCText(null, " class A extends B { boolean mm() { return true; } \n //@ invariant mm(); \n} /*@ pure */ class B {  }"
                ,"/TEST.java:2: warning: A non-pure method is being called where it is not permitted: A.mm()",18
                );
    }

    /** Test that pure from enclosing class does apply */
    @Test
    public void testPureClass3() {
        helpTCText(null, " /*@ pure */ class A  {  static class B { //@ invariant mm(); \n boolean mm() { return true; } }\n } "
                );
    }

    @Test
    public void testCollection() {
        helpTCText(null, " class A { /*@ pure */ public int m(java.util.Vector v) { return v.size(); }\n } "
                );
    }

    @Test
    public void testCollection2() {
        helpTCText(null, " class A  {  public void m(java.util.Vector v) { //@ assert 0 == v.size(); \n }} "
                );
    }

    @Test
    public void testCollection3() {
        helpTCText(null, " class A  {  public void m(java.util.Vector v) { //@ assert 0 == v.size(); }\n } " // Intentional typo
                ,"/TEST.java:2: error: illegal start of type", 2
                ,"/TEST.java:2: error: reached end of file while parsing", 3
                );
    }

    @Test
    public void testPureNotSpecPure() {
        expectedExit = 0;
        helpTCText(null, " class A { /*@ pure */ Object m() { return new Object(); }  \n //@ invariant m() != null; \n}"
                ,"/TEST.java:2: warning: A non-pure method is being called where it is not permitted: A.m()", 17
                );
    }
    

}
