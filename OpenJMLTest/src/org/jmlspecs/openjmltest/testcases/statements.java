package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class statements extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    @Test public void testFor() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_invariant i>=0; decreasing -i; \n for (int i=0; i<10; i++) {}  \n}}"
                );
    }

    @Test public void testForWithModifies() {
        helpTCF("A.java"," class A { int k; void m() { \n //@  loop_modifies k; loop_invariant i>=0; decreasing -i;\n for (int i=0; i<10; i++) {}  \n}}"
                );
    }

    @Test public void testForWithModifies2() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_modifies x; \n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: error: cannot find symbol\n  symbol:   variable x\n  location: class A",20
                );
    }

    @Test public void testForWithModifies2a() {
        helpTCF("A.java"," class A { int j; void m() { \n //@ loop_modifies j; \n for (int i=0; i<10; i++) {}  \n}}"
                );
    }

    @Test public void testForWithModifies3() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_modifies \\nothing; \n for (int i=0; i<10; i++) {}  \n}}"
                );
    }

    @Test public void testForWithModifies4() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_modifies \\everything; \n for (int i=0; i<10; i++) {}  \n}}"
                );
    }

    @Test public void testForWithModifies5() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_modifies ; \n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: error: Use \\nothing to denote an empty list of locations in an assignable clause",20
                );
    }

    @Test public void testForWithModifies6() {
        helpTCF("A.java"," class A { int k; void m() { \n //@ loop_modifies k[; \n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: error: illegal start of expression",22
                ,"/A.java:2: error: An invalid expression or succeeding token near here",24
                );
    }

    @Test public void testForWithModifies6a() {
        helpTCF("A.java"," class A { int k; void m() { \n //@ loop_modifies k.; \n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: error: Expected an identifier or star after the dot",22
                );
    }

    @Test public void testForWithModifies7() {
        helpTCF("A.java"," class A { int k; void m() { \n //@ loop_modifies k k k; \n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: error: Missing comma or otherwise ill-formed type name",22
                ,"/A.java:2: error: Missing comma or otherwise ill-formed type name",24
                );
    }

    @Test public void testForWithModifies8() {
        helpTCF("A.java"," class A { int k; void m() { \n //@ loop_modifies k,,; \n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: error: Incorrectly formed or terminated store-reference near here",22
                ,"/A.java:2: error: Incorrectly formed or terminated store-reference near here",23
                );
    }

    @Test public void testForEach() {
        helpTCF("A.java"," class A { void m(java.util.List list) { \n //@ loop_invariant o != null; decreasing 6; \n for (Object o: list) {}  \n}}"
                );
    }

    @Test public void testWhile() {
        helpTCF("A.java"," class A { void m() { int i = 0; \n //@ loop_invariant i>=0; decreasing i; \n while (i>=0) {}  \n}}"
                );
    }

    @Test public void testFor2() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_invariant j;\n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: error: cannot find symbol\n  symbol:   variable j\n  location: class A",21
                );
    }

    @Test public void testLoop() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_invariant j;\n int a = 0;  \n}}"
        		,"/A.java:3: error: variable declaration not allowed here",6
                ,"/A.java:2: error: Loop specifications must immediately precede a loop statement",6
                );
    }

    @Test public void testLoop2() {
        helpTCF("A.java"," class A { boolean j; void m() { \n //@ loop_invariant j;\n  \n}}"
        		,"/A.java:4: error: illegal start of statement",1
                ,"/A.java:2: error: Loop specifications must immediately precede a loop statement",6
                );
    }
    
    @Test public void testLoop3() {
        helpTCF("A.java"," class A { boolean j; void m() { \n //@ loop_invariant j;\n j=true; \n}}"
                ,"/A.java:2: error: Loop specifications must immediately precede a loop statement",6
                );
    }
    
    @Test public void testAssert() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume true; assert o==o;*/\n  \n}}"
                );
    }

    @Test public void testAssert1() {
        helpTCF("A.java"," class A { Object o; void m() { \n //@ assume true: \"a\"; \n//@ assert false: \"b\";\n  \n}}"
                );
    }

    @Test public void testAssert2() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume 0; assert o;*/\n  \n}}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",13
                ,"/A.java:2: error: incompatible types: java.lang.Object cannot be converted to boolean",23
                );
    }

    @Test public void testAssert3() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume ; assert ;*/\n  \n}}"
                ,"/A.java:2: error: illegal start of expression",13
                );
    }

    @Test public void testAssert4() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume true assert false;*/\n  \n}}"
                ,"/A.java:2: error: Incorrectly formed or terminated assume statement near here -- perhaps a missing semicolon",17
                );
    }

    @Test public void testUnreachable() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ unreachable; \n i = 0; \n}}"
                );
    }

    @Test public void testUnreachable1() {
    	expectedExit = 0;
    	main.addOptions("-lang=jml");
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ unreachable \n i = 0; \n}}"
                //,"/A.java:2: warning: Inserting missing semicolon at the end of a unreachable statement",16
                );
    }

    @Test public void testSet() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; set j = 1; \n i = 0; \n}}"
                );
    }

    @Test public void testSet1() {
        expectedExit = 1;
        helpTCF("A.java"," class A { void m() { int i; \n //@ ghost int j; set j = 1 \n i = 0; \n}}"
                ,"/A.java:2: error: ';' expected",28
                );
    }
    
    @Test public void testSet1a() {
        expectedExit = 1;
        helpTCF("A.java"," class A { void m() { int i; \n //@ ghost int j; set j = 1 \n; i = 0; \n}}"
                ,"/A.java:2: error: ';' expected",28
                );
    }
    
    @Test public void testSet2() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; set if (true) {}; \n i = 0; \n}}"
                //,"/A.java:2: A set or debug statement may only contain assignments or method calls",23
                );
    }
    
    @Test public void testSet3() {
        helpTCF("A.java"," class A { boolean o; void m() { int i; \n //@ ghost boolean j; set j =  (o <==> \\old(o)); \n i = 0; \n}}"
                );
    }
    
//    @Test public void testDebug() {
//        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; debug m(); \n i = 0; \n}}"
//                );
//    }
//
//    @Test public void testDebug1() {
//        expectedExit = 1;
//        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; debug m() \n i = 0; \n}}"
//                ,"/A.java:2: error: ';' expected",28
//                );
//    }
//
//    @Test public void testDebug2() {
//        helpTCF("A.java"," class A { Object o; void m() { int i=0; \n //@ ghost int j; debug while (i>0) {}; \n i = 0; \n}}"
//                );
//    }
//
    @Test public void testDecl() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; final ghost int k = 0; \n i = 0; \n}}"
                );
    }

    @Test public void testDec2() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; ghost final int k = 0; \n i = 0; \n}}"
                );
    }

    @Test public void testSpecs1() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ refining ensures i ==0; \n i = 0; \n}}"
                );
    }

    @Test public void testSpecs2() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ refining normal_behavior ensures i ==0; also behavior ensures i >= 0; \n i = 0; \n}}"
                );
    }

    @Test public void testSpecs3() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ refining also ensures i ==0; \n i = 0; \n}}"
                ,"/A.java:2: error: An also token may not follow a refining token",15
                );
    }

    @Test public void testSpecs4() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ refining public behavior ensures i ==0; \n i = 0; \n}}"
                ,"/A.java:2: error: No modifiers are allowed in the body of a refining statement",15
                );
    }

    @Test public void testSynchronized1() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n synchronized (this) { i = 0; } \n}}"
                );
    }

    @Test public void testSynchronized2() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n synchronized (this) { i = 0; } \n}}"
                );
    }

    @Test public void testSynchronized3() {
        helpTCF("A.java"," class A { Object o; synchronized void m() { int i; \n  { i = 0; } \n}}"
                );
    }

    @Test public void testSynchronized() {
        helpTCF("A.java"," public class A { void m() { \n synchronized (this) { ; } \n}}"
                );
    }

    @Test public void testSynchronized4() { // Bug 3316767
        helpTCF("A.java"," public class A { void m() { \n synchronized (this) {  } \n}}"
                );
    }

    @Test public void testEmptyBlock() { // Bug 3316853
        helpTCF("A.java"," public class A { void m() { { } }  { { } } static { { } }  }"
                );
    }


// TODO - need tests for hence_by; test for local specification cases; tests for pure methods in expressions
}
