package tests;

public class statements extends TCBase {


    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    public void testFor() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_invariant i>=0; decreasing -i; \n for (int i=0; i<10; i++) {}  \n}}"
                );
    }

    public void testForEach() {
        helpTCF("A.java"," class A { void m(java.util.List list) { \n //@ loop_invariant o != null; decreasing 6; \n for (Object o: list) {}  \n}}"
                );
    }

    public void testWhile() {
        helpTCF("A.java"," class A { void m() { int i = 0; \n //@ loop_invariant i>=0; decreasing i; \n while (i>=0) {}  \n}}"
                );
    }

    public void testFor2() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_invariant j;\n for (int i=0; i<10; i++) {}  \n}}"
                ,"/A.java:2: cannot find symbol\nsymbol  : variable j\nlocation: class A",21
                );
    }

    public void testLoop() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_invariant j;\n int a = 0;  \n}}"
                ,"/A.java:2: Loop specifications must immediately precede a while or for statement",6
                );
    }

    public void testLoop2() {
        helpTCF("A.java"," class A { void m() { \n //@ loop_invariant j;\n  \n}}"
                ,"/A.java:2: Loop specifications must immediately precede a while or for statement",6
                );
    }
    
    public void testAssert() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume true; assert o==o;*/\n  \n}}"
                );
    }

    public void testAssert1() {
        helpTCF("A.java"," class A { Object o; void m() { \n //@ assume true: \"a\"; \n//@ assert false: \"b\";\n  \n}}"
                );
    }

    public void testAssert2() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume 0; assert o;*/\n  \n}}"
                ,"/A.java:2: incompatible types\nfound   : int\nrequired: boolean",13
                ,"/A.java:2: incompatible types\nfound   : java.lang.Object\nrequired: boolean",23
                );
    }

    public void testAssert3() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume ; assert ;*/\n  \n}}"
                ,"/A.java:2: illegal start of expression",13
                ,"/A.java:2: illegal start of expression",22
                );
    }

    public void testAssert4() {
        helpTCF("A.java"," class A { Object o; void m() { \n /*@ assume true assert false;*/\n  \n}}"
                ,"/A.java:2: Incorrectly formed or terminated assume statement near here",18
                );
    }

    public void testUnreachable() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ unreachable; \n i = 0; \n}}"
                );
    }

    public void testUnreachable1() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ unreachable \n i = 0; \n}}"
                ,"/A.java:2: Incorrectly formed or terminated unreachable statement near here",18
                );
    }

    public void testSet() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; set j = 1; \n i = 0; \n}}"
                );
    }

    public void testSet1() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; set j = 1 \n i = 0; \n}}"
                ,"/A.java:2: ';' expected",28
                );
    }
    
    public void testDebug() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; debug m(); \n i = 0; \n}}"
                );
    }

    public void testDebug1() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; debug m() \n i = 0; \n}}"
                ,"/A.java:2: ';' expected",28
                );
    }

    public void testDecl() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; final ghost int k = 0; \n i = 0; \n}}"
                );
    }

    public void testDec2() {
        helpTCF("A.java"," class A { Object o; void m() { int i; \n //@ ghost int j; ghost final int k = 0; \n i = 0; \n}}"
                );
    }

// TODO - need tests for hence_by; test for local specification cases; tests for pure methods in expressions
}
