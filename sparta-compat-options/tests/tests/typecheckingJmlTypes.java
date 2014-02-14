package tests;

import org.junit.Test;

public class typecheckingJmlTypes extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
        main.addOptions("-no-purityCheck");
    }

    @Test public void testBigint() {
        helpTC(" class A { //@ ghost \\bigint b = 0; \n}");
    }

    @Test public void testReal() {
        helpTC(" class A { //@ ghost \\real b = 0; \n}");
    }

    @Test public void testTYPE() {
        helpTC(" class A { //@ ghost \\TYPE b ; \n}");
    }

    @Test public void testMinusBigint() {
        helpTC(" class A { //@ ghost \\bigint b = 0; ghost \\bigint bb = -b; \n}");
    }

    @Test public void testBinaryBigint() {
        helpTC(" class A { void m() { //@ ghost \\bigint b = 0; ghost \\bigint bb = b + b; set bb = b-b; set bb = b*b; set bb = b/b; \n}}");
    }

    
    
}
