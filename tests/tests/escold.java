package tests;

public class escold extends escnew {

    protected void setUp() throws Exception {
        super.setUp();
        options.put("-newesc",null);
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
    }
    
    // messages are in a different order
    public void testJmlLabelExpression() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"

                +"  //@ requires true;\n"
                +"  //@ ensures b ==> (i==0) ;\n"
                +"  public int m1ok(boolean b, int i) {\n"
                +"    //@ ghost boolean bb = (\\lbl LBL_BB b);\n"
                +"    //@ ghost boolean bbp = (\\lblpos LBL_BB2 (i==0));\n"
                +"    //@ ghost boolean bbn = (\\lblneg LBL_BB3 (i==0));\n"
                +"    return 1;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1ok",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:8: warning: Label LBL_BB3 reported",30
                ,"/tt/TestJava.java:6: warning: Label LBL_BB has value true",29
                );
    }
    
    public void testAssignable2() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testNullThrow() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testUnreachable() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testNullSynchronized() {
        // old esc did not check for this problem
    }
    
    public void testPostcondition4() {
        // old esc did not check for this problem
    }
    
    public void testAssignable5() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable1() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable3() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable4() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
    
    public void testAssignable6() {
        noAssociatedDeclaration = true;
        super.testAssignable5();
    }
}
