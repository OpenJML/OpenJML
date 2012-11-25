package tests;

public class escold extends escnew {

    public void setUp() throws Exception {
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

    // Messages have a different location
    public void testExplicitAssert() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  public void m1ok(int i) {\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  public void m1okb(int i) {\n"
                +"    //@ assume i == 0 ;\n"
                +"    //@ assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  public void m2bad(int i) {\n"
                +"    assert i == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires i == 0;\n"
                +"  public void m2ok(int i) {\n"
                +"    assert i == 0 : \"ASD\" ;\n"
                +"  }\n"
                
                +"  public void m2okb(int i) {\n"
                +"    //@ assume i == 0 ;\n"
                +"    assert i == 0 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m2bad",12
                );
    }
    

    public void testBox() {
        // Was not implemented in old esc
    }
    
//    public void testAssignable2() {
//        // FIXME - skip until problem in escnew is fixed
//    }
    
    public void testNullThrow() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testUnreachable() {
        // FIXME - skip until problem in escnew is fixed
    }
    
    public void testNullSynchronized() {
        // old esc did not check for this problem
    }
    
    public void testShortCircuit() {}
    public void testAssignOp() {}
    public void testGhostSetNoDebug() {}

    
    public void testPostcondition4() {
        // old esc did not check for this problem
    }
    
    public void testHavoc() {
        // old esc did not implement havoc
    }
    
//    public void testAssignable5() {
//        noAssociatedDeclaration = true;
//        super.testAssignable5();
//    }
//    
//    public void testAssignable1() {
//        noAssociatedDeclaration = true;
//        super.testAssignable5();
//    }
//    
//    public void testAssignable3() {
//        noAssociatedDeclaration = true;
//        super.testAssignable5();
//    }
//    
//    public void testAssignable4() {
//        noAssociatedDeclaration = true;
//        super.testAssignable5();
//    }
//    
//    public void testAssignable6() {
//        noAssociatedDeclaration = true;
//        super.testAssignable5();
//    }
}
