package tests;

import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.util.Options;

public class escnew extends EscBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        options.put("-newesc","");
        options.put("-noPurityCheck","");
        //options.put("-jmlverbose",   "");
        //options.put("-showbb",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }

    // Just testing binary and unary 
    public void testBinaryUnary() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result ==4;\n"
                +"  public int m1bad() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 3;\n"
                +"  public int m1ok() {\n"
                +"    return 1 + 2;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result < 0;\n"
                +"  public int m2bad(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                +"  //@ requires x >= 0;\n"
                +"  //@ ensures \\result <= 0;\n"
                +"  public int m2ok(int x) {\n"
                +"    return -x;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: warning: Associated declaration",7
                );
    }

    public void testConditional() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result >= i;\n"
                +"  public int m1ok(boolean b, int i) {\n"
                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    public void testBoolOpsParens() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m1bad(boolean p, boolean q) {\n"
                +"    return p == q;\n"
                +"  }\n"
                
                +"  //@ requires p && q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m1ok(boolean p, boolean q) {\n"
                +"    return ((p == q)) ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m2bad(boolean p, boolean q) {\n"
                +"    return p != q;\n"
                +"  }\n"
                
                +"  //@ requires p && !q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m2ok(boolean p, boolean q) {\n"
                +"    return p != q ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m3bad(boolean p, boolean q) {\n"
                +"    return p == !q;\n"
                +"  }\n"
                
                +"  //@ requires p && !q;\n"
                +"  //@ ensures \\result;\n"
                +"  public boolean m3ok(boolean p, boolean q) {\n"
                +"    return p == !q ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:14: warning: Associated declaration",7
                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:24: warning: Associated declaration",7
                );
    }

    public void testSelect() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m1bad() {\n"
                +"    return this.f ;\n"
                +"  }\n"
                
                +"  //@ requires this.f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m1ok() {\n"
                +"    return this.f ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m2bad() {\n"
                +"    return f ;\n"
                +"  }\n"
                
                +"  //@ requires f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m2ok() {\n"
                +"    return f ;\n"
                +"  }\n"
                
                +"  //@ requires f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m3bad(TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                +"  //@ requires true;\n"
                +"  //@ ensures true;\n"
                +"  public int m3bad2(/*@nullable*/ TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                +"  //@ requires p.f == 1;\n"
                +"  //@ ensures \\result == 1;\n"
                +"  public int m3ok(TestJava p) {\n"
                +"    return p.f ;\n"
                +"  }\n"
                
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                ,"/tt/TestJava.java:15: warning: Associated declaration",7
                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:25: warning: Associated declaration",7
                ,"/tt/TestJava.java:32: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m3bad2",13
                );
    }

    public void testArrayIndex() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1bad(int[] a) {\n"
                +"    return a[10] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1bada(int[] a) {\n"
                +"    return a[-1] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1badb(int[] a, int i) {\n"
                +"    return a[i] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1good(int[] a) {\n"
                +"    return a[0] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  public int m1gooda(int[] a) {\n"
                +"    return a[9] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  //@ requires i >= 3;\n"
                +"  //@ requires i <= 8;\n"
                +"  public int m1goodb(int[] a, int i) {\n"
                +"    return a[i] ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",13
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",13
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1badb",-13
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",-13
                );
    }

    public void testArrayValue() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  //@ ensures \\result == a[1];\n"
                +"  public int m1bad(int[] a) {\n"
                +"    return a[0] ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 10;\n"
                +"  //@ ensures \\result == a[0];\n"
                +"  public int m1good(int[] a) {\n"
                +"    return a[0] ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: warning: Associated declaration",7
                );
    }

    public void testAssignOp() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ ensures \\result == j;\n"
                +"  public int m1bad(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == j+1;\n"
                +"  public int m1good(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    public void testChangedParam() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ ensures \\result == i;\n"
                +"  public int m1bad(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == i+1;\n"
                +"  public int m1good(int i) {\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                );
    }

    public void testNonNullField() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public Object nnf;\n"
                +"  public /*@ nullable*/ Object f;\n"

                // FIXME - these crash Z3
//                +"  public Object m1bad() {\n"
//                +"    return this.f ;\n"
//                +"  }\n"
//                
//                +"  public Object m1ok() {\n"
//                +"    return this.nnf ;\n"
//                +"  }\n"
                
                +"  public void m2bad() {\n"
                +"    nnf = null ;\n"
                +"  }\n"
                
//                +"  public void m2ok() {\n"
//                +"    f = null ;\n"
//                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",9
                );
    }

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
    
    public void testAssignment() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(boolean i) {\n"
                +"    int x = 0 ;\n"
                +"    if (i) x = 1; else x = 2; ;\n"
                +"    x = x + 1 ;\n"
                +"    //@ assert x < 3 ;\n"
                +"  }\n"
                
                +"  public void m1ok(boolean i) {\n"
                +"    int x = 0 ;\n"
                +"    if (i) x = 1; else x = 2; ;\n"
                +"    x = x + 1 ;\n"
                +"    //@ assert x < 4 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                );    }

    public void testUndefined() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires 10/i < 0;\n"
                +"  public void m1bad(int i) {\n"
                +"  }\n"
                
                +"  //@ requires i != 0 && 10/i < 0;\n"
                +"  public void m1good(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures 10/i < 0 || true;\n"
                +"  public void m2bad(int i) {\n"
                +"  }\n"
                
                +"  //@ ensures i == 0 || 10/i < 0 || true;\n"
                +"  public void m2good(int i) {\n"
                +"  }\n"
                
                +"  public void m3bad(int i) {\n"
                +"  //@ assume 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m3good(int i) {\n"
                +"  //@ assume i == 0 || 10/i < 0 || true;\n"
                +"  }\n"
                
                +"  public void m4bad(int i) {\n"
                +"  //@ assert 10/i < 0 ||true;\n"
                +"  }\n"
                
                +"  public void m4good(int i) {\n"
                +"  //@ assert i == 0 || 10/i < 0 || true;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m1bad",18
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m2bad",17
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m3bad",16
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4bad",16
                );    }

}
