package tests;

import java.util.ArrayList;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class escall3 extends EscBase {

    public escall3(String option, String solver) {
        super(option,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        main.addOptions("-noPurityCheck");

        //options.put("-jmlverbose",   "");
        //options.put("-method",   "m2bad");
        //options.put("-showbb",   "");
        //options.put("-jmldebug",   "");
        //options.put("-noInternalSpecs",   "");
        //options.put("-showce",   "");
        //options.put("-trace",   "");
        //JmlEsc.escdebug = true;
        //org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        //print = true;
    }
    
    @Test
    public void testSimple() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>=0;\n"
                +"  public void m2bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>=0;\n"
                +"  //@ ensures \\result>0;\n"
                +"  public int m3bad(int i) {\n"
                +"    return i ;\n"
                +"  }\n"
                
                +"  public void m1good(int i) {\n"
                +"    //@ assume i>0 ;\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m2good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>=0;\n"
                +"  //@ ensures \\result>=0;\n"
                +"  public int m3good(int i) {\n"
                +"    return i ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ also\n"
                +"  //@ requires i==0;\n"
                +"  public void m4good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2bad",9
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:12: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testFieldAccess() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                 
                +"  int f; \n"
                
                +"  public void m1bad(TestJava o) {\n"
                +"    //@ assume o.f >0 ;\n"
                +"    //@ assert f > 0 ;\n"
                +"  }\n"
                
                +"  public void m2bad(@Nullable TestJava o) {\n"
                +"    //@ assume o.f >0 ;\n"
                +"  }\n"
                
                +"  public void m1good(TestJava o) {\n"
                +"    //@ assume o.f >0 ;\n"
                +"    //@ assume o == this ;\n"
                +"    //@ assert f > 0 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m2bad",17
                );
    }
    
    @Test
    public void testArrayAccess() {
        helpTCX("tt.TestJava","package tt; \n"
                +"import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires a.length > 5; \n"
                +"  public void m1bad(@Nullable int[] a) {\n"
                +"    //@ assume a[1] == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  public void m2bad(int[] a) {\n"
                +"    //@ assume a[1] == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  //@ requires a.length > 5; \n"
                +"  public void m3bad(int[] a) {\n"
                +"    //@ assume a[-1] == 0 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  //@ requires a.length > 5; \n"
                +"  //@ requires b.length > 5; \n"
                +"  public void m4bad(int[] a, int[] b) {\n"
                +"    //@ assume a[1] == 5 ;\n"
                +"    //@ assert b[1] == 5 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  //@ requires a.length > 5; \n"
                +"  public void m1good(int[] a, int[] b) {\n"
                +"    //@ assume a[1] == 5 ;\n"
                +"    //@ assume a == b ;\n"
                +"    //@ assert b[1] ==5 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1bad",17
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m2bad",17
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m3bad",17
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assert) in method m4bad",9
                );
    }
    
    @Test
    public void testArrayAssign() {
        helpTCX("tt.TestJava","package tt; \n"
                +"import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires a.length > 5; \n"
                +"  public void m1bad(@Nullable int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  public void m2bad(int[] a) {\n"
                +"    a[1] = 0 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  //@ requires a.length > 5; \n"
                +"  public void m3bad(int[] a) {\n"
                +"    a[-1] = 0 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  //@ requires a.length > 5; \n"
                +"  //@ requires b.length > 5; \n"
                +"  public void m4bad(int[] a, int[] b) {\n"
                +"    a[1] = 5 ;\n"
                +"    //@ assert b[1] ==5 ;\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  //@ requires a.length > 5; \n"
                +"  public void m1good(int[] a, int[] b) {\n"
                +"    a[1] = 5;\n"
                +"    //@ assume a == b ;\n"
                +"    //@ assert b[1] ==5 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullReference) in method m1bad",17
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m2bad",6
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m3bad",6
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assert) in method m4bad",9
                );
    }
    
    @Test
    public void testFieldAssign() {
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                 
                +"  int f; \n"
                
                +"  public void m1bad(TestJava o) {\n"
                +"    o.f = 1 ;\n"
                +"    //@ assert f > 0 ;\n"
                +"  }\n"
                
                +"  public void m2bad(@Nullable TestJava o) {\n"
                +"    o.f = 1 ;\n"
                +"    // @ assert f > 0 ;\n"
                +"  }\n"
                
                +"  public void m1good(TestJava o) {\n"
                +"    o.f = 1 ;\n"
                +"    //@ assume o == this ;\n"
                +"    //@ assert f > 0 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m2bad",6
                );
    }
    
    @Test
    public void testPrecondition1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  \n"
                +"  public void m1bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>=0;\n"
                +"  public void m2bad(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m1good(int i) {\n"
                +"    //@ assert i>0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  public void m2good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ also\n"
                +"  //@ requires i==0;\n"
                +"  public void m3good(int i) {\n"
                +"    //@ assert i>=0 ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Assert) in method m2bad",9
                );
    }
    
    @Test
    public void testPrecondition2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires i>0;\n"
                +"  //@ ensures false;\n"
                +"  public void m1a(int i) {\n"
                +"  }\n"
                
                +"  //@ requires i>0;\n"
                +"  //@ requires i<0;\n"
                +"  //@ ensures false;\n"  // FIXME - this should eventually warn about infeasible preconditions
                +"  public void m1b(int i) {\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Postcondition) in method m1a",15
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:10: warning: Invariants+Preconditions appear to be contradictory in method m1b(int)",-15
                );
    }
    
//    @Test
//    public void testPrecondition3() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires a[i]>0;\n"
//                +"  public void m1bad(int[] a, int i) {\n"
//                +"  }\n"
//                
//                +"  //@ requires i >= 0 && i < a.length;\n"
//                +"  //@ requires a[i]>0;\n"
//                +"  public void m1good(int[] a, int i) {\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",17
//                );
//    }

//    public void testPostcondition1() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ signals (Exception) false;\n"
//                +"  public void m1bad(int[] a, int i) {\n"
//                +"    throw new RuntimeException(); \n"
//                +"  }\n"
//                
//                +"  //@ ensures false;\n"
//                +"  public void m2bad(int[] a, int i) {\n"
//                +"  }\n"
//                
//                +"  //@ ensures false;\n"
//                +"  public void m3bad(int[] a, int i) {\n"
//                +"     return;\n"
//                +"  }\n"
//                
//                +"  //@ ensures true;\n"
//                +"  //@ signals (Exception e)  false;\n"
//                +"  public void m1good(int[] a, int i) {\n"
//                +"  }\n"
//                
//                +"  //@ ensures false;\n"
//                +"  public void m2good(int[] a, int i) {\n"
//                +"    throw new RuntimeException(); \n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",5
//                ,"/tt/TestJava.java:3: warning: Associated declaration",7
//                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",15
//                ,"/tt/TestJava.java:7: warning: Associated declaration",7
//                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",6
//                ,"/tt/TestJava.java:10: warning: Associated declaration",7
//                );
//    }
//    
//    public void testPostcondition2() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires i == 0;\n"
//                +"  //@ ensures false;\n"
//                +"  //@ also\n"
//                +"  //@ requires i!= 0;\n"
//                +"  //@ ensures true;\n"
//                +"  public void m1bad(int[] a, int i) {\n"
//                +"      if (i == 0) \n"
//                +"         return;\n"
//                +"      else\n"
//                +"         return;\n"
//                +"  }\n"
//                
//                +"  //@ requires i == 0;\n"
//                +"  //@ ensures true;\n"
//                +"  //@ also\n"
//                +"  //@ requires i!= 0;\n"
//                +"  //@ ensures false;\n"
//                +"  public void m2bad(int[] a, int i) {\n"
//                +"      if (i == 0) \n"
//                +"         return;\n"
//                +"      else\n"
//                +"         return;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",10
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",10
//                ,"/tt/TestJava.java:18: warning: Associated declaration",7
//                );
//    }
//    
//    public void testPostcondition3() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires i == 0;\n"
//                +"  //@ signals (Exception e) false;\n"
//                +"  //@ also\n"
//                +"  //@ requires i!= 0;\n"
//                +"  //@ signals (Exception e) true;\n"
//                +"  public void m1bad(int[] a, int i) throws Exception {\n"
//                +"      if (i == 0) \n"
//                +"         throw new Exception();\n"
//                +"      else\n"
//                +"         throw new Exception();\n"
//                +"  }\n"
//                
//                +"  //@ requires i == 0;\n"
//                +"  //@ signals (Exception e) true;\n"
//                +"  //@ also\n"
//                +"  //@ requires i!= 0;\n"
//                +"  //@ signals (Exception e) false;\n"
//                +"  public void m2bad(int[] a, int i) throws Exception {\n"
//                +"      if (i == 0) \n"
//                +"         throw new Exception();\n"
//                +"      else\n"
//                +"         throw new Exception();\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2bad",10
//                ,"/tt/TestJava.java:18: warning: Associated declaration",7
//                );
//    }
//    
//    // Tests use of \exception token
//    public void testPostcondition4() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ signals (Exception e) \\exception == null;\n"
//                +"  public void m1bad(int[] a, int i) throws Exception {\n"
//                +"         throw new Exception();\n"
//                +"  }\n"
//                
//                +"  //@ signals (Exception e) \\exception != null;\n"
//                +"  public void m1good(int[] a, int i) throws Exception {\n"
//                +"         throw new Exception();\n"
//                +"  }\n"
//                
//                +"  //@ signals (Exception) \\exception != null;\n"
//                +"  public void m2good(int[] a, int i) throws Exception {\n"
//                +"         throw new Exception();\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",10
//                ,"/tt/TestJava.java:3: warning: Associated declaration",7
//                );
//    }
//    
//    public void testNullThrow() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1bad(int i) throws Exception {\n"
//                +"      if (i == 0) \n"
//                +"         throw null;\n"
//                +"  }\n"
//                
//                +"  public void m2bad(int i, /*@ nullable */ Exception e) throws Exception {\n"
//                +"      if (i == 0) \n"
//                +"         throw e;\n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0; \n"
//                +"  public void m1good(int i) throws Exception {\n"
//                +"      if (i == 0) \n"
//                +"         throw null;\n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0; \n"
//                +"  public void m2good(int i, Exception e) throws Exception {\n"
//                +"      if (i == 0) \n"
//                +"         throw e;\n"
//                +"  }\n"
//                
//                +"  public void m3good(int i, Exception e) throws Exception {\n"
//                +"      if (i == 0) \n"
//                +"         throw e;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1bad",16
//                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m2bad",16
//                );
//    }
//    
//    public void testNullSynchronized() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1bad(/*@ nullable */ Object o) throws Exception {\n"
//                +"       synchronized (o) {};\n"
//                +"  }\n"
//                
//                +"  public void m2bad( Object o) throws Exception {\n"
//                +"       synchronized (o) {\n"
//                +"          o = null; };\n"
//                +"  }\n"
//                
//                +"  public void m1good(Object o) throws Exception {\n"
//                +"       synchronized (o) {};\n"
//                +"  }\n"
//                
//                +"  public void m2good(Object o) throws Exception {\n"
//                +"       synchronized (this) {};\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1bad",21
//                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",13
//                );
//    }
//    
//    // FIXME - add checks on object fields, quantifier variables
//    // FIXME - need attribute checks on scopes of variables
//    public void testLabeled() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires i == 0; \n"
//                +"  public void m1good(int i) throws Exception {\n"
//                +"       int j = 0;\n"
//                +"       //@ assert j == 0;\n"
//                +"       a: j = 1; i = 1;\n"
//                +"       //@ assert \\old(i) == 0;\n"
//                +"       b: j = 2; i = 2;\n"
//                +"       //@ assert \\old(j,a) == 0;\n"
//                +"       //@ assert \\old(i,a) == 0;\n"
//                +"       //@ assert \\old(j,b) == 1;\n"
//                +"       //@ assert \\old(i,b) == 1;\n"
//                +"       //@ assert \\pre(i) == 0;\n"
//                +"       \n"
//                +"  }\n"
//                
//                +"}"
//                );
//    }
//    
//    public void testBox() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ ensures \\result == 7; \n"
//                +"  public int m1good()  {\n"
//                +"      Integer k = 7;\n"
//                +"      int i = k;\n"
//                +"      return i;\n"
//                +"  }\n"
//                +"  }\n"
//                
//                );
//    }
//    
//    public void testMethodInvocation() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public int z(int i)  {\n"
//                +"      return i;\n"
//                +"  }\n"
//                
//                +"  public int m1bad(int k)  {\n"
//                +"      int i = z(k/k);\n"
//                +"      return i;\n"
//                +"  }\n"
//                
//                +"  public void m2bad(int k)  {\n"
//                +"      z(k/k);\n"
//                +"  }\n"
//                
//                +"  //@ requires k > 0; \n"
//                +"  public int m1good(int k)  {\n"
//                +"      int i = z(k/k);\n"
//                +"      return i;\n"
//                +"  }\n"
//                +"  }\n"
//                
//                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",18
//                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",10
//
//                );
//    }
//    
//    public void testSwitch() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ ensures \\result == i* 2 + 1; \n"
//                +"  public int m1bad(int i) throws Exception {\n"
//                +"      int k;\n"
//                +"       switch (i) {\n"
//                +"        case 1: k = 3; break;\n"
//                +"        default: k = i + i + 1; break;\n"
//                +"        case 2: k = 6; return k;\n"
//                +"       } return k;\n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == i* 2 + 1; \n"
//                +"  public int m1good(int i) throws Exception {\n"
//                +"      int k;\n"
//                +"       switch (i) {\n"
//                +"        case 1: k = 3; break;\n"
//                +"        default: k = i + i + 1; break;\n"
//                +"        case 2: k = 5; break;\n"
//                +"       } return k;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",24
//                ,"/tt/TestJava.java:3: warning: Associated declaration",7
//                );
//    }
//    
//    public void testTry() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ ensures \\result == 1; \n"
//                +"  public int m1bad() throws Exception {\n"
//                +"      int k;\n"
//                +"       try {\n"
//                +"        k=1; \n"
//                +"       } finally {\n"
//                +"           k = 2;\n"
//                +"        }return k;\n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == 0; \n"
//                +"  public int m2bad() throws Exception {\n"
//                +"      int k;\n"
//                +"       try {\n"
//                +"        k=1; throw new RuntimeException();\n"
//                +"       } catch (RuntimeException e) {\n"
//                +"           k = 2;\n"
//                +"        } return k; \n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == 0; \n"
//                +"  public int m3bad() throws Exception {\n"
//                +"      int k;\n"
//                +"       try {\n"
//                +"        k=1; throw new RuntimeException();\n"
//                +"       } catch (RuntimeException e) {\n"
//                +"           k = 2;\n"
//                +"       } finally {\n"
//                +"           k = 3;\n"
//                +"        } return k; \n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == 1; \n"
//                +"  public int m1good() throws Exception {\n"
//                +"      int k;\n"
//                +"       try {\n"
//                +"        k=1; return k;\n"
//                +"       } finally {\n"
//                +"           k = 2;\n"
//                +"        } \n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == 2; \n"
//                +"  public int m0good() throws Exception {\n"
//                +"      int k;\n"
//                +"       try {\n"
//                +"        k=1; \n"
//                +"       } finally {\n"
//                +"           k = 2;\n"
//                +"        } return k;\n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == 2; \n"
//                +"  public int m2good() throws Exception {\n"
//                +"      int k;\n"
//                +"       try {\n"
//                +"        k=1; throw new RuntimeException();\n"
//                +"       } catch (RuntimeException e) {\n"
//                +"           k = 2;\n"
//                +"        } return k; \n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == 3; \n"
//                +"  public int m3good() throws Exception {\n"
//                +"      int k;\n"
//                +"       try {\n"
//                +"        k=1; throw new RuntimeException();\n"
//                +"       } catch (RuntimeException e) {\n"
//                +"           k = 2;\n"
//                +"       } finally {\n"
//                +"           k = 3\n;"
//                +"        } return k; \n"
//                +"  }\n"
//                
//                +"  static int kk;\n"
//
//                +"  //@ assignable kk;\n"
//                +"  //@ ensures \\result == 3; signals (Exception e)  false; \n"
//                +"  public int m4good(int i ) throws Exception {\n"
//                +"       try {\n"
//                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
//                +"       } catch (RuntimeException e) {\n"
//                +"           kk = 2;\n"
//                +"        } \n"
//                +"       kk = 3;\n"
//                +"       return kk; \n"
//                +"  }\n"
//                
//                +"  //@ assignable kk;\n"
//                +"  //@ ensures \\result == 3; signals (Exception e)  kk == 1; \n"
//                +"  public int m5good(int i) throws Exception {\n"
//                +"       try {\n"
//                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
//                +"        } finally {} \n"
//                +"       kk = 3;\n"
//                +"       return kk; \n"
//                +"  }\n"
//                
//                +"  //@ assignable kk;\n"
//                +"  //@ ensures \\result == 3; signals (Exception e)  kk == 1; \n"
//                +"  public int m6good(int i) throws Exception {\n"
//                +"        kk=1; if (i == 0) throw new RuntimeException();\n"
//                +"       kk = 3;\n"
//                +"       return kk; \n"
//                +"  }\n"
//                
//                +"  //@ assignable kk;\n"
//                +"  //@ ensures \\result == 3; signals (Exception e) kk == 4; \n"
//                +"  public int m7good(int i) throws Exception {\n"
//                +"       try {\n"
//                +"           kk=1; if (i == 0) throw new RuntimeException();\n"
//                +"           try {\n"
//                +"             kk=2; if (i == 1) throw new RuntimeException();\n"
//                +"           } finally { kk = 5; } \n"
//                +"       } finally { kk = 4; } \n"
//                +"       kk = 3;\n"
//                +"       return kk; \n"
//                +"  }\n"
//                
//                +"  //@ assignable kk;\n"
//                +"  //@ ensures i==0 ==> \\result == 4; signals (Exception e) false; \n"
//                +"  public int m8good(int i) throws Exception {\n"
//                +"       try {\n"
//                +"           kk=1; if (i == 0) throw new RuntimeException();\n"
//                +"       } finally { if (i == 0) return 4; } \n"
//                +"       kk = 3;\n"
//                +"       return kk; \n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",10
//                ,"/tt/TestJava.java:3: warning: Associated declaration",7
//                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",11
//                ,"/tt/TestJava.java:12: warning: Associated declaration",7
//                ,"/tt/TestJava.java:30: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",11
//                ,"/tt/TestJava.java:21: warning: Associated declaration",7
//                
//                );
//    }
//    
//    public void testUnreachable() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1bad(int i) {\n"
//                +"      if (i == 0) { \n"
//                +"         //@ unreachable;\n"
//                +"      }\n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0; \n"
//                +"  public void m1good(int i) {\n"
//                +"      if (i == 0) { \n"
//                +"         //@ unreachable;\n"
//                +"      }\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Unreachable) in method m1bad",14
//                );
//    }
//    
//
//    public void testGhostSet() {
//        //args = new String[] { "-keys=DEBUG" };
//        options.put(JmlOption.KEYS.optionName(), "DEBUG");
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1bad(int i) {\n"
//                +"      //@ ghost int k = 0;"
//                +"      //@ set k = 1;\n"
//                +"      //@ assert k == 0; \n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0; \n"
//                +"  public void m1good(int i) {\n"
//                +"      //@ ghost int k = 0;"
//                +"      //@ set k = 1;\n"
//                +"      //@ assert k == 1; \n"
//                +"  }\n"
//                
//                +"  public void m2bad(int i) {\n"
//                +"      //@ ghost int k = 0;"
//                +"      //@ debug k = 1;\n"
//                +"      //@ assert k == 0; \n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0; \n"
//                +"  public void m2good(int i) {\n"
//                +"      //@ ghost int k = 0;"
//                +"      //@ debug k = 1;\n"
//                +"      //@ assert k == 1; \n"
//                +"  }\n"
//
//                // FIXME - need to handle jml constructs in set, debug statements
////                +"  public void m3bad() {\n"
////                +"      //@ ghost boolean k = true;"
////                +"      //@ set k = (k <=!=> k);\n"
////                +"      //@ assert k; \n"
////                +"  }\n"
////                
////                +"  public void m3good() {\n"
////                +"      //@ ghost boolean k = true;"
////                +"      //@ set k = (k <==> k);\n"
////                +"      //@ assert k; \n"
////                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",11
//                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (Assert) in method m2bad",11
//                );
//    }
//    
//    public void testGhostSetNoDebug() {
//        // debug is not enabled 
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m2good(int i) {\n"
//                +"      //@ ghost int k = 0;"
//                +"      //@ debug k = 1;\n"
//                +"      //@ assert k == 0; \n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0; \n"
//                +"  public void m2bad(int i) {\n"
//                +"      //@ ghost int k = 0;"
//                +"      //@ debug k = 1;\n"
//                +"      //@ assert k == 1; \n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m2bad",11
//                );
//    }
//    
//    public void testHavoc() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1good() {\n"
//                +"      int i = 0; \n"
//                +"      //@ assert i == 0;\n"
//                +"  }\n"
//                
//                +"  public void m1bad() {\n"
//                +"      int i = 0; \n"
//                +"      //@ havoc i; \n"
//                +"      //@ assert i == 0;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Assert) in method m1bad",11
//                );
//    }
//    
//    
//    
////    public void testArrays() {
////        helpTCX("tt.TestJava","package tt; \n"
////                +"public class TestJava { \n"
////                
////                +"  public void m1bad(/*@ nullable*/ int[] a, int i) {\n"
////                +"      a[1] = 9;\n"
////                +"  }\n"
////                
////                +"  //@ requires i < a.length; \n"
////                +"  public void m2bad(int[] a, int i) {\n"
////                +"      a[i] = 9;\n"
////                +"  }\n"
////                
////                +"  //@ requires i >= 0; \n"
////                +"  public void m3bad(int[] a, int i) {\n"
////                +"      a[i] = 9;\n"
////                +"  }\n"
////                
////                +"  //@ requires i >= 0 && i < a.length; \n"
////                +"  public void m1good(int[] a, int i) {\n"
////                +"      a[i] = 9;\n"
////                +"  }\n"
////                
////                +"}"
////                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m1bad",12
////                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bad",12
////                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3bad",12
////                );
////    }
//    
//    // FIXME _ check that different return or throw statements are properly pointed to
//
//    // FIXME - needs proper expansion of array accesses
////    public void testPostcondition1() {
////        helpTCX("tt.TestJava","package tt; \n"
////                +"public class TestJava { \n"
////                
////                +"  //@ ensures a[i]>0;\n"
////                +"  public void m1bad(int[] a, int i) {\n"
////                +"  }\n"
////                
////                +"  //@ requires i >= 0 && i < a.length;\n"
////                +"  //@ ensures a[i]==true || a[i]==false;\n"
////                +"  public void m1good(boolean[] a, int i) {\n"
////                +"  }\n"
////                
////                +"}"
////                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",16
////                );
////    }
//    
//    // FIXME - need tests with multiple ensures and various cases
//    
//    // FIXME - test definedness in postconditions
//    
//    // FIXME - exceptional postconditions
//    
//    // FIXME - need precondition checks for calling methods
//    // FIXME - need checks for ensures assumptions when calling methods
//    // FIXME - complete assignables
//    // FIXME - assignables for method calls
//
//    // Just testing binary and unary 
//    public void testBinaryUnary() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires true;\n"
//                +"  //@ ensures \\result ==4;\n"
//                +"  public int m1bad() {\n"
//                +"    return 1 + 2;\n"
//                +"  }\n"
//                
//                +"  //@ requires true;\n"
//                +"  //@ ensures \\result == 3;\n"
//                +"  public int m1ok() {\n"
//                +"    return 1 + 2;\n"
//                +"  }\n"
//                
//                +"  //@ requires x >= 0;\n"
//                +"  //@ ensures \\result < 0;\n"
//                +"  public int m2bad(int x) {\n"
//                +"    return -x;\n"
//                +"  }\n"
//                
//                +"  //@ requires x >= 0;\n"
//                +"  //@ ensures \\result <= 0;\n"
//                +"  public int m2ok(int x) {\n"
//                +"    return -x;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
//                ,"/tt/TestJava.java:14: warning: Associated declaration",7
//                );
//    }
//
//    public void testIncDec() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { static int i; \n"
//                
//                +"  //@ assignable \\everything;\n"
//                +"  //@ ensures \\result == i;\n"
//                +"  //@ ensures i == \\old(i) + 1;\n"
//                +"  public int m1ok() {\n"
//                +"    return ++i;\n"
//                +"  }\n"
//                
//                +"  //@ assignable \\everything;\n"
//                +"  //@ ensures \\result == i;\n"
//                +"  //@ ensures i == \\old(i) - 1;\n"
//                +"  public int m2ok() {\n"
//                +"    return --i;\n"
//                +"  }\n"
//                
//                +"  //@ assignable \\everything;\n"
//                +"  //@ ensures \\result == \\old(i);\n"
//                +"  //@ ensures i == \\old(i) + 1;\n"
//                +"  public int m3ok() {\n"
//                +"    return i++;\n"
//                +"  }\n"
//                
//                +"  //@ assignable \\everything;\n"
//                +"  //@ ensures \\result == i;\n"
//                +"  //@ ensures i == \\old(i) + 1;\n"
//                +"  public int m3bad() {\n"
//                +"    return i++;\n"
//                +"  }\n"
//                
//                +"  //@ assignable \\everything;\n"
//                +"  //@ ensures \\result == \\old(i);\n"
//                +"  //@ ensures i == \\old(i) - 1;\n"
//                +"  public int m4ok() {\n"
//                +"    return i--;\n"
//                +"  }\n"
//                
//                +"  //@ assignable \\everything;\n"
//                +"  //@ ensures \\result == i;\n"
//                +"  //@ ensures i == \\old(i) - 1;\n"
//                +"  public int m4bad() {\n"
//                +"    return i--;\n"
//                +"  }\n"
//                
//               
//                +"}"
//                ,"/tt/TestJava.java:25: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
//                ,"/tt/TestJava.java:22: warning: Associated declaration",7
//                ,"/tt/TestJava.java:37: warning: The prover cannot establish an assertion (Postcondition) in method m4bad",5
//                ,"/tt/TestJava.java:34: warning: Associated declaration",7
//                );
//    }
//
//    // Just testing binary and unary 
//    public void testJMLBinaryUnary() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires p ==> q;\n"
//                +"  //@ ensures !p || q;\n"
//                +"  public void m1ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                +"  //@ requires p <==> q;\n"
//                +"  //@ ensures p == q;\n"
//                +"  public void m2ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                +"  //@ requires p <=!=> q;\n"
//                +"  //@ ensures p != q;\n"
//                +"  public void m3ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                +"  //@ requires p <== q;\n"
//                +"  //@ ensures p || !q;\n"
//                +"  public void m4ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                +"  //@ requires !p || q;\n"
//                +"  //@ ensures p ==> q;\n"
//                +"  public void m5ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                +"  //@ requires p == q;\n"
//                +"  //@ ensures p <==> q;\n"
//                +"  public void m6ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                +"  //@ requires p != q;\n"
//                +"  //@ ensures p <=!=> q;\n"
//                +"  public void m7ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                +"  //@ requires p || !q;\n"
//                +"  //@ ensures p <== q;\n"
//                +"  public void m8ok(boolean p, boolean q) {\n"
//                +"  }\n"
//                
//                
//                +"}"
//                );
//    }
//
//    public void testConditional() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires true;\n"
//                +"  //@ ensures \\result == i;\n"
//                +"  public int m1bad(boolean b, int i) {\n"
//                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
//                +"  }\n"
//                
//                +"  //@ requires true;\n"
//                +"  //@ ensures \\result >= i;\n"
//                +"  public int m1ok(boolean b, int i) {\n"
//                +"    return (b && (i == 1)) ? i : i + 1 ;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                );
//    }
//
//    public void testShortCircuit() {
//        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
//                +"public class TestJava { int f; \n"
//                
//                +"  public boolean m1bad(boolean b, int i) {\n"
//                +"    return i != 0 || (20/i <= 20) ;\n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m1ok(boolean b, int i) {\n"
//                +"    return i == 0 || (i/i > 0) ;\n"
//                +"  }\n"
//                
//                +"  public boolean m2bad(boolean b, int i) {\n"
//                +"    return i == 0 && (20/i <= 20) ;\n"
//                +"  }\n"
//                
//                +"  public boolean m2ok(boolean b, int i) {\n"
//                +"    return i != 0 && (20/i <= 20) ;\n"
//                +"  }\n"
//                
//                +"  public boolean m3bad(@Nullable TestJava t) {\n"
//                +"    return t != null || t.f == 1 ;\n"
//                +"  }\n"
//                
//                +"  public boolean m3ok(@Nullable TestJava t) {\n"
//                +"    return t != null && t.f == 1 ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a;\n"
//                +"  //@ ensures \\result;\n"
//                +"  //@ also \n"
//                +"  //@ requires !a;\n"
//                +"  //@ ensures \\result == b;\n"
//                +"  public boolean m4ok(boolean a, boolean b) {\n"
//                +"    return a || b ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a;\n"
//                +"  //@ ensures b;\n"
//                +"  //@ also \n"
//                +"  //@ requires !a;\n"
//                +"  //@ ensures \\result == b;\n"
//                +"  public boolean m4bad(boolean a, boolean b) {\n"
//                +"    return a || b ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a;\n"
//                +"  //@ ensures \\result == b;\n"
//                +"  //@ also \n"
//                +"  //@ requires !a;\n"
//                +"  //@ ensures \\result == false;\n"
//                +"  public boolean m5ok(boolean a, boolean b) {\n"
//                +"    return a && b ;\n"
//                +"  }\n"
//                
//                // FIXME - it should be valid, but returns unknown
//                // Keep these - the result is unknown on some solvers and
//                // exposed a bug in handling unknown results
//                +"  //@ requires i < 2 && i > -2; ensures \\result;\n"
//                +"  public boolean m1bugOK(int i) {\n"
//                +"    return i == 0 || (20/i <= 20) ;\n"
//                +"  }\n"
//                
//                // Look at the counterexample on this one (TODO)
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m1bug(int i) {\n"
//                +"    return i == 0 || (20/i <= 20) ;\n"
//                +"  }\n"
//                
//                +"  //@ requires i < 30 && i > -30; ensures \\result;\n"
//                +"  public boolean m1bugOK2(int i) {\n"
//                +"    return i == 0 || (20/i <= 20) ;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",25
//                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",25
//                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m3bad",26
//                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Postcondition) in method m4bad",5
//                ,"/tt/TestJava.java:31: warning: Associated declaration",7
//                ,"/tt/TestJava.java:52: warning: The prover cannot establish an assertion (Postcondition) in method m1bug",5
//                ,"/tt/TestJava.java:50: warning: Associated declaration",7
//                );
//    }
//
//    public void testJmlLabelExpression() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//
//                +"  //@ requires true;\n"
//                +"  //@ ensures b ==> (i==0) ;\n"
//                +"  public int m1ok(boolean b, int i) {\n"
//                +"    //@ ghost boolean bb = (\\lbl LBL_BB b);\n"
//                +"    //@ ghost boolean bbp = (\\lblpos LBL_BB2 (i==0));\n"
//                +"    //@ ghost boolean bbn = (\\lblneg LBL_BB3 (i==0));\n"
//                +"    return 1;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:6: warning: Label LBL_BB has value true",41
//                ,"/tt/TestJava.java:8: warning: Label LBL_BB3 has value false",46
//                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1ok",5
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                );
//    }
//
//    public void testBoolOpsParens() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires true;\n"
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m1bad(boolean p, boolean q) {\n"
//                +"    return p == q;\n"
//                +"  }\n"
//                
//                +"  //@ requires p && q;\n"
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m1ok(boolean p, boolean q) {\n"
//                +"    return ((p == q)) ;\n"
//                +"  }\n"
//                
//                +"  //@ requires true;\n"
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m2bad(boolean p, boolean q) {\n"
//                +"    return p != q;\n"
//                +"  }\n"
//                
//                +"  //@ requires p && !q;\n"
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m2ok(boolean p, boolean q) {\n"
//                +"    return p != q ;\n"
//                +"  }\n"
//                
//                +"  //@ requires true;\n"
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m3bad(boolean p, boolean q) {\n"
//                +"    return p == !q;\n"
//                +"  }\n"
//                
//                +"  //@ requires p && !q;\n"
//                +"  //@ ensures \\result;\n"
//                +"  public boolean m3ok(boolean p, boolean q) {\n"
//                +"    return p == !q ;\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
//                ,"/tt/TestJava.java:14: warning: Associated declaration",7
//                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
//                ,"/tt/TestJava.java:24: warning: Associated declaration",7
//                );
//    }
//
////    public void testBoxing() {
////        helpTCX("tt.TestJava","package tt; \n"
////                +"public class TestJava { \n"
////                
////                +"  public int m1bad(/*@ nullable */ Integer i) {\n"
////                +"    return i;\n"
////                +"  }\n"
////                
////                +"  public void m1ok() {\n"
////                +"    int i = 3;\n"
////                +"    Integer ii = i;\n"
////                +"    int j = ii;\n"
////                +"    //@ assert i == j;\n"
////                +"  }\n"
////                
////                +"}"
////                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
////                ,"/tt/TestJava.java:4: warning: Associated declaration",7
////                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
////                ,"/tt/TestJava.java:14: warning: Associated declaration",7
////                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
////                ,"/tt/TestJava.java:24: warning: Associated declaration",7
////                );
////    }
//
//    // FIXME
////    public void testSelect() {
////        helpTCX("tt.TestJava","package tt; \n"
////                +"public class TestJava { \n"
////                
////                +"  public int f;\n"
////                
////                +"  //@ requires true;\n"
////                +"  //@ ensures \\result == 1;\n"
////                +"  public int m1bad() {\n"
////                +"    return this.f ;\n"
////                +"  }\n"
////                
////                +"  //@ requires this.f == 1;\n"
////                +"  //@ ensures \\result == 1;\n"
////                +"  public int m1ok() {\n"
////                +"    return this.f ;\n"
////                +"  }\n"
////                
////                +"  //@ requires true;\n"
////                +"  //@ ensures \\result == 1;\n"
////                +"  public int m2bad() {\n"
////                +"    return f ;\n"
////                +"  }\n"
////                
////                +"  //@ requires f == 1;\n"
////                +"  //@ ensures \\result == 1;\n"
////                +"  public int m2ok() {\n"
////                +"    return f ;\n"
////                +"  }\n"
////                
////                +"  //@ requires f == 1;\n"
////                +"  //@ ensures \\result == 1;\n"
////                +"  public int m3bad(TestJava p) {\n"
////                +"    return p.f ;\n"
////                +"  }\n"
////                
////                +"  //@ requires true;\n"
////                +"  //@ ensures true;\n"
////                +"  public int m3bad2(/*@nullable*/ TestJava p) {\n"
////                +"    return p.f ;\n"
////                +"  }\n"
////                
////                +"  //@ requires p.f == 1;\n"
////                +"  //@ ensures \\result == 1;\n"
////                +"  public int m3ok(TestJava p) {\n"
////                +"    return p.f ;\n"
////                +"  }\n"
////                
////                +"  public void m4ok(TestJava p) {\n"
////                +"    System.out.println(\"A\");\n"
////                +"  }\n"
////                
////                
////                
////                +"}"
////                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
////                ,"/tt/TestJava.java:5: warning: Associated declaration",7
////                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
////                ,"/tt/TestJava.java:15: warning: Associated declaration",7
////                ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
////                ,"/tt/TestJava.java:25: warning: Associated declaration",7
////                ,"/tt/TestJava.java:32: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m3bad2",13
////                );
////    }
//
//    public void testArrayIndex() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public int f;\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  public int m1bad(int[] a) {\n"
//                +"    return a[10] ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  public int m1bada(int[] a) {\n"
//                +"    return a[-1] ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  public int m1badb(int[] a, int i) {\n"
//                +"    return a[i] ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  public int m1good(int[] a) {\n"
//                +"    return a[0] ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  public int m1gooda(int[] a) {\n"
//                +"    return a[9] ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  //@ requires i >= 3;\n"
//                +"  //@ requires i <= 8;\n"
//                +"  public int m1goodb(int[] a, int i) {\n"
//                +"    return a[i] ;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",13
//                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",13
//                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1badb",-13
//                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",-13
//                );
//    }
//
//    public void testArrayValue() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public int f;\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  //@ ensures \\result == a[1];\n"
//                +"  public int m1bad(int[] a) {\n"
//                +"    return a[0] ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 10;\n"
//                +"  //@ ensures \\result == a[0];\n"
//                +"  public int m1good(int[] a) {\n"
//                +"    return a[0] ;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
//                ,"/tt/TestJava.java:5: warning: Associated declaration",7
//                );
//    }
//
//    public void testAssignOp() {
//        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
//                +"public class TestJava { \n"
//                
//                +"  public int f;\n"
//                
//                +"  //@ ensures \\result == j;\n"
//                +"  public int m1bad(int j) {\n"
//                +"    int i = j ;\n"
//                +"    return (i+=1) ;\n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == j+j+1;\n"
//                +"  public int m1good(int j) {\n"
//                +"    int i = j ;\n"
//                +"    return (i+=j+1) ;\n"
//                +"  }\n"
//                
//                +"  public int m2bad(int j) {\n"
//                +"    int i = j ;\n"
//                +"    return (i/=j) ;\n"
//                +"  }\n"
//                
//                +"  //@ requires j != 0;\n"
//                +"  public int m2good(int j) {\n"
//                +"    int i = j ;\n"
//                +"    return (i/=j) ;\n"
//                +"  }\n"
//                
//                +"  //@ requires t != null;\n"
//                +"  //@ requires i != 0;\n"
//                +"  public void m3bad(TestJava t, int i) {\n"
//                +"    t.f /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ assignable t.f;\n"
//                +"  //@ requires t != null;\n"
//                +"  public void m3badb(TestJava t, int i) {\n"
//                +"    t.f /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0;\n"
//                +"  //@ assignable \\everything;\n"
//                +"  public void m3badc(@Nullable TestJava t, int i) {\n"
//                +"    t.f /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ requires t != null;\n"
//                +"  //@ requires i != 0;\n"
//                +"  //@ assignable \\everything;\n"
//                +"  public void m3good(TestJava t, int i) {\n"
//                +"    t.f /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0;\n"
//                +"  //@ assignable \\everything;\n"
//                +"  public void m4bad(@Nullable int[] a, int i) {\n"
//                +"    a[0] /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 4;\n"
//                +"  //@ requires i != 0;\n"
//                +"  //@ assignable \\everything;\n"
//                +"  public void m4badb(@NonNull int[] a, int i) {\n"
//                +"    a[-1] /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 4;\n"
//                +"  //@ requires i != 0;\n"
//                +"  //@ assignable \\everything;\n"
//                +"  public void m4badc(@NonNull int[] a, int i) {\n"
//                +"    a[4] /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 4;\n"
//                +"  //@ assignable \\everything;\n"
//                +"  public void m4badd(@NonNull int[] a, int i) {\n"
//                +"    a[0] /= i ;\n"
//                +"  }\n"
//                
//                +"  //@ requires a.length == 4;\n"
//                +"  //@ requires i != 0;\n"
//                +"  //@ assignable \\everything;\n"
//                +"  public void m4good(@NonNull int[] a, int i) {\n"
//                +"    a[0] /= i ;\n"
//                +"  }\n"
//                
//                +"  public void m10ok(boolean i) {\n"
//                +"    int x = 10 ;\n"
//                +"    int y = 20 ;\n"
//                +"    x = (y += x + 1) + 2 ;\n"
//                +"    //@ assert x == 33 ;\n"
//                +"    //@ assert y == 31 ;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",14
//                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assignable) in method m3bad",9
//                ,"/tt/TestJava.java:23: warning: Associated declaration",7
//                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3badb",9
//                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m3badc",9
//                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (PossiblyNullReference) in method m4bad",10
//                ,"/tt/TestJava.java:53: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m4badb",11
//                ,"/tt/TestJava.java:59: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4badc",10
//                ,"/tt/TestJava.java:64: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4badd",10
//                );
//    }
//
//    public void testChangedParam() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public int f;\n"
//                
//                +"  //@ ensures \\result == i;\n"
//                +"  public int m1bad(int i) {\n"
//                +"    return (i+=1) ;\n"
//                +"  }\n"
//                
//                +"  //@ ensures \\result == i+1;\n"
//                +"  public int m1good(int i) {\n"
//                +"    return (i+=1) ;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
//                ,"/tt/TestJava.java:4: warning: Associated declaration",7
//                );
//    }
//
//    public void testNameReused() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1good() {\n"
//                +"    { int s = 0; /*@ assert s == 0; */ }\n"
//                +"    { int s = 1; /*@ assert s == 1; */ }\n"
//                +"  }\n"
//                
//                +"  public void m1bad() {\n"
//                +"    { int s = 0; /*@ assert s == 1; */ }\n"
//                +"    { int s = 1; /*@ assert s == 0; */ }\n"
//                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (Assert) in method m1bad",22
//                );
//    }
//
//    public void testNonNullField() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public Object nnf;\n"
//                +"  public /*@ nullable*/ Object f;\n"
//
//                // FIXME - these crash Z3
////                +"  public Object m1bad() {\n"
////                +"    return this.f ;\n"
////                +"  }\n"
////                
////                +"  public Object m1ok() {\n"
////                +"    return this.nnf ;\n"
////                +"  }\n"
//                
//                +"  public void m2bad() {\n"
//                +"    nnf = null ;\n"
//                +"  }\n"
//                
////                +"  public void m2ok() {\n"
////                +"    f = null ;\n"
////                +"  }\n"
//                
//                +"}"
//                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",9
//                );
//    }
//
//    public void testExplicitAssert() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires true;\n"
//                +"  public void m1bad(int i) {\n"
//                +"    //@ assert i == 0 ;\n"
//                +"  }\n"
//                
//                +"  //@ requires i == 0;\n"
//                +"  public void m1ok(int i) {\n"
//                +"    //@ assert i == 0 ;\n"
//                +"  }\n"
//                
//                +"  public void m1okb(int i) {\n"
//                +"    //@ assume i == 0 ;\n"
//                +"    //@ assert i == 0 ;\n"
//                +"  }\n"
//                
//                +"  //@ requires true;\n"
//                +"  public void m2bad(int i) {\n"
//                +"    assert i == 0 ;\n"
//                +"  }\n"
//                
//                +"  //@ requires true;\n"
//                +"  public void m2badb(int i) {\n"
//                +"    assert i == 0 : \"m2badb fails\" ;\n"
//                +"  }\n"
//                
//                +"  //@ requires i == 0;\n"
//                +"  public void m2ok(int i) {\n"
//                +"    assert i == 0 : \"ASD\" ;\n"
//                +"  }\n"
//                
//                +"  public void m2okb(int i) {\n"
//                +"    //@ assume i == 0 ;\n"
//                +"    assert i == 0 ;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
//                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (Assert) in method m2bad",5
//                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (Assert) in method m2badb: m2badb fails",5
//                );
//    }
//    
//    public void testAssignment() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  public void m1bad(boolean i) {\n"
//                +"    int x = 0 ;\n"
//                +"    if (i) x = 1; else x = 2; ;\n"
//                +"    x = x + 1 ;\n"
//                +"    //@ assert x < 3 ;\n"
//                +"  }\n"
//                
//                +"  public void m1ok(boolean i) {\n"
//                +"    int x = 0 ;\n"
//                +"    if (i) x = 1; else x = 2; ;\n"
//                +"    x = x + 1 ;\n"
//                +"    //@ assert x < 4 ;\n"
//                +"  }\n"
//                
//                +"  public void m2ok(boolean i) {\n"
//                +"    int x = 10 ;\n"
//                +"    int y ;\n"
//                +"    x = (y = x + 1) + 2 ;\n"
//                +"    //@ assert x == 13 ;\n"
//                +"    //@ assert y == 11 ;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
//                );    }
//
//    public void testUndefined() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                
//                +"  //@ requires 10/i < 0;\n"
//                +"  public void m1bad(int i) {\n"
//                +"  }\n"
//                
//                +"  //@ requires i != 0 && 10/i < 0;\n"
//                +"  public void m1good(int i) {\n"
//                +"  }\n"
//                
//                +"  //@ ensures 10/i < 0 || true;\n"
//                +"  public void m2bad(int i) {\n"
//                +"  }\n"
//                
//                +"  //@ ensures i == 0 || 10/i < 0 || true;\n"
//                +"  public void m2good(int i) {\n"
//                +"  }\n"
//                
//                +"  public void m3bad(int i) {\n"
//                +"  //@ assume 10/i < 0 || true;\n"
//                +"  }\n"
//                
//                +"  public void m3good(int i) {\n"
//                +"  //@ assume i == 0 || 10/i < 0 || true;\n"
//                +"  }\n"
//                
//                +"  public void m4bad(int i) {\n"
//                +"  //@ assert 10/i < 0 ||true;\n"
//                +"  }\n"
//                
//                +"  public void m4good(int i) {\n"
//                +"  //@ assert i == 0 || 10/i < 0 || true;\n"
//                +"  }\n"
//                
//                +"  public void m5bad(int i) {\n"
//                +"  //@ assert 10%i < 0 ||true;\n"
//                +"  }\n"
//                
//                +"  public void m5good(int i) {\n"
//                +"  //@ assert i == 0 || 10%i < 0 || true;\n"
//                +"  }\n"
//                
//                
//                +"}"
//                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m1bad",18
//                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m2bad",17
//                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m3bad",16
//                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4bad",16
//                ,"/tt/TestJava.java:28: warning: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5bad",16
//                );    }
//
//
//    public void testControl() {
//        helpTCX("tt.TestJava","package tt; \n"
//                +"public class TestJava { \n"
//                +"  int x,xx; static int y,yy; \n"
//                
//                +"  public void m1good() {\n"
//                +"    for (int i=0; i<10; i=i+1) {\n"
//                +"       //@ assert i<10;\n"
//                +"    }\n"
//                +"  }\n"
//                                
//                +"  public void m2good() {\n"
//                +"    int i=0; \n"
//                +"    while (i<10) {\n"
//                +"       //@ assert i<10;\n"
//                +"       i = i + 1;\n"
//                +"    }\n"
//                +"    //@ assert i>=10;\n"
//                +"  }\n"
//                                
//                +"  public void m2bad() {\n"
//                +"    int i=0; \n"
//                +"    while (i<10) {\n"
//                +"       //@ assert i<10;\n"
//                +"       i = i + 1;\n"
//                +"    }\n"
//                +"    //@ assert i>10;\n"
//                +"  }\n"
//
//                // FIXME - fix the assumptions here - first time through loop
////                +"  public void m3good() {\n"
////                +"    int i=0; \n"
////                +"    do {\n"
////                +"       //@ assert i<10;\n"
////                +"       i = i + 1;\n"
////                +"       //@ assert i<=10;\n"
////                +"    } while (i<10); \n"
////                +"    //@ assert i>=10;\n"
////                +"  }\n"
////                                
////                +"  public void m3bad() {\n"
////                +"    int i=0; \n"
////                +"    do {\n"
////                +"       //@ assert i<10;\n"
////                +"       i = i + 1;\n"
////                +"       //@ assert i<=10;\n"
////                +"    } while (i<10); \n"
////                +"    //@ assert i>10;\n"
////                +"  }\n"
//                                
//                +"  //@ requires arg != null; \n"
//                +"  public void m4good(int[] arg) {\n"
//                +"    int i=0; \n"
//                +"    for (int k: arg) {\n"
//                +"       i = i + 1;\n"
//                +"    }  \n"
//                +"    // FIXME //@ assert i == arg.length;\n"
//                +"  }\n"
//                                
//                +"  //@ requires arg != null; \n"
//                +"  public void m4bad(int[] arg) {\n"
//                +"    int i=0; \n"
//                +"    for (int k: arg) {\n"
//                +"       i = i + 1;\n"
//                +"    }  \n"
//                +"    //@ unreachable;\n"
//                +"  }\n"
//                                
//                                
//                +"}"
//                ,"/tt/TestJava.java:23: warning: The prover cannot establish an assertion (Assert) in method m2bad",9
//                ,"/tt/TestJava.java:39: warning: The prover cannot establish an assertion (Unreachable) in method m4bad",9
//                );
//        }


}
