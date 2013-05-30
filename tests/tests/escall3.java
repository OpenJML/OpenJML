package tests;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.Utils;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class escall3 extends EscBase {

    public escall3(String option, String solver) {
        super(option,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //print = true;
        main.addOptions("-jmltesting");
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
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m2bad",17
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
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1bad",17
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
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1bad",17
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m2bad",6
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m3bad",!option.equals("-custom")?8:6
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
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2bad",6
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
    public void testLet() {
        if (option.equals("-custom")) return;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures (\\let int k = i; \\result == k);\n"
                +"  public int m1(int i) {\n"
                +"     return i;\n"
                +"  }\n"
                
                +"  //@ ensures (\\let int k = 1; \\result == k);\n"
                +"  public int m1bad(int i) {\n"
                +"     return 2;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",6
                ,"/tt/TestJava.java:7: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testLet2() {
        if (option.equals("-custom")) return;
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ ensures (\\let int k = i, int j = k; \\result == j);\n"
                +"  public int m1(int i) {\n"
                +"     return i;\n"
                +"  }\n"
                
                +"  //@ ensures (\\let int k = 1, int j = k; \\result == j);\n"
                +"  public int m1bad(int i) {\n"
                +"     return 2;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",6
                ,"/tt/TestJava.java:7: warning: Associated declaration",7
                );
    }
    
// TODO - are these tests duplicated elsewhere?
    
    @Test
    public void testPrecondition3a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires a.length > 10 && i < 5 && a[i]>0 ;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"  }\n"
                
                +"  //@ requires i >= 0 && i < a.length;\n"
                +"  //@ requires a[i]>0;\n"
                +"  public void m1good(int[] a, int i) {\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:3: warning: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m1bad",43
                );
    }

    @Test
    public void testPostcondition1a() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  //@ signals (Exception) false;\n"
                +"  public void m1bad(int[] a, int i) {\n"
                +"    throw new RuntimeException(); \n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1bad",5
                ,"/tt/TestJava.java:3: warning: Associated declaration",7
                );
    }
    


    
    @Test
    public void testNullThrow() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw null;\n"
                +"  }\n"
                
                +"  public void m2bad(int i, /*@ nullable */ Exception e) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw e;\n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m1good(int i) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw null;\n"
                +"  }\n"
                
                +"  //@ requires i != 0; \n"
                +"  public void m2good(int i, Exception e) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw e;\n"
                +"  }\n"
                
                +"  public void m3good(int i, Exception e) throws Exception {\n"
                +"      if (i == 0) \n"
                +"         throw e;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",16
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullValue) in method m2bad",16
                );
    }
    
    @Test public void testNullSynchronized() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(/*@ nullable */ Object o) throws Exception {\n"
                +"       synchronized (o) {};\n"
                +"  }\n"
                
                +"  public void m2bad( Object o) throws Exception {\n"
                +"       synchronized (o) {\n"
                +"          o = null; };\n"
                +"  }\n"
                
                +"  public void m1good(Object o) throws Exception {\n"
                +"       synchronized (o) {};\n"
                +"  }\n"
                
                +"  public void m2good(Object o) throws Exception {\n"
                +"       synchronized (this) {};\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",21
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",13
                );
    }

    // Almost duplicate of escnew
    @Test public void testMethodInvocation() {
        main.addOptions("-logic=AUFNIRA");
        if ("cvc4".equals(solver)) return; // CVC4 complains about the integer-division operation (FIXME)
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int z(int i)  {\n"
                +"      return i;\n"
                +"  }}\n"
                

                );
    }
    


    
    
    
    
    // FIXME _ check that different return or throw statements are properly pointed to


    
    // FIXME - need tests with multiple ensures and various cases
    
    // FIXME - test definedness in postconditions
    
    // FIXME - exceptional postconditions
    
    // FIXME - need precondition checks for calling methods
    // FIXME - need checks for ensures assumptions when calling methods
    // FIXME - complete assignables
    // FIXME - assignables for method calls





    // FIXME - almost duplciate with escnew
    @Ignore // TODO - ignore until we model division better
    @Test public void testShortCircuit() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { int f; \n"
                
                +"  public boolean m1bad(boolean b, int i) {\n"
                +"    return i != 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result;\n"
                +"  public boolean m1ok(boolean b, int i) {\n"
                +"    return i == 0 || (i/i > 0) ;\n"
                +"  }\n"
                
                +"  public boolean m2bad(boolean b, int i) {\n"
                +"    return i == 0 && (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  public boolean m2ok(boolean b, int i) {\n"
                +"    return i != 0 && (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  public boolean m3bad(@Nullable TestJava t) {\n"
                +"    return t != null || t.f == 1 ;\n"
                +"  }\n"
                
                +"  public boolean m3ok(@Nullable TestJava t) {\n"
                +"    return t != null && t.f == 1 ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures \\result;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  public boolean m4ok(boolean a, boolean b) {\n"
                +"    return a || b ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures b;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  public boolean m4bad(boolean a, boolean b) {\n"
                +"    return a || b ;\n"
                +"  }\n"
                
                +"  //@ requires a;\n"
                +"  //@ ensures \\result == b;\n"
                +"  //@ also \n"
                +"  //@ requires !a;\n"
                +"  //@ ensures \\result == false;\n"
                +"  public boolean m5ok(boolean a, boolean b) {\n"
                +"    return a && b ;\n"
                +"  }\n"
                
                // FIXME - it should be valid, but returns unknown
                // Keep these - the result is unknown on some solvers and
                // exposed a bug in handling unknown results
                +"  //@ requires i < 2 && i > -2; ensures \\result;\n"
                +"  public boolean m1bugOK(int i) {\n"
                +"    return i == 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                // Look at the counterexample on this one (TODO)
                +"  //@ ensures \\result;\n"
                +"  public boolean m1bug(int i) {\n"
                +"    return i == 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                +"  //@ requires i < 30 && i > -30; ensures \\result;\n"
                +"  public boolean m1bugOK2(int i) {\n"
                +"    return i == 0 || (20/i <= 20) ;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m1bad",25
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",25
                ,"/tt/TestJava.java:17: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3bad",26
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Postcondition) in method m4bad",5
                ,"/tt/TestJava.java:31: warning: Associated declaration",7
//                ,"/tt/TestJava.java:52: warning: The prover cannot establish an assertion (Postcondition) in method m1bug",5
//                ,"/tt/TestJava.java:50: warning: Associated declaration",7
                );
    }



    // FIXME - almost duplicat ewith escnew
    @Test public void testArrayIndex() {
        main.addOptions("-escMaxWarnings=1");
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
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",15
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1badb",-14
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",-13
                );
    }

    // FIXME - check for duplicates with escnew after this point



    @Test public void testAssignOp() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-logic=AUFNIRA");
        if ("cvc4".equals(solver)) return; // SKIPPING because CVC4 does not handle integer division
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ ensures \\result == j;\n"
                +"  public int m1bad(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  //@ ensures \\result == j+j+1;\n"
                +"  public int m1good(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=j+1) ;\n"
                +"  }\n"
                
                +"  public int m2bad(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i/=j) ;\n"
                +"  }\n"
                
                +"  //@ requires j != 0;\n"
                +"  public int m2good(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i/=j) ;\n"
                +"  }\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ requires i != 0;\n"
                +"  public void m3(TestJava t, int i) {\n"
                +"    t.f /= i ;\n"
                +"  }\n"
                
                +"  //@ assignable t.f;\n"
                +"  //@ requires t != null;\n"
                +"  public void m3badb(TestJava t, int i) {\n"
                +"    t.f /= i ;\n"
                +"  }\n"
                
                +"  //@ requires i != 0;\n"
                +"  //@ assignable \\everything;\n"
                +"  public void m3badc(@Nullable TestJava t, int i) {\n"
                +"    t.f /= i ;\n"
                +"  }\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ requires i != 0;\n"
                +"  //@ assignable \\everything;\n"
                +"  public void m3good(TestJava t, int i) {\n"
                +"    t.f /= i ;\n"
                +"  }\n"
                
                +"  //@ requires i != 0;\n"
                +"  //@ assignable \\everything;\n"
                +"  public void m4bad(@Nullable int[] a, int i) {\n"
                +"    a[0] /= i ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 4;\n"
                +"  //@ requires i != 0;\n"
                +"  //@ assignable \\everything;\n"
                +"  public void m4badb(@NonNull int[] a, int i) {\n"
                +"    a[-1] /= i ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 4;\n"
                +"  //@ requires i != 0;\n"
                +"  //@ assignable \\everything;\n"
                +"  public void m4badc(@NonNull int[] a, int i) {\n"
                +"    a[4] /= i ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 4;\n"
                +"  //@ assignable \\everything;\n"
                +"  public void m4badd(@NonNull int[] a, int i) {\n"
                +"    a[0] /= i ;\n"
                +"  }\n"
                
                +"  //@ requires a.length == 4;\n"
                +"  //@ requires i != 0;\n"
                +"  //@ assignable \\everything;\n"
                +"  public void m4good(@NonNull int[] a, int i) {\n"
                +"    a[0] /= i ;\n"
                +"  }\n"
                
                +"  public void m10ok(boolean i) {\n"
                +"    int x = 10 ;\n"
                +"    int y = 20 ;\n"
                +"    x = (y += x + 1) + 2 ;\n"
                +"    //@ assert x == 33 ;\n"
                +"    //@ assert y == 31 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",14
//                ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Assignable) in method m3",9
//                ,"/tt/TestJava.java:23: warning: Associated declaration",7
                ,"/tt/TestJava.java:31: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3badb",9
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3badc",9
                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-10
                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4bad",-10
                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-10
                ,"/tt/TestJava.java:53: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m4badb",11
                ,"/tt/TestJava.java:59: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4badc",10
                ,"/tt/TestJava.java:64: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4badd",10
                );
    }



}
