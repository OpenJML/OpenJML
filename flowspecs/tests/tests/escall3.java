package tests;

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
        main.addOptions("-checkFeasibility=none");
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
    public void testArrayAccess1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NullableByDefault public class TestJava { \n"
                
                +"  public void m1() {\n"
                +"    int[] a = null;\n"
                +"    a[0] = 0;\n" // ERROR 
                +"  }\n"
                
                +"  public void m2() {\n"
                +"    int[] a = null;\n"
                +"    int i = (a)[0];\n" // ERROR 
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:6: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",6
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2",16
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
                +"  //@ requires a.length > 5; \n" // Line 25
                +"  public void m1good(int[] a, int[] b) {\n"
                +"    a[1] = 5;\n"
                +"    //@ assume a == b ;\n"
                +"    //@ assert b[1] ==5 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1bad",17
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m2bad",6
                ,"/tt/TestJava.java:15: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m3bad",6
                ,"/tt/TestJava.java:22: warning: The prover cannot establish an assertion (Assert) in method m4bad",9
                );
    }

    @Test
    public void testArrayAssign1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NullableByDefault public class TestJava { \n"
                
                +"  int i; static int j[];\n"
                
                +"  //@ requires a.length > 3; \n"
                +"  //@ assignable \\everything; \n"
                +"  public int m0bada(int[] a) {\n"
                +"    a[1] = 1;\n"
                +"    return a[0];\n"
                +"  }\n"
                
                +"  //@ requires a != null; \n"
                +"  //@ assignable \\everything; \n"
                +"  public int m0badb(int[] a) {\n"
                +"    a[1] = 1;\n"
                +"    return a[0];\n"
                +"  }\n"
                
                +"  //@ requires a != null && a.length > 3; \n"
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == \\old(a[0]); \n"
                +"  public int m0badc(int[] a) {\n"
                +"    a[-1] = 1;\n"
                +"    return a[0];\n"
                +"  }\n"
                
                +"  //@ requires a != null && a.length > 3; \n"
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == \\old(a[0]); \n" // Line 26
                +"  public int m1good(int[] a) {\n"
                +"    a[1] = 1;\n"
                +"    return a[0];\n"
                +"  }\n"
                
                +"  //@ requires a != null && a.length > 3 && i >= 0 && i <= 1; \n"
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == \\old(a[0]); \n"
                +"  public int m1bad(int[] a, int i) {\n"
                +"    a[i] = 1;\n"
                +"    return a[0];\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (UndefinedNullDeReference) in method m0bada",17
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m0badb",6
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m0badc",6
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:33: warning: Associated declaration",7
                );
    }
    

    @Test
    public void testFieldAssign() {
        main.addOptions("-checkFeasibility=none");
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
    public void testFieldAssign1() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  int i; static int j;\n"
                
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == 2; \n"
                +"  public int m1bad(boolean b) {\n"
                +"    i = 1;\n"
                +"    if (b) i = 2;\n"
                +"    return i;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures b ==> \\result == 2; \n"
                +"  public int m1good(boolean b) {\n"
                +"    i = 1;\n"
                +"    if (b) i = 2;\n"
                +"    return i;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == 10; \n"
                +"  public int m2bad(boolean b) {\n"
                +"    j = 1;\n"
                +"    if (b) TestJava.j = TestJava.j + this.j + j;\n"
                +"    if (b) tt.TestJava.j = TestJava.j + this.j + j;\n"
                +"    if (b) this.j = j + 1;\n"
                +"    return tt.TestJava.j;\n"
                +"  }\n"
                
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures b ==> \\result == 10; \n"
                +"  public int m2good(boolean b) {\n"
                +"    j = 1;\n"
                +"    if (b) TestJava.j = TestJava.j + this.j + j;\n"
                +"    if (b) tt.TestJava.j = TestJava.j + this.j + j;\n"
                +"    if (b) this.j = j + 1;\n"
                +"    return tt.TestJava.j;\n"
                +"  }\n"
                
                +"  //@ requires o != null; \n"
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == 1; \n"
                +"  public int m3bad(TestJava o) {\n"
                +"    o.i = 1;\n"
                +"    i = 2;\n"
                +"    return o.i;\n"
                +"  }\n"
                
                +"  //@ requires this != o && o != null; \n"
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == 1; \n"
                +"  public int m3good(TestJava o) {\n"
                +"    o.i = 1;\n"
                +"    i = 2;\n"
                +"    return o.i;\n"
                +"  }\n"
                
                
                +"}"
                    ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                    ,"/tt/TestJava.java:6: warning: Associated declaration",7
                    ,"/tt/TestJava.java:26: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                    ,"/tt/TestJava.java:20: warning: Associated declaration",7
                    ,"/tt/TestJava.java:43: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                    ,"/tt/TestJava.java:39: warning: Associated declaration",7
                );
    }
    
    @Test
    public void testLet() {
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


    
    
    
    
    // FIXME _ check that different return or throw statements are properly pointed to


    
    // FIXME - need tests with multiple ensures and various cases
    
    // FIXME - test definedness in postconditions
    
    // FIXME - exceptional postconditions
    
    // FIXME - need precondition checks for calling methods
    // FIXME - need checks for ensures assumptions when calling methods
    // FIXME - complete assignables
    // FIXME - assignables for method calls






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
                
                +"  //@ requires a.length == 10 && i >= 0;\n"
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
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",13
                );
    }


    @Test
    public void testArrayIndex1() {
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
                
                +"  //@ requires i > 1 && a.length == 10;\n"
                +"  public int m1badb(int[] a, int i) {\n"
                +"    return a[i] ;\n"
                +"  }\n"
                
                +"  //@ requires i < 5 && a.length == 10;\n"
                +"  public int m1badc(int[] a, int i) {\n"
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
                ,"/tt/TestJava.java:14: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",13
                ,"/tt/TestJava.java:18: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1badc",13
                );
    }

    @Test
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



    @Test
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
                
                +"  public void m2ok(boolean i) {\n"
                +"    int x = 10 ;\n"
                +"    int y ;\n"
                +"    x = (y = x + 1) + 2 ;\n"
                +"    //@ assert x == 13 ;\n"
                +"    //@ assert y == 11 ;\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Assert) in method m1bad",9
                );    }


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
                +"    int i = j ;\n"  // Line 20
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
                +"  //@ assignable \\everything;\n"  // Line 40
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
                ,"/tt/TestJava.java:36: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3badc",6
                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-9
                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4bad",-6
                ,"/tt/TestJava.java:47: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-6
                ,"/tt/TestJava.java:53: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m4badb",6
                ,"/tt/TestJava.java:59: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4badc",6
                ,"/tt/TestJava.java:64: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4badd",10
                );
    }

  
    @Ignore
    @Test public void testArrays() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(/*@ nullable*/ int[] a, int i) {\n"
                +"      a[1] = 9;\n"
                +"  }\n"
                
                +"  //@ requires i < a.length; \n"
                +"  public void m2bad(int[] a, int i) {\n"
                +"      a[i] = 9;\n"
                +"  }\n"
                
                +"  //@ requires i >= 0; \n"
                +"  public void m3bad(int[] a, int i) {\n"
                +"      a[i] = 9;\n"
                +"  }\n"
                
                +"  //@ requires i >= 0 && i < a.length; \n"
                +"  public void m1good(int[] a, int i) {\n"
                +"      a[i] = 9;\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1bad",12
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bad",12
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3bad",12
                );
    }
    


}
