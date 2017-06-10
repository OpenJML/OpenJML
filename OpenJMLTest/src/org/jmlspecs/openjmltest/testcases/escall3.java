package org.jmlspecs.openjmltest.testcases;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;

@RunWith(ParameterizedWithNames.class)
public class escall3 extends EscBase {

    public escall3(String option, String solver) {
        super(option,solver);
    }
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
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
        //main.addOptions("-method=m1bad","-show");
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
                +"  //@ ensures \\result == 10; \n"
                +"  public int m2bad(boolean b) {\n"
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
                
                
                +"}"
                    ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                    ,"/tt/TestJava.java:6: warning: Associated declaration",7
                    ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                    ,"/tt/TestJava.java:13: warning: Associated declaration",7
                    ,"/tt/TestJava.java:27: warning: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                    ,"/tt/TestJava.java:23: warning: Associated declaration",7
                );
    }
    
    @Test 
    public void testFieldAssign2() {
        helpTCX("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  int i; static int j;\n"
                
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures b ==> \\result == 2; \n"
                +"  public int m1good(boolean b) {\n"
                +"    i = 1;\n"
                +"    if (b) i = 2;\n"
                +"    return i;\n"
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
                
                +"  //@ requires this != o && o != null; \n"
                +"  //@ assignable \\everything; \n"
                +"  //@ ensures \\result == 1; \n"
                +"  public int m3good(TestJava o) {\n"
                +"    o.i = 1;\n"
                +"    i = 2;\n"
                +"    return o.i;\n"
                +"  }\n"
                
                
                +"}"
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
    public void testNullThrow1() {
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
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",16
                ,"/tt/TestJava.java:9: warning: The prover cannot establish an assertion (PossiblyNullValue) in method m2bad",16
                );
    }
    
    @Test
    public void testNullThrow2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
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
                );
    }
    
    @Test public void testNullSynchronized1() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(/*@ nullable */ Object o) throws Exception {\n"
                +"       synchronized (o) {};\n"
                +"  }\n"
                
                +"  public void m2bad( Object o) throws Exception {\n"
                +"       synchronized (o) {\n"
                +"          o = null; };\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",21
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",13
                );
    }

    @Test public void testNullSynchronized2() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1good(Object o) throws Exception {\n"
                +"       synchronized (o) {};\n"
                +"  }\n"
                
                +"  public void m2good(Object o) throws Exception {\n"
                +"       synchronized (this) {};\n"
                +"  }\n"
                
                +"}"
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
                );
        }


    @Test public void testAssignOp1() {
        main.addOptions("-escMaxWarnings=1");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires j < 1000 && -1000 < j; ensures \\result == j+j+1;\n"
                +"  public int m1good(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=j+1) ;\n"
                +"  }\n"
                
                +"}"
                );
    }

    @Test public void testAssignOp1Div() {
        Assume.assumeTrue(runLongTests);
        Assume.assumeTrue(!"cvc4".equals(solver)); // SKIPPING because CVC4 does not handle integer division
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
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

                +"  //@ requires t != null;\n"
                +"  //@ requires i != 0;\n"
                +"  //@ assignable \\everything;\n" 
                +"  public void m3good(TestJava t, int i) {\n"
                +"    t.f /= i ;\n"
                +"  }\n"
                

                +"}"
                );
    }

    @Ignore // takes a long time
    @Test public void testAssignOp2() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ ensures \\result == j;\n"
                +"  public int m1bad(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i+=1) ;\n"
                +"  }\n"
                
                +"  public int m2bad(int j) {\n"
                +"    int i = j ;\n"
                +"    return (i/=j) ;\n"
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

                
                
                +"}"
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: warning: Associated declaration",7
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",14
                ,"/tt/TestJava.java:16: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3badb",9
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3badc",6
                );
    }

    @Ignore // takes a long time
    @Test public void testAssignOp3() {
        main.addOptions("-escMaxWarnings=1");
        main.addOptions("-logic=AUFNIRA");
        helpTCX("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                                
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
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-9
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4bad",-6
                ,"/tt/TestJava.java:7: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-6
                ,"/tt/TestJava.java:13: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m4badb",6
                ,"/tt/TestJava.java:19: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4badc",6
                ,"/tt/TestJava.java:24: warning: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4badd",10
                );
    }

  
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
                ,anyorder(
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1bad",8),
                        seq("/tt/TestJava.java:4: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",8)
                        )
                ,"/tt/TestJava.java:8: warning: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2bad",8
                ,"/tt/TestJava.java:12: warning: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3bad",8
                );
    }
    
    @Test public void testArrayType1() { // TODO: CVC4 takes 147 sec
        //main.addOptions("-show","-method=B");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int[] a) {\n"
                +"      //@ assume a != null && a.length > 1;\n"
                +"      a[0] = 9;\n"
                +"  }\n"
                
                +"  public void m2(Integer[] a, Integer i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"
                
                +"  public void m3(Integer[] a, Integer i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      //@ assume \\elemtype(\\typeof(a)) == \\type(Integer);\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"
                
                +"  public void m4bad(Integer[] a, Object i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"
                
                +"  static class A {}\n"
                +"  static class B extends A {}\n"
                
                +"}"
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m4bad",12
                );
    }

    @Test public void testArrayType1Bug() { // TODO: CVC4 takes 147 sec
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int[] a) {\n"
                +"      //@ assume a != null && a.length > 1;\n"
                +"      a[0] = 9;\n"
                +"  }\n"
                
                +"  public void m2bad(String[] a, Integer i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"
                
                +"  public void m3(String[] a, String i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      //@ assume \\elemtype(\\typeof(a)) == \\type(String);\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"
                
                +"  public void m4bad(String[] a, Object i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"
                
                +"  static class A {}\n"
                +"  static class B extends A {}\n"
                
                +"}"
                ,"/tt/TestJava.java:10: warning: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m2bad",12
                ,"/tt/TestJava.java:21: warning: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m4bad",12
                );
    }
    
    @Test public void testArrayType2() { // TODO: CVC4 takes 186 sec
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m3a(Integer[] a, Integer i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"

                +"  public void m5bad(A[] a, B i) {\n" // FAILS because 'a' might have a dynamic type that does not hold a B
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"

                +"  public void m5(A[] a, B i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      //@ assume \\type(B) <: \\elemtype(\\typeof(a));\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"

                +"  static class A {}\n"
                +"  static class B extends A {}\n"
                
                +"}"
                ,"/tt/TestJava.java:11: warning: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m5bad",12
                );
    }
    
    @Test public void testArrayType2Bug() { // TODO: CVC4 takes 186 sec
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m3a(String[] a, String i) {\n"
                +"      //@ assume a != null && a.length > 1 && i != null;\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"

                +"  static class A {}\n"
                +"  static class B extends A {}\n"
                
                +"}"
                );
    }
    
    
    @Test public void testMethodWithConstructorNameFixed() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public byte[] b;\n"
                +"  //@ public invariant b != null && b.length == 20;\n"
                
                +"  public TestJava(int i) {\n"
                +"      b = new byte[20];\n"
                +"  }\n"
                
                
                +"}"
                );
    }
    
    @Test public void testMethodWithConstructorNameOK() {
    	main.addOptions("-verbose","-trace","-ce");
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public byte[] b;\n"
                +"  //@ public invariant b != null && b.length == 20;\n"

                +"  public TestJava(int i) {\n"
                +"      b = new byte[20];\n"
                +"  }\n"

                // The following method - not constructor - note the return type
                // appears to be legal Java
                +"  public void TestJava(int i) {\n"
                +"      b = new byte[20];\n"
                +"  }\n"
                
                
                +"}"
                );
    }
    
    @Test public void testMethodWithConstructorName() {
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public byte[] b;\n"
                +"  //@ public invariant b != null && b.length == 20;\n"

                +"  public TestJava() {\n"
                +"  }\n"

                // The following method - not constructor - note the return type
                // appears to be legal Java
                +"  public void TestJava(int i) {\n"
                +"  }\n"
                
                
                +"}"
                ,"/tt/TestJava.java:5: warning: The prover cannot establish an assertion (InvariantExit) in method TestJava",10
                ,"/tt/TestJava.java:4: warning: Associated declaration",14
                );
    }
    
    @Test public void testMethodWithConstructorNameBug() {
        main.addOptions("-no-internalSpecs");
        // If there are no internal specs, then the implicit super() call of the
        // Object() constructor may throw an exception. Then TestJava() would
        // terminate exceptionally - and the invariant would not be established in
        // that case either. With internal Specs, Object() is pure and has 
        // only normal termination.
        helpTCX("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public byte[] b;\n"
                +"  //@ public invariant b != null && b.length == 20;\n"

                +"  public TestJava() {\n"
                +"  }\n"

                
                +"}"
                ,anyorder(
                        seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (InvariantExit) in method TestJava",10
                           ,"/tt/TestJava.java:4: warning: Associated declaration",14)
                ,seq("/tt/TestJava.java:5: warning: The prover cannot establish an assertion (InvariantExceptionExit) in method TestJava",21
                ,"/tt/TestJava.java:4: warning: Associated declaration",14))
                );
    }
    


}
