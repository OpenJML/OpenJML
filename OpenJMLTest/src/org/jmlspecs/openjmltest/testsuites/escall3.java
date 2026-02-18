package org.jmlspecs.openjmltest.testsuites;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escall3 extends EscBase {
    
    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        //print = true;
    }
    
    @Test
    public void testNoProver() {
        expectedExit=1;
        addOptions("--prover=Z");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { }\n"
                ,"/tt/TestJava.java: warning: Implicit executable does not exist $ROOT/OpenJML/OpenJMLsrc/../../Solvers/Solvers-macos/Z.X",-1
                ,"/tt/TestJava.java: error: The executable for prover Z is not specified - use -exec or define an openjml.prover.... property",-1
                );
    }
    
    @Test
    public void testNoExec() {
        expectedExit=1;
        addOptions("--exec= ");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { }\n"
                ,"/tt/TestJava.java: error: The executable for prover z3_4_3 is not specified - use -exec or define an openjml.prover.... property",-1
                );
    }
    
    @Test
    public void testTimeoutBad() {
        expectedExit=0;
        addOptions("--timeout=ZZ");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { }\n"
                ,"/tt/TestJava.java: warning: Timeout value cannot be parsed as a double: ZZ",-1
                );
    }
    
    @Test
    public void testTimeoutOK() {
        expectedExit=0;
        addOptions("--timeout", "");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { }\n"
                );
    }
    
    @Test
    public void testDebugOK() { // Test is noisy because debug feasibility turns on progress // FIXME - capture/redirect the output to stdout
        expectedExit=0;
        addOptions("--check-feasibility", "debug:");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { }\n"
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                );
    }
    
    @Test
    public void testDebugBad() { // Test is noisy because debug feasibility turns on progress // FIXME - capture/redirect the output to stdout
        expectedExit=0;
        addOptions("--check-feasibility", "debug:zzz");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { }\n"
                ,"/tt/TestJava.java: warning: debug feasibility starting number has bad format: zzz", -1
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                );
    }
    
    @Test
    public void testSMTout() {
        expectedExit=0;
        addOptions("--smt=smt/testSMToutZ.smt");
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { }\n"
                );
        new java.io.File("smt/testSMToutZ.smt").delete();
    }
    
    @Test
    public void testSimple() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2bad",9
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:12: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testFieldAccess() {
        addOptions("--check-feasibility=none"); // Part of test
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m2bad",17
                );
    }
    
    @Test
    public void testArrayAccess() {
        helpEsc("tt.TestJava","package tt; \n"
                +"import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires a.length > 5; \n"
                +"  public void m1bad(int @Nullable [] a) {\n"
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
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1bad",17
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m2bad",17
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m3bad",17
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Assert) in method m4bad",9
                );
    }
    
    @Test
    public void testArrayAccess1() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",6
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2",16
                );
    }
   
    @Test
    public void testArrayLength() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public void m1(int[] c) {\n"
                +"    //@ assert c != null;\n"
                +"    //@ assert c.length >= 0; \n"
                +"  }\n"
                
                +"}"
                );
    }
   
    @Test
    public void testArrayAssign() {
        helpEsc("tt.TestJava","package tt; \n"
                +"import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  //@ requires a.length > 5; \n"
                +"  public void m1bad(int @Nullable [] a) {\n"
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
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1bad",17
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m2bad",6
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m3bad",6
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Assert) in method m4bad",9
                );
    }

    @Test
    public void testArrayAssign1() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m0bada",17
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m0badb",6
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m0badc",6
                ,"/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:33: verify: Associated declaration",7
                );
    }
    

    @Test
    public void testFieldAssign() {
        addOptions("--check-feasibility=none"); // Part of test
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2bad",6
                );
    }
    
    @Test 
    public void testFieldAssign1() {
        helpEsc("tt.TestJava","package tt; \n"
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
                    ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                    ,"/tt/TestJava.java:6: verify: Associated declaration",7
                    ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Postcondition) in method m2bad",5
                    ,"/tt/TestJava.java:13: verify: Associated declaration",7
                    ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                    ,"/tt/TestJava.java:23: verify: Associated declaration",7
                );
    }
    
    @Test 
    public void testFieldAssign2() {
        helpEsc("tt.TestJava","package tt; \n"
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
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",6
                ,"/tt/TestJava.java:7: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testAssertionError() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1(int i) {\n"
                +"     if (i < 0) assert false;\n"
                +"  }\n"
                
                +"  //@ requires i >= 0;\n"
                +"  public void m1ok(int i) {\n"
                +"     if (i < 0) assert false;\n"
                +"  }\n"
                
                +"  public void m2(int i) {\n"
                +"     if (i < 0) throw new AssertionError();\n"
                +"  }\n"
                
                +"  //@ requires i >= 0;\n"
                +"  public void m2ok(int i) {\n"
                +"     if (i < 0) throw new AssertionError();\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m1",17
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m2",17
                );
    }
    
    @Test
    public void testLet2() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",6
                ,"/tt/TestJava.java:7: verify: Associated declaration",7
                );
    }
    
// TODO - are these tests duplicated elsewhere?
    
    
    @Test
    public void testNullThrow1() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",16
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m2bad",16
                );
    }
    
    @Test
    public void testNullThrow2() {
        helpEsc("tt.TestJava","package tt; \n"
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
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad(/*@ nullable */ Object o) throws Exception {\n"
                +"       synchronized (o) {};\n"
                +"  }\n"
                
                +"  public void m2bad( Object o) throws Exception {\n"
                +"       synchronized (o) {\n"
                +"          o = null; };\n"
                +"  }\n"
                
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",21
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",13
                );
    }

    @Test public void testNullSynchronized2() {
        helpEsc("tt.TestJava","package tt; \n"
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
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",13
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",13
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",13
                );
    }


    @Test
    public void testArrayIndex1() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",13
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",13
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",13
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1badc",13
                );
    }

    @Test
    public void testArrayValue() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: verify: Associated declaration",7
                );
    }



    @Test
    public void testHavocB() {
    	addOptions("--method=m1");
        helpEsc("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                +"  /*@ non_null */ public TestJava ooo;\n"
                +"  /*@ non_null */ public static TestJava sooo;\n"
                
                +"  public void m1(boolean b, /*@ non_null */ TestJava o) {\n"
                +"    ooo = o; sooo = o;\n"
                +"    if (b) meverything();\n"
                +"    //@ assert ooo != null;\n"
                +"    //@ assert ooo instanceof TestJava;\n"
                +"  }\n"
                
                +"  public void meverything() {\n"
                +"  }\n"
                                
                +"}"
                );
        }

    @Test
    public void testHavoc() {
        helpEsc("A",
            """
            public class A {
              int i;
              //@ writes \\nothing;
              public void m(int k) {
                int j;
                //@ havoc i,j,k;
              }
            }
            """
                ,"/A.java:6: verify: The prover cannot establish an assertion (Assignable) in method m: i", 15
                ,"/A.java:3: verify: Associated declaration", 7
        );
    }

    @Test
    public void testHavocA() {
    	addOptions("--exclude=TestJava");
        helpEsc("tt.TestJava","package tt; \n"
                +"/*@ nullable_by_default*/ public class TestJava { \n"
                +"  /*@ non_null */ public TestJava ooo;\n"
                +"  /*@ non_null */ public static TestJava sooo;\n"
                
                +"  public void m1(boolean b, /*@ non_null */ TestJava o) {\n"
                +"    ooo = o; sooo = o;\n"
                +"    if (b) meverything();\n"
                +"    //@ assert ooo != null;\n"
                +"    //@ assert ooo instanceof TestJava;\n"
                +"  }\n"
                
                +"  //@ assignable ooo;\n"
                +"  public void meverything() {\n"
                +"  }\n"
                                
                +"}"
                );
        }

    @Test
    public void testAssignment() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                );
        }


    @Test public void testAssignOp1() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
                +"public class TestJava { \n"
                
                +"  public int f;\n"
                
                +"  //@ requires j != 0;\n"
                +"  public int m2good(int j) {\n"
                +"    int i = j ;\n"  // Line 20
                +"    return (i/=j) ;\n"
                +"  }\n"
                
                +"  //@ requires t != null;\n"
                +"  //@ requires i != 0 && i != -1;\n"
                +"  public void m3(TestJava t, int i) {\n"
                +"    t.f /= i ;\n"
                +"  }\n"

                +"  //@ requires t != null;\n"
                +"  //@ requires i != 0 && i != -1;\n"
                +"  //@ assignable \\everything;\n" 
                +"  public void m3good(TestJava t, int i) {\n"
                +"    t.f /= i ;\n"
                +"  }\n"
                

                +"}"
                );
    }

    @Ignore // takes a long time
    @Test public void testAssignOp2() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m2bad",14
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m3badb",9
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3badc",6
                );
    }

    @Ignore // takes a long time
    @Test public void testAssignOp3() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava","package tt; import org.jmlspecs.annotation.*; \n"
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
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-9
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4bad",-6
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-6
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m4badb",6
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4badc",6
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4badd",10
                );
    }

  
    @Test public void testArrays() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public void m1bad( int /*@ nullable*/[] a, int i) {\n"
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
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1bad",8),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",8)
                        )
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2bad",8
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3bad",8
                );
    }
    
    @Test public void testArrayType1() { // TODO: CVC4 takes 147 sec
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m4bad",12
                );
    }

    @Test public void testArrayType1Bug() {
        helpEsc("tt.TestJava","package tt; \n"
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
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m2bad",12
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m4bad",12
                );
    }
    
    @Test public void testArrayType2() {
        helpEsc("tt.TestJava","package tt; \n"
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
                +"      //@ assume \\type(B) <:= \\elemtype(\\typeof(a));\n"
                +"      Object[] o = a;\n"
                +"      o[0] = i;\n"
                +"  }\n"

                +"  static class A {}\n"
                +"  static class B extends A {}\n"
                
                +"}"
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m5bad",12
                );
    }
    
    @Test public void testArrayType2Bug() { // TODO: CVC4 takes 186 sec
        helpEsc("tt.TestJava","package tt; \n"
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
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public byte[] b;\n"
                +"  //@ public invariant b != null && b.length == 20;\n"
                
                +"  public TestJava(int i) {\n"
                +"      b = new byte[20];\n"
                +"  }\n"
                
                
                +"}"
                );
    }
    
    @Test public void testMultiException() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void m() {}\n"
                +"  public void mm() {\n"
                +"  try {\n"
                +"    m();\n"
                +"  } catch (NullPointerException|ArithmeticException e) {\n"
                +"     //@ assert e instanceof NullPointerException || e instanceof ArithmeticException;\n"
                +"  }}\n"
                
                
                +"}\n"
                );
    }
    
    @Test public void testExceptionTypeC() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void mm(int i) throws ClassNotFoundException, NoSuchMethodException {\n"
                +"  try {\n"
                +"    if (i == 0) throw new ClassNotFoundException();\n"
                +"    if (i == 1) throw new NoSuchMethodException();\n"
                +"  } catch (Exception e) {\n"
                +"     throw e;\n"
                +"  }}\n"
                
                
                +"}\n"
                );
    }
    
    @Test public void testExceptionType() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
        		+"  //@ signals_only NullPointerException, ArithmeticException;\n"
                +"  public void mm(int i) throws NullPointerException, ArithmeticException {\n"
                +"  try {\n"
                +"    if (i == 0) throw new NullPointerException();\n"
                +"    if (i == 1) throw new ArithmeticException();\n"
                +"  } catch (Exception e) {\n"
                +"     throw e;\n"
                +"  }}\n"
                
                
                +"}\n"
                );
    }
    
    @Test public void testExceptionTypeB() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
        		+"  //@ signals_only NullPointerException;\n"
                +"  public void mm(int i) throws NullPointerException {\n"
                +"  try {\n"
                +"    if (i == 0) throw new NullPointerException();\n"
                +"    if (i == 1) throw new ArithmeticException();\n"
                +"  } catch (Exception e) {\n"
                +"     throw e;\n"
                +"  }}\n"
                
                
                +"}\n"
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (ExceptionList) in method mm",6
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }
    
    @Test public void testExceptionType2() {
    	expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  public void mm(int i) throws ClassNotFoundException {\n"
                +"  try {\n"
                +"    if (i == 0) throw new ClassNotFoundException();\n"
                +"    if (i == 1) throw new NoSuchMethodException();\n"
                +"  } catch (Exception e) {\n"
                +"     throw e;\n"
                +"  }}\n"
                
                
                +"}\n"
                ,"/tt/TestJava.java:8: error: unreported exception java.lang.NoSuchMethodException; must be caught or declared to be thrown", 6
                ,optional("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (ExceptionList) in method mm",6)
                );
        // FIXME - in the above, the second error message appears to be non-deterministic
    }
    
    @Test public void testMethodWithConstructorNameOK() {
        helpEsc("tt.TestJava","package tt; \n"
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public byte /*@ nullable */ [] b;
                  //@ public invariant b != null && b.length == 20;
                
                  public TestJava() {
                  }
                
                  // The following method - not constructor - note the return type
                  // appears to be legal Java
                  public void TestJava(int i) {
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (InvariantExit) in method TestJava",10
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                );
    }
    
    // Checks boxing conversion on assignment to a field
    @Test public void testBoxingOnAssignment() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public int b;\n"
                +"  public Integer bb;\n"

                +"  public TestJava(Integer b, int bb) {\n"
                +"    this.b = b;\n"
                +"    this.bb = bb;\n"
                +"  }\n"
                +"}"
                );
    }
    
    // A problem from MHuisman, with String initialization and invariants
    @Test public void testStringInitialization() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                
                +"  public String x = new String();\n"

                +"  public TestJava(String xx) {\n"
                +"    this.x = xx;\n"
                +"  }\n"
                +"}"
                );
    }
    
    // If RR() throws an exception, mmm exits exceptionally
    @Test public void testTryResources() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"
                +"}"
                );
    }
    
    // If RR() throws an exception, mmm exits exceptionally
    // If close throws an exception, then mmm exits exceptionally and flag is not tested
    @Test public void testTryResources1() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"
                +"}"
                );
    }
    
    // If RR() throws an exception, flag == 0
    // If close exits normally, flag == 1
    // If close throws an exception, flag == 10
    @Test public void testTryResources1x() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ pure */ public RR(){}\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 10;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    } catch (Exception eee) { \n"
                +"    //@ assert (\\lbl FLAG TestJava.flag) == 0 || TestJava.flag == 1|| TestJava.flag == 10;\n"
                +"    }\n"
                +"  }\n"
                +"}"
                );
    }
    
    // If RR() throws an exception, mmm exits exceptionally
    @Test public void testTryResources1a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR r = new RR()){\n"
                +"       flag = 2; \n"
                +"       //@ assert TestJava.flag == 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 1;\n"
                +"  }\n"
                +"}"
                );
    }
    
    // Checks that close calls execute in reverse order
    @Test public void testTryResources2() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;}\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }
    
    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2b() {
        addOptions("-checkFeasibility=assert","-defaults=constructor:pure"); // Part of test
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
                +"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
                +"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
                +"    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() throws EE { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() throws EE { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm(boolean b) {\n"  // Line 26
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"      if (b || !b) try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new EE3();\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 1;\n" // not feasible line 34
                +"    } catch (EE e) {\n"
                +"      //@ assert TestJava.flag == 1;\n" 
                +"       //@ assert e instanceof EE3 ;\n" // Line 37
                +"    }\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm(boolean)",11
                );
    }
    
    // Checks the class of the resulting exception when try body and close calls throw exceptions
    @Test public void testTryResources2c() {
        addOptions("-checkFeasibility=assert","-defaults=constructor:pure"); // Part of test
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
        		+"    public static class EE extends RuntimeException {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
        		+"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
        		+"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
        		+"    public static class EE3 extends EE {/*@ public normal_behavior ensures true; */public EE3() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm(boolean b) {\n"  // Line 26
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"      if (b || !b) try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new EE3();\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 2;\n" // not feasible
                +"    } catch (EE1 | EE2 | EE3 e) {\n"
                +"       //@ assert e instanceof EE3 ;\n" // Line 36
                +"    }\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm(boolean)",11
                );
    }
    
    // Checks the class of the resulting exception when close calls throw exceptions, but not the try body
    @Test public void testTryResources2a() {
        addOptions("--check-feasibility=assert","--defaults=constructor:pure");  // Part of test
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    public static class EE extends Exception {  /*@ public normal_behavior ensures true; */public EE() {}}\n"
                +"    public static class EE1 extends EE {/*@ public normal_behavior ensures true; */public EE1() {}}\n"
                +"    public static class EE2 extends EE {/*@ public normal_behavior ensures true; */public EE2() {}}\n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ \n"
                +"       /*@ public normal_behavior ensures true; */ public RR() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag,this.autocloseableContent;\n"
                +"       //@ signals_only EE1;\n"
                +"       //@ signals (Exception e) TestJava.flag == 1;\n"
                +"       public void close() throws EE1 { TestJava.flag = 1; throw new EE1(); }\n"
                +"    }\n"
                +"    public static class RR2 implements AutoCloseable {\n"
                +"       //@ \n"
                +"       /*@ public normal_behavior ensures true; */ public RR2() { }\n"
                +"       //@ also public exceptional_behavior\n"
                +"       //@ assignable TestJava.flag,this.autocloseableContent;\n"
                +"       //@ signals_only EE2;\n"
                +"       //@ signals (Exception e) TestJava.flag == 2;\n"
                +"       public void close() throws EE2 { TestJava.flag = 2; throw new EE2(); }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n" // Line 25
                +"  //@ assignable flag;\n"
                +"  public void mmm() throws EE {\n"  // Line 27
                +"    //@ assert TestJava.flag == 0;  \n"
                +"    try {\n"
                +"      try (RR2 r = new RR2(); RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"      }\n"
                +"      //@ assert TestJava.flag == 2;\n"  // Line 34 -- Not feasible
                +"    } catch (EE e) {\n"
                +"       //@ assert TestJava.flag == 2;\n" // Should be OK
                +"       //@ assert e instanceof EE1;\n"  // Should be OK
                +"    }\n"
                +"  }\n"
                +"}"
                ,"/tt/TestJava.java:34: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.mmm()",11
                );
    }
    
    // Check that finally block of try encloses declarations and calls to close
    @Test public void testTryResources3() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } finally {\n"
                +"      flag = 2;"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }
    
    // If RR() throws an exception, then catch block will execute
    @Test public void testTryResources4() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    boolean normal = true;\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;"
                +"      normal = false;"
                +"    }\n"
                +"    //@ assert normal ==> flag == 1;\n"
                +"    //@ assert !normal ==> flag == 2;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Test public void testTryResources4a() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"  // FIXME - should not be able to skip the catch block
                +"  }\n"
                +"}"
                );
    }
    
    @Test public void testTryResources4b() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2;\n"  // FIXME - should not be able to skip the catch block
                +"  }\n"
                +"}"
                );
    }
    
    // No resource - executes the catch block
    @Test public void testTryResources4c() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also public normal_behavior\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try {\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"       throw new Exception();\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;\n"
                +"    }\n"
                +"    //@ assert TestJava.flag == 2; \n"
                +"  }\n"
                +"}"
                );
    }
    
    // Checks that the outer finally block is last to execute
    @Test public void testTryResources5() {
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"    static public int flag = 0;\n"
                +"    public static class RR implements AutoCloseable {\n"
                +"       //@ also\n"
                +"       //@ assignable TestJava.flag, this.autocloseableContent;\n"
                +"       //@ ensures TestJava.flag == 1;\n"
                +"       public void close() { TestJava.flag = 1;  }\n"
                +"    }\n"
                
                +"  //@ requires flag == 0;\n"
                +"  //@ assignable flag;\n"
                +"  public void mmm() {\n"
                +"    //@ assert TestJava.flag == 0;\n"
                +"    try (RR rr = new RR()){\n"
                +"       flag = 3; \n"
                +"       //@ assert TestJava.flag == 3;\n"
                +"    } catch (Exception e) {\n"
                +"      flag = 2;"
                +"    } finally {\n"
                +"      flag = 5;"
                +"    }\n"
                +"    //@ assert TestJava.flag == 5;\n"
                +"  }\n"
                +"}"
                );
    }
    
    @Ignore // constant folding not implemented
    @Test public void divByZero() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public void m(int i, long l) {
                        var a = i/0;
                        var b = l/0;
                        var c = i % 0;
                        var d = l % 0;
                    }
                }
                """
                );
    }
    
    @Ignore // constant folding not implemented
    @Test public void divByZeroQ() {
        addOptions("--no-warn=literal-div-by-zero");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    public void m(int i, long l) {
                        var a = i/0;
                        var b = l/0;
                        var c = i % 0;
                        var d = l % 0;
                    }
                }
                """
                );
    }
    
    // FIXME - test all these try tests in a constructor
    
    @Test
    public void testIsArray() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    int i = 0;
                    Object oo = new Object();
                    int[] x = new int[1];
                    Object o = new Object[2];
                    Object[] oa = new Object[2];
                
                    //@ assert  \\isarray(\\typeof(x));
                    //@ assert  \\isarray(\\type(int[]));
                    //@ assert  \\isarray(\\typeof(o));
                    //@ assert  \\isarray(\\type(Object[]));
                    //@ assert !\\isarray(\\typeof(i));
                    //@ assert !\\isarray(\\type(int));
                    //@ assert !\\isarray(\\typeof(oo));
                    //@ assert !\\isarray(\\type(Object));
                
                    //@ assert \\isarray(x.getClass());
                    //@ assert \\isarray(int[].class);
                    //@ assert \\isarray(o.getClass());
                    //@ assert \\isarray(Object[].class);
                    //  assert !\\isarray(i.getClass()); // Invalid syntax
                    //@ assert !\\isarray(int.class);
                    //@ assert !\\isarray(oo.getClass());
                    //@ assert !\\isarray(Object.class);
                    //@ assert  \\isarray(oa.getClass());
                  }
                }
                """
                 );
        
    }

    @Test
    public void testIsArrayN() {
        helpEsc("tt.TestJava",
                """
                package tt;
                //@ nullable_by_default
                public class TestJava {
                  public static void main(String[] args) {
                    Class<?> n = null;
                    //@ assert \\isarray(n);
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (NullArgument) in method main", 25
                );
    }

    @Test
    public void testIsArrayIllegal() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                //@ nullable_by_default
                public class TestJava {
                  public static void main(String[] args) {
                    //@ ghost \\bigint z;
                    int i;
                    //@ assert \\isarray(z);
                    //@ assert !\\isarray(i.getClass()); // Invalid syntax
                  }
                }
                """
                ,"/tt/TestJava.java:7: error: The argument of \\isarray must have type \\TYPE or java.lang.Class, not \\bigint", 25
                ,"/tt/TestJava.java:8: error: int cannot be dereferenced", 27
                );
    }

    @Test
    public void testElemType() {
        helpEsc("tt.TestJava",
                """
                package tt;
                //@ nullable_by_default
                public class TestJava {
                  public static void main(String[] args) {
                    Object o = new Object();
                    Object oo = new Object[2];
                    Object[] oa = new Object[2];
                    Object[] ob = new Integer[2];
                    // \\TYPE argument
                    //@ assert \\elemtype(\\typeof(oo)) == \\type(Object);
                    //@ assert \\elemtype(\\typeof(oa)) == \\typeof(o);
                    //@ assert \\elemtype(\\type(Integer[])) == \\type(Integer);
                    //@ assert \\elemtype(\\type(int[])) == \\type(int);
                    // Object argument
                    //@ assert \\elemtype(oa) == \\type(Object);
                    //@ assert \\elemtype(oo) == \\typeof(o);
                    //@ assert \\elemtype(ob) == \\type(Integer);
                  }
                }
                """
                );
    }

    @Test
    public void testElemTypeN() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void m1(String[] args) {
                    // Not allowed: non-array reference types
                    Integer i = 0;
                    //@ show \\elemtype(i);
                  }
                  public static void m2(String[] args) {
                    // Not allowed: non-array reference types
                    //@ show \\elemtype(\\type(Integer));
                  }
                  public static void m3(String[] args) {
                    // not allowed: non-array primitive types
                    int ii = 0;
                    //@ show \\elemtype(\\typeof(ii));
                  }
                  public static void m4(String[] args) {
                    // not allowed: non-array primitive types
                    //@ show \\elemtype(\\type(int));
                  }
                  public static void m5(String[] args) {
                    // not allowed: null values
                    /*@ nullable */ Class<?> n = null;
                    //@ show \\elemtype(n);
                  }
                  public static void m6(String[] args) {
                    // not allowed: null values
                    //@ show \\elemtype(null);
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (IllegalArgument) in method m1", 23
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (IllegalArgument) in method m2", 23
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (IllegalArgument) in method m3", 23
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (IllegalArgument) in method m4", 23
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (NullArgument) in method m5", 24
                ,"/tt/TestJava.java:28: verify: The prover cannot establish an assertion (NullArgument) in method m6", 24
                );
    }

    @Test // Tests for type-checking errors in using \elemtype
    public void testElemTypeIllegal() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                //@ nullable_by_default
                public class TestJava {
                  public static void main(String[] args) {
                    int i; Object o = new Object();
                    //@ check \\elemtype(i) == \\typeof(o); // Java primitive values are not allowed as arguments
                    //@ ghost \\bigint z; // JML type values are not allowed as arguments
                    //@ check \\elemtype(z) == \\typeof(o);
                    //@ ghost \\seq<Integer> s; // JML type values are not allowed as arguments
                    //@ check \\elemtype(s) == \\typeof(o);
                  }
                }
                """
                ,"/tt/TestJava.java:6: error: The argument of \\elemtype must have type \\TYPE or be a Java reference object, not int", 25
                ,"/tt/TestJava.java:8: error: The argument of \\elemtype must have type \\TYPE or be a Java reference object, not \\bigint", 25
                ,"/tt/TestJava.java:10: error: The argument of \\elemtype must have type \\TYPE or be a Java reference object, not \\seq<java.lang.@org.jmlspecs.annotation.Nullable Integer>", 25
                );
    }

    @Test // Tests information about formals
    public void testIsArrayFormal() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void m1(Object[] a) {
                    //@ assert \\isarray(\\typeof(a));
                  }
                  public static void m21(int[] a) {
                    //@ assert \\isarray(\\typeof(a));
                  }
                  public static void m3(int a) {
                    //@ assert !\\isarray(\\typeof(a));
                  }
                  public static void m4(Integer a) {
                    //@ assert !\\isarray(\\typeof(a));
                  }
                  public static void m5(Object a) {
                    //@ assert \\isarray(\\typeof(a));
                  }
                }
                """
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Assert) in method m5", 9
                );
    }
    
    @Test // cf. gitbug877 -- was a bug in RAC, but included an ESC test here for good measure - here instead of escfiles because of indeterminate output order
    public void testSwitch877() {
        helpEsc("tt.ZZ",
        """
        public class ZZ {
            public static void main(String... args) {
              //@ ghost \\bigint z = \\bigint.one*10;
              for (int i = 0; i<5; i++) {
                  switch (i) {
                      case 0 -> { /*@ show (byte)(z+Byte.MAX_VALUE); */}
                      case 1 -> { /*@ show (short)(z+Short.MAX_VALUE); */}
                      case 2 -> { /*@ show (char)(z+Character.MAX_VALUE); */}
                      case 3 -> { /*@ show (int)(z+Integer.MAX_VALUE); */}
                      default -> { /*@ show (long)(z+Long.MAX_VALUE); */}
                   }
              }
            }
        }
        """
        ,anyorder(
             seq("/tt/ZZ.java:6: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method main",36)
             ,seq("/tt/ZZ.java:7: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method main",36)
             ,seq("/tt/ZZ.java:8: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method main",36)
             ,seq("/tt/ZZ.java:9: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method main",36)
             ,seq("/tt/ZZ.java:10: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method main",37)
             )
        );
    }

    @Test
    public void testLabel() {
        helpEsc("tt.ZZ",
            """
            package tt;
            public class ZZ {
              public void m() {
                int i = 0;
                //@ p:;
                i = 1;
                //@ q:{}
                i = 2;
                //@ check \\old(i,p) == 0;
                //@ check \\old(i,q) == 1;
                //@ check i == 2;
              }
            }
            """
        );
    }

    @Test
    public void testLabelBad() {
        expectedExit = 1;
        helpEsc("tt.ZZ",
            """
            package tt;
            public class ZZ {
              public void m() {
                int i = 0;
                //@ p:
                i = 1;
                //@ check i == 0;
              }
            }
            """
            ,"/tt/ZZ.java:5: error: ';' expected", 11
        );
    }

    @Test
    public void testImpliesInstanceof() {
        helpEsc("tt.ZZ",
            """
            package tt;
            public class ZZ {
              //@ requires o == (Integer)42 || o == "abc";
              public void m(Object o) {
                //@ assert o instanceof Integer i ==> i == 42;
              }
            }
            """
        );
    }

    @Test
    public void testLoopAssignsInference() {
        expectedExit = 1;
        addOptions("--infer=show");
        allowNotes(true);
        helpEsc("LOOP",
            """
            public class LOOP {
              public void m() {
                int k = 0;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
                //@ loop_assigns i,k;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
                //@ loop_assigns k;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
                //@ loop_assigns i;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
                //@ loop_decreases 10 - i;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
              }
            }
            """
           ,"/LOOP.java:4: Note: Inferred clause: //@ loop_writes \\count, i, k;", 5
           ,"/LOOP.java:15: Note: Inferred clause: //@ loop_writes k, \\count, i;", 9
           ,"/LOOP.java:25: error: Local variable is assigned but not present in loop frame clause: k not in //@ loop_writes i, \\count;", 7
           ,"/LOOP.java:28: Note: Inferred clause: //@ loop_writes \\count, i, k;", 5
        );
    }

    @Test
    public void testLoopAssignsInferenceB() {
        expectedExit = 1;
        allowNotes(true);
        addOptions("--infer=none");
        helpEsc("LOOP",
            """
            public class LOOP {
              public void m() {
                int k = 0;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
                //@ loop_assigns i,k;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
                //@ loop_assigns k;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
                //@ loop_assigns i;
                for (int i = 0; i < 10; i++) {
                  int j = 0;
                  j = 1;
                  k = 1;
                }
              }
            }
            """
            ,"/LOOP.java:4: error: Inference of loop_assigns clauses is disabled, so this loop requires an explicit loop_assigns clause", 5
            ,"/LOOP.java:7: error: Local variable is assigned but not present in loop frame clause: k not in //@ loop_writes \\count;", 7
            ,"/LOOP.java:4: error: Local variable is assigned but not present in loop frame clause: i not in //@ loop_writes \\count;", 29
            ,"/LOOP.java:16: error: Local variable is assigned but not present in loop frame clause: i not in //@ loop_writes k, \\count;", 29
            ,"/LOOP.java:25: error: Local variable is assigned but not present in loop frame clause: k not in //@ loop_writes i, \\count;", 7
        );
    }
}
