package org.jmlspecs.openjmltest.testsuites;
import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { }
                """
                ,oneof(
                        seq("/tt/TestJava.java: warning: Implicit executable does not exist $ROOT/OpenJML/OpenJMLsrc/../../Solvers/Solvers-macos/Z.X",-1)
                        ,seq("/tt/TestJava.java: warning: Implicit executable does not exist $ROOT/OpenJML/OpenJMLsrc/../../Solvers/Solvers-linux/Z.X",-1)
                    )
                ,"/tt/TestJava.java: error: The executable for prover Z is not specified - use -exec or define an openjml.prover.... property",-1
                );
    }
    
    @Test
    public void testNoExec() {
        expectedExit=1;
        addOptions("--exec= ");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { }
                """
                ,"/tt/TestJava.java: error: The executable for prover z3_4_3 is not specified - use -exec or define an openjml.prover.... property",-1
                );
    }
    
    @Test
    public void testTimeoutBad() {
        expectedExit=0;
        addOptions("--timeout=ZZ");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { }
                """
                ,"/tt/TestJava.java: warning: Timeout value cannot be parsed as a double: ZZ",-1
                );
    }
    
    @Test
    public void testTimeoutOK() {
        expectedExit=0;
        addOptions("--timeout", "");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { }
                """
                );
    }
    
    @Test
    public void testDebugOK() { // Test is noisy because debug feasibility turns on progress // FIXME - capture/redirect the output to stdout
        expectedExit=0;
        addOptions("--check-feasibility", "debug:");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { }
                """
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                );
    }
    
    @Test
    public void testDebugBad() { // Test is noisy because debug feasibility turns on progress // FIXME - capture/redirect the output to stdout
        expectedExit=0;
        addOptions("--check-feasibility", "debug:zzz");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { }
                """
                ,"/tt/TestJava.java: warning: debug feasibility starting number has bad format: zzz", -1
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                ,"/tt/TestJava.java:2: verify: There is no feasible path to program point FeasibilityDebugAssert in method tt.TestJava.TestJava()", 8 // Exception checking is dead code
                );
    }
    
    @Test
    public void testAbsentSpec1() {
        expectedExit=0;
        addOptions("--check-feasibility=none");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { /*@ requires i > 0; */ public void m(int i) {}}
                class A extends TestJava {
                    public void p() { m(0); }
                    public void m(int i) {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method p", 24
                ,"/tt/TestJava.java:5: verify: Associated declaration", 17
                ,"/tt/TestJava.java:2: verify: Precondition conjunct is false: i > 0", 40
                );
    }
    
    @Test
    public void testAbsentSpec2() {
        expectedExit=0;
        addOptions("--check-feasibility=none");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { /*@ requires i > 0; */ public void m(int i) {}}
                class A extends TestJava {
                    public void p() { m(0); }
                    //@ also ensures true;
                    public void m(int i) {}
                }
                """
                );
    }
    
    @Test
    public void testAbsentSpec3() {
        expectedExit=0;
        addOptions("--check-feasibility=none");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { /*@ requires i > 0; */ public void m(int i) {}}
                class A extends TestJava {
                    public void p() { m(0); }
                    //@ pure
                    public void m(int i) {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method p", 24
                ,"/tt/TestJava.java:6: verify: Associated declaration", 17
                ,"/tt/TestJava.java:2: verify: Precondition conjunct is false: i > 0", 40
                );
    }
    
    @Test
    public void testAbsentSpec4() {
        expectedExit=0;
        addOptions("--check-feasibility=none");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { /*@ requires i > 0; */ public void m(int i) {}}
                class A extends TestJava {
                    public void p() { m(0); }
                    //@ final
                    public void m(int i) {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method p", 24
                ,"/tt/TestJava.java:6: verify: Associated declaration", 17
                ,"/tt/TestJava.java:2: verify: Precondition conjunct is false: i > 0", 40
                );
    }
    
    @Test
    public void testAbsentSpec5() {
        expectedExit=0;
        addOptions("--check-feasibility=none");
        helpEsc("tt.TestJava",
                """
                package tt; //@ pure
                public class TestJava { /*@ requires i > 0; */ public void m(int i) {}}
                class A extends TestJava {
                    public void p() { m(0); }
                    public void m(int i) {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method p", 24
                ,"/tt/TestJava.java:5: verify: Associated declaration", 17
                ,"/tt/TestJava.java:2: verify: Precondition conjunct is false: i > 0", 40
                );
    }
    
    @Test
    public void testAbsentSpec6() {
        expectedExit=0;
        addOptions("--check-feasibility=none");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i > 0;
                  //@ pure
                  public void m(int i) {}
                  public int k;
                }
                class A extends TestJava {
                    public void p() { m(0); }
                    //@ pure
                    public void m(int i) { k = 0; }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Precondition) in method p", 24
                ,"/tt/TestJava.java:11: verify: Associated declaration", 17
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: i > 0", 18
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assignable) in method m: k", 30
                ,"/tt/TestJava.java:4: verify: Associated declaration", 7
                );
    }
    
    @Test
    public void testSMTout() {
        expectedExit=0;
        addOptions("--smt=smt/testSMToutZ.smt");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { }
                """
                );
        new java.io.File("smt/testSMToutZ.smt").delete();
    }
    
    @Test
    public void testSimple() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {

                  public void m1bad(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>=0;
                  public void m2bad(int i) {
                    //@ assert i>0 ;
                  }
                  //@ requires i>=0;
                  //@ ensures \\result>0;
                  public int m3bad(int i) {
                    return i ;
                  }
                  public void m1good(int i) {
                    //@ assume i>0 ;
                    //@ assert i>0 ;
                  }
                  //@ requires i>0;
                  public void m2good(int i) {
                    //@ assert i>=0 ;
                  }
                  //@ requires i>=0;
                  //@ ensures \\result>=0;
                  public int m3good(int i) {
                    return i ;
                  }
                  //@ requires i>0;
                  //@ also
                  //@ requires i==0;
                  public void m4good(int i) {
                    //@ assert i>=0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2bad",9
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Postcondition) in method m3bad",5
                ,"/tt/TestJava.java:12: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testFieldAccess() {
        addOptions("--check-feasibility=none"); // Part of test
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  int f;
                  public void m1bad(TestJava o) {
                    //@ assume o.f >0 ;
                    //@ assert f > 0 ;
                  }
                  public void m2bad(@Nullable TestJava o) {
                    //@ assume o.f >0 ;
                  }
                  public void m1good(TestJava o) {
                    //@ assume o.f >0 ;
                    //@ assume o == this ;
                    //@ assert f > 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m2bad",17
                );
    }
    
    @Test
    public void testArrayAccess() {
        helpEsc("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires a.length > 5;
                  public void m1bad(int @Nullable [] a) {
                    //@ assume a[1] == 0 ;
                  }
                  //@ requires a != null;
                  public void m2bad(int[] a) {
                    //@ assume a[1] == 0 ;
                  }
                  //@ requires a != null;
                  //@ requires a.length > 5;
                  public void m3bad(int[] a) {
                    //@ assume a[-1] == 0 ;
                  }
                  //@ requires a != null;
                  //@ requires a.length > 5;
                  //@ requires b.length > 5;
                  public void m4bad(int[] a, int[] b) {
                    //@ assume a[1] == 5 ;
                    //@ assert b[1] == 5 ;
                  }
                  //@ requires a != null;
                  //@ requires a.length > 5;
                  public void m1good(int[] a, int[] b) {
                    //@ assume a[1] == 5 ;
                    //@ assume a == b ;
                    //@ assert b[1] ==5 ;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1bad",17
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m2bad",17
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m3bad",17
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Assert) in method m4bad",9
                );
    }
    
    @Test
    public void testArrayAccess1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NullableByDefault public class TestJava {
                  public void m1() {
                    int[] a = null;
                    a[0] = 0;
                  }
                  public void m2() {
                    int[] a = null;
                    int i = (a)[0];
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",6
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2",16
                );
    }
   
    @Test
    public void testArrayLength() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  public void m1(int[] c) {
                    //@ assert c != null;
                    //@ assert c.length >= 0;
                  }
                }
                """
                );
    }
   
    @Test
    public void testArrayAssign() {
        helpEsc("tt.TestJava",
                """
                package tt;
                import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires a.length > 5;
                  public void m1bad(int @Nullable [] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null;
                  public void m2bad(int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null;
                  //@ requires a.length > 5;
                  public void m3bad(int[] a) {
                    a[-1] = 0 ;
                  }
                  //@ requires a != null;
                  //@ requires a.length > 5;
                  //@ requires b.length > 5;
                  public void m4bad(int[] a, int[] b) {
                    a[1] = 5 ;
                    //@ assert b[1] ==5 ;
                  }
                  //@ requires a != null;
                  //@ requires a.length > 5;
                  public void m1good(int[] a, int[] b) {
                    a[1] = 5;
                    //@ assume a == b ;
                    //@ assert b[1] ==5 ;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1bad",17
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m2bad",6
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m3bad",6
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Assert) in method m4bad",9
                );
    }

    @Test
    public void testArrayAssign1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                @NullableByDefault public class TestJava {
                  int i; static int j[];
                  //@ requires a.length > 3;
                  //@ assignable \\everything;
                  public int m0bada(int[] a) {
                    a[1] = 1;
                    return a[0];
                  }
                  //@ requires a != null;
                  //@ assignable \\everything;
                  public int m0badb(int[] a) {
                    a[1] = 1;
                    return a[0];
                  }
                  //@ requires a != null && a.length > 3;
                  //@ assignable \\everything;
                  //@ ensures \\result == \\old(a[0]);
                  public int m0badc(int[] a) {
                    a[-1] = 1;
                    return a[0];
                  }
                  //@ requires a != null && a.length > 3;
                  //@ assignable \\everything;
                  //@ ensures \\result == \\old(a[0]);
                  public int m1good(int[] a) {
                    a[1] = 1;
                    return a[0];
                  }
                  //@ requires a != null && a.length > 3 && i >= 0 && i <= 1;
                  //@ assignable \\everything;
                  //@ ensures \\result == \\old(a[0]);
                  public int m1bad(int[] a, int i) {
                    a[i] = 1;
                    return a[0];
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  int f;
                  public void m1bad(TestJava o) {
                    o.f = 1 ;
                    //@ assert f > 0 ;
                  }
                  public void m2bad(@Nullable TestJava o) {
                    o.f = 1 ;
                    // @ assert f > 0 ;
                  }
                  public void m1good(TestJava o) {
                    o.f = 1 ;
                    //@ assume o == this ;
                    //@ assert f > 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2bad",6
                );
    }
    
    @Test 
    public void testFieldAssign1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  int i; static int j;
                  //@ assignable \\everything;
                  //@ ensures \\result == 2;
                  public int m1bad(boolean b) {
                    i = 1;
                    if (b) i = 2;
                    return i;
                  }
                  //@ assignable \\everything;
                  //@ ensures \\result == 10;
                  public int m2bad(boolean b) {
                    j = 1;
                    if (b) TestJava.j = TestJava.j + this.j + j;
                    if (b) tt.TestJava.j = TestJava.j + this.j + j;
                    if (b) this.j = j + 1;
                    return tt.TestJava.j;
                  }
                  //@ requires o != null;
                  //@ assignable \\everything;
                  //@ ensures \\result == 1;
                  public int m3bad(TestJava o) {
                    o.i = 1;
                    i = 2;
                    return o.i;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                 import org.jmlspecs.annotation.*;
                public class TestJava {
                  int i; static int j;
                  //@ assignable \\everything;
                  //@ ensures b ==> \\result == 2;
                  public int m1good(boolean b) {
                    i = 1;
                    if (b) i = 2;
                    return i;
                  }
                  //@ assignable \\everything;
                  //@ ensures b ==> \\result == 10;
                  public int m2good(boolean b) {
                    j = 1;
                    if (b) TestJava.j = TestJava.j + this.j + j;
                    if (b) tt.TestJava.j = TestJava.j + this.j + j;
                    if (b) this.j = j + 1;
                    return tt.TestJava.j;
                  }
                  //@ requires this != o && o != null;
                  //@ assignable \\everything;
                  //@ ensures \\result == 1;
                  public int m3good(TestJava o) {
                    o.i = 1;
                    i = 2;
                    return o.i;
                  }
                }
                """
                );
    }
    
    @Test
    public void testLet() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures (\\let int k = i; \\result == k);
                  public int m1(int i) {
                     return i;
                  }
                  //@ ensures (\\let int k = 1; \\result == k);
                  public int m1bad(int i) {
                     return 2;
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",6
                ,"/tt/TestJava.java:7: verify: Associated declaration",7
                );
    }
    
    @Test
    public void testAssertionError() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i) {
                     if (i < 0) assert false;
                  }
                  //@ requires i >= 0;
                  public void m1ok(int i) {
                     if (i < 0) assert false;
                  }
                  public void m2(int i) {
                     if (i < 0) throw new AssertionError();
                  }
                  //@ requires i >= 0;
                  public void m2ok(int i) {
                     if (i < 0) throw new AssertionError();
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m1",17
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m2",17
                );
    }
    
    @Test
    public void testLet2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures (\\let int k = i, int j = k; \\result == j);
                  public int m1(int i) {
                     return i;
                  }
                  //@ ensures (\\let int k = 1, int j = k; \\result == j);
                  public int m1bad(int i) {
                     return 2;
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",6
                ,"/tt/TestJava.java:7: verify: Associated declaration",7
                );
    }
    
// TODO - are these tests duplicated elsewhere?
    
    
    @Test
    public void testNullThrow1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1bad(int i) throws Exception {
                      if (i == 0)
                         throw null;
                  }
                  public void m2bad(int i, /*@ nullable */ Exception e) throws Exception {
                      if (i == 0)
                         throw e;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",16
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m2bad",16
                );
    }
    
    @Test
    public void testNullThrow2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i != 0;
                  public void m1good(int i) throws Exception {
                      if (i == 0)
                         throw null;
                  }
                  //@ requires i != 0;
                  public void m2good(int i, Exception e) throws Exception {
                      if (i == 0)
                         throw e;
                  }
                  public void m3good(int i, Exception e) throws Exception {
                      if (i == 0)
                         throw e;
                  }
                }
                """
                );
    }
    
    @Test public void testNullSynchronized1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1bad(/*@ nullable */ Object o) throws Exception {
                       synchronized (o) {};
                  }
                  public void m2bad( Object o) throws Exception {
                       synchronized (o) {
                          o = null; };
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m1bad",21
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullAssignment) in method m2bad",13
                );
    }

    @Test public void testNullSynchronized2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1good(Object o) throws Exception {
                       synchronized (o) {};
                  }
                  public void m2good(Object o) throws Exception {
                       synchronized (this) {};
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int f;
                  //@ requires a.length == 10;
                  public int m1bad(int[] a) {
                    return a[10] ;
                  }
                  //@ requires a.length == 10;
                  public int m1bada(int[] a) {
                    return a[-1] ;
                  }
                  //@ requires a.length == 10 && i >= 0;
                  public int m1badb(int[] a, int i) {
                    return a[i] ;
                  }
                  //@ requires a.length == 10;
                  public int m1good(int[] a) {
                    return a[0] ;
                  }
                  //@ requires a.length == 10;
                  public int m1gooda(int[] a) {
                    return a[9] ;
                  }
                  //@ requires a.length == 10;
                  //@ requires i >= 3;
                  //@ requires i <= 8;
                  public int m1goodb(int[] a, int i) {
                    return a[i] ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",13
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",13
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",13
                );
    }


    @Test
    public void testArrayIndex1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int f;
                  //@ requires a.length == 10;
                  public int m1bad(int[] a) {
                    return a[10] ;
                  }
                  //@ requires a.length == 10;
                  public int m1bada(int[] a) {
                    return a[-1] ;
                  }
                  //@ requires i > 1 && a.length == 10;
                  public int m1badb(int[] a, int i) {
                    return a[i] ;
                  }
                  //@ requires i < 5 && a.length == 10;
                  public int m1badc(int[] a, int i) {
                    return a[i] ;
                  }
                  //@ requires a.length == 10;
                  public int m1good(int[] a) {
                    return a[0] ;
                  }
                  //@ requires a.length == 10;
                  public int m1gooda(int[] a) {
                    return a[9] ;
                  }
                  //@ requires a.length == 10;
                  //@ requires i >= 3;
                  //@ requires i <= 8;
                  public int m1goodb(int[] a, int i) {
                    return a[i] ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",13
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1bada",13
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1badb",13
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1badc",13
                );
    }

    @Test
    public void testArrayValue() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int f;
                  //@ requires a.length == 10;
                  //@ ensures \\result == a[1];
                  public int m1bad(int[] a) {
                    return a[0] ;
                  }
                  //@ requires a.length == 10;
                  //@ ensures \\result == a[0];
                  public int m1good(int[] a) {
                    return a[0] ;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",5
                ,"/tt/TestJava.java:5: verify: Associated declaration",7
                );
    }



    @Test
    public void testHavocB() {
    	addOptions("--method=m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  /*@ non_null */ public TestJava ooo;
                  /*@ non_null */ public static TestJava sooo;
                  public void m1(boolean b, /*@ non_null */ TestJava o) {
                    ooo = o; sooo = o;
                    if (b) meverything();
                    //@ assert ooo != null;
                    //@ assert ooo instanceof TestJava;
                  }
                  public void meverything() {
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/ public class TestJava {
                  /*@ non_null */ public TestJava ooo;
                  /*@ non_null */ public static TestJava sooo;
                  public void m1(boolean b, /*@ non_null */ TestJava o) {
                    ooo = o; sooo = o;
                    if (b) meverything();
                    //@ assert ooo != null;
                    //@ assert ooo instanceof TestJava;
                  }
                  //@ assignable ooo;
                  public void meverything() {
                  }
                }
                """
                );
        }

    @Test
    public void testAssignment() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1bad(boolean i) {
                    int x = 0 ;
                    if (i) x = 1; else x = 2; ;
                    x = x + 1 ;
                    //@ assert x < 3 ;
                  }
                  public void m1ok(boolean i) {
                    int x = 0 ;
                    if (i) x = 1; else x = 2; ;
                    x = x + 1 ;
                    //@ assert x < 4 ;
                  }
                  public void m2ok(boolean i) {
                    int x = 10 ;
                    int y ;
                    x = (y = x + 1) + 2 ;
                    //@ assert x == 13 ;
                    //@ assert y == 11 ;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1bad",9
                );
        }


    @Test public void testAssignOp1() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public int f;
                  //@ requires j < 1000 && -1000 < j;
                  //@ ensures \\result == j+j+1;
                  public int m1good(int j) {
                    int i = j ;
                    return (i+=j+1) ;
                  }
                }
                """
                );
    }

    @Test public void testAssignOp1Div() {
        Assume.assumeTrue(runLongTests);
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public int f;
                  //@ requires j != 0;
                  public int m2good(int j) {
                    int i = j ;
                    return (i/=j) ;
                  }
                  //@ requires t != null;
                  //@ requires i != 0 && i != -1;
                  public void m3(TestJava t, int i) {
                    t.f /= i ;
                  }
                  //@ requires t != null;
                  //@ requires i != 0 && i != -1;
                  //@ assignable \\everything;
                  public void m3good(TestJava t, int i) {
                    t.f /= i ;
                  }
                }
                """
                );
    }

    @Ignore // takes a long time
    @Test public void testAssignOp2() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public int f;
                  //@ ensures \\result == j;
                  public int m1bad(int j) {
                    int i = j ;
                    return (i+=1) ;
                  }
                  public int m2bad(int j) {
                    int i = j ;
                    return (i/=j) ;
                  }
                  //@ assignable t.f;
                  //@ requires t != null;
                  public void m3badb(TestJava t, int i) {
                    t.f /= i ;
                  }
                  //@ requires i != 0;
                  //@ assignable \\everything;
                  public void m3badc(@Nullable TestJava t, int i) {
                    t.f /= i ;
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public int f;
                  //@ requires i != 0;
                  //@ assignable \\everything;
                  public void m4bad(@Nullable int[] a, int i) {
                    a[0] /= i ;
                  }
                  //@ requires a.length == 4;
                  //@ requires i != 0;
                  //@ assignable \\everything;
                  public void m4badb(@NonNull int[] a, int i) {
                    a[-1] /= i ;
                  }
                  //@ requires a.length == 4;
                  //@ requires i != 0;
                  //@ assignable \\everything;
                  public void m4badc(@NonNull int[] a, int i) {
                    a[4] /= i ;
                  }
                  //@ requires a.length == 4;
                  //@ assignable \\everything;
                  public void m4badd(@NonNull int[] a, int i) {
                    a[0] /= i ;
                  }
                  //@ requires a.length == 4;
                  //@ requires i != 0;
                  //@ assignable \\everything;
                  public void m4good(@NonNull int[] a, int i) {
                    a[0] /= i ;
                  }
                  public void m10ok(boolean i) {
                    int x = 10 ;
                    int y = 20 ;
                    x = (y += x + 1) + 2 ;
                    //@ assert x == 33 ;
                    //@ assert y == 31 ;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-9
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4bad",-6
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4bad",-6
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m4badb",6
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m4badc",6
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4badd",10
                );
    }

  
    @Test public void testArrays() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1bad( int /*@ nullable*/[] a, int i) {
                      a[1] = 9;
                  }
                  //@ requires i < a.length;
                  public void m2bad(int[] a, int i) {
                      a[i] = 9;
                  }
                  //@ requires i >= 0;
                  public void m3bad(int[] a, int i) {
                      a[i] = 9;
                  }
                  //@ requires i >= 0 && i < a.length;
                  public void m1good(int[] a, int i) {
                      a[i] = 9;
                  }
                }
                """
                ,anyorder(
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1bad",8),
                        seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1bad",8)
                        )
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2bad",8
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3bad",8
                );
    }
    
    @Test public void testArrayType1() { // TODO: CVC4 takes 147 sec
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int[] a) {
                      //@ assume a != null && a.length > 1;
                      a[0] = 9;
                  }
                  public void m2(Integer[] a, Integer i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      Object[] o = a;
                      o[0] = i;
                  }
                  public void m3(Integer[] a, Integer i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      //@ assume \\elemtype(\\typeof(a)) == \\type(Integer);
                      Object[] o = a;
                      o[0] = i;
                  }
                  public void m4bad(Integer[] a, Object i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      Object[] o = a;
                      o[0] = i;
                  }
                  static class A {}
                  static class B extends A {}
                }
                """
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m4bad",12
                );
    }

    @Test public void testArrayType1Bug() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int[] a) {
                      //@ assume a != null && a.length > 1;
                      a[0] = 9;
                  }
                  public void m2bad(String[] a, Integer i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      Object[] o = a;
                      o[0] = i;
                  }
                  public void m3(String[] a, String i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      //@ assume \\elemtype(\\typeof(a)) == \\type(String);
                      Object[] o = a;
                      o[0] = i;
                  }
                  public void m4bad(String[] a, Object i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      Object[] o = a;
                      o[0] = i;
                  }
                  static class A {}
                  static class B extends A {}
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m2bad",12
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m4bad",12
                );
    }
    
    @Test public void testArrayType2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m3a(Integer[] a, Integer i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      Object[] o = a;
                      o[0] = i;
                  }
                  public void m5bad(A[] a, B i) { // FAILS because 'a' might have a dynamic type that does not hold a B
                      //@ assume a != null && a.length > 1 && i != null;
                      Object[] o = a;
                      o[0] = i;
                  }
                  public void m5(A[] a, B i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      //@ assume \\type(B) <:= \\elemtype(\\typeof(a));
                      Object[] o = a;
                      o[0] = i;
                  }
                  static class A {}
                  static class B extends A {}
                }
                """
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method m5bad",12
                );
    }
    
    @Test public void testArrayType2Bug() { // TODO: CVC4 takes 186 sec
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m3a(String[] a, String i) {
                      //@ assume a != null && a.length > 1 && i != null;
                      Object[] o = a;
                      o[0] = i;
                  }
                  static class A {}
                  static class B extends A {}
                }
                """
                );
    }
    
    
    @Test public void testMethodWithConstructorNameFixed() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public byte[] b;
                  //@ public invariant b != null && b.length == 20;
                  public TestJava(int i) {
                      b = new byte[20];
                  }
                }
                """
                );
    }
    
    @Test public void testMultiException() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {}
                  public void mm() {
                  try {
                    m();
                  } catch (NullPointerException|ArithmeticException e) {
                     //@ assert e instanceof NullPointerException || e instanceof ArithmeticException;
                  }}
                }
                """
                );
    }
    
    @Test public void testExceptionTypeC() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void mm(int i) throws ClassNotFoundException, NoSuchMethodException {
                  try {
                    if (i == 0) throw new ClassNotFoundException();
                    if (i == 1) throw new NoSuchMethodException();
                  } catch (Exception e) {
                     throw e;
                  }}
                }
                """
                );
    }
    
    @Test public void testExceptionType() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ signals_only NullPointerException, ArithmeticException;
                  public void mm(int i) throws NullPointerException, ArithmeticException {
                  try {
                    if (i == 0) throw new NullPointerException();
                    if (i == 1) throw new ArithmeticException();
                  } catch (Exception e) {
                     throw e;
                  }}
                }
                """
                );
    }
    
    @Test public void testExceptionTypeB() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ signals_only NullPointerException;
                  public void mm(int i) throws NullPointerException {
                  try {
                    if (i == 0) throw new NullPointerException();
                    if (i == 1) throw new ArithmeticException();
                  } catch (Exception e) {
                     throw e;
                  }}
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (ExceptionList) in method mm",6
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }
    
    @Test public void testExceptionType2() {
    	expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void mm(int i) throws ClassNotFoundException {
                  try {
                    if (i == 0) throw new ClassNotFoundException();
                    if (i == 1) throw new NoSuchMethodException();
                  } catch (Exception e) {
                     throw e;
                  }}
                }
                """
                ,"/tt/TestJava.java:8: error: unreported exception java.lang.NoSuchMethodException; must be caught or declared to be thrown", 6
                ,optional("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (ExceptionList) in method mm",6)
                );
        // FIXME - in the above, the second error message appears to be non-deterministic
    }
    
    @Test public void testMethodWithConstructorNameOK() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public byte[] b;
                  //@ public invariant b != null && b.length == 20;
                  public TestJava(int i) {
                      b = new byte[20];
                  }
                  // The following method - not constructor - note the return type
                  // appears to be legal Java
                  public void TestJava(int i) {
                      b = new byte[20];
                  }
                }
                """
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
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int b;
                  public Integer bb;
                  public TestJava(Integer b, int bb) {
                    this.b = b;
                    this.bb = bb;
                  }
                }
                """
                );
    }
    
    // A problem from MHuisman, with String initialization and invariants
    @Test public void testStringInitialization() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public String x = new String();
                  public TestJava(String xx) {
                    this.x = xx;
                  }
                }
                """
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
    
    @Test
    public void testReturnNullity() {
        helpEsc("RET",
            """
            import org.jmlspecs.annotation.*;
            public class RET {
            
              public static class R<T> {
                public T m(T t) { return t; }
                public /*@ nullable */ T q(T t) { return t; }
                public /*@ non_null */ T s(T t) { return t; }
              }
              public void z() {
                  Integer i = 42;
            
                  /*@ nullable */
                  Object x = new R<Integer>().m(i);
                  //@ check x != null; // OK - default
                  x = new R</*@ non_null */ Integer>().m(i);
                  //@ check x != null; // OK - explicit type-variable
                  x = new R</*@ nullable */ Integer>().m(i);
                  //@ check x != null; // FAILS - explicit type-variable
                  x = new R<Integer>().q(i);
                  //@ check x != null; // FAILS - explicit in decl
                  x = new R<@NonNull Integer>().q(i);
                  //@ check x != null; // FAILS - explicit in decl
                  x = new R<@Nullable Integer>().q(i);
                  //@ check x != null; // FAILS - explicit in decl
                  x = new R<Integer>().s(i);
                  //@ check x != null; // OK - explicit in decl
                  x = new R<@NonNull Integer>().s(i);
                  //@ check x != null; // OK - explicit in decl and type variable
                  x = new R<@Nullable Integer>().s(i);
                  //@ check x != null; // OK - explicit in decl
            
                }
            }
            """
            ,anyorder(
                 seq("/RET.java:18: verify: The prover cannot establish an assertion (Assert) in method z",11)
                ,seq("/RET.java:20: verify: The prover cannot establish an assertion (Assert) in method z",11)
                ,seq("/RET.java:22: verify: The prover cannot establish an assertion (Assert) in method z",11)
                ,seq("/RET.java:24: verify: The prover cannot establish an assertion (Assert) in method z",11)
                )
        );
    }
}
