package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escm extends EscBase {
    
    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--code-math=bigint");  // To avoid overflow reports and semantics
    }
    
    /** This test checks that nested, local and anonymous classes are handled */
    @Test
    public void testNestedClass() {
        helpEsc("tt.TestJava",
        """
        package tt;
        import org.jmlspecs.annotation.*;
        @NonNullByDefault public class TestJava {
            public TestJava t;
            public int a;
            public static int b;
            public void m1(TestJava o) {
                class C { void m() { /*@ assert false; */ }};
                C x;
                C y = new C() { void m() {/*@ assert false; */}};
                //@ assert false;
            }
            public static class A {
                public void m2() {
                    //@ assert false;
                }
            }

            /*@ pure */ public TestJava() { t = new TestJava(); }
        }
        """
        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m",34
        ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m",39
        ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m1",13
        ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method m2",17
        );
    }
   
    /** This test checks that the specs of methods in nested, local and anonymous classes are used */
    @Test
    public void testNestedMethodSpecs() {
        helpEsc("tt.TestJava",
                "package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"
                
                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"
                
                +"  public void me(TestJava o) {\n"
                +"       class C { /*@ ensures false; */ void mc() {  }};\n"
                +"       C x;\n"
                +"       class D { void md() {  }};\n" // Line 10
                +"       D y = new D() { /*@ also ensures false; */ void md() {}};\n"
                +"       class E { /*@ ensures false; */void me() {  }};\n"
                +"       E z = new E() {  void me() {}};\n"
                +"  }\n"
                
                +"  public static class A {\n"
                +"       //@ ensures false;\n"
                +"     public void m2() {\n"
                +"     }\n"
                +"  }\n"
                
                +"  /*@ pure */ public TestJava() { t = new TestJava(); }\n"
                
                +"}"
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method mc",45
                ,"/tt/TestJava.java:8: verify: Associated declaration",22
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Postcondition) in method md",56
                ,"/tt/TestJava.java:11: verify: Associated declaration",33
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Postcondition) in method me",44
                ,"/tt/TestJava.java:12: verify: Associated declaration",22
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Postcondition) in method me",30
                ,"/tt/TestJava.java:12: verify: Associated declaration",22
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Postcondition) in method m2",18
                ,"/tt/TestJava.java:16: verify: Associated declaration",12
                );
    }
   
    /** This test checks that the specs of nested, local and anonymous classes are used */
    @Test
    public void testNestedClassSpecs() {
        addOptions("--check-feasibility=precondition,exit");
        helpEsc("TestJava",
                """
                import org.jmlspecs.annotation.*;
                @NonNullByDefault public class TestJava {
                  public TestJava t;
                  public int a;
                  public static int b;
                  public void m1(TestJava o) {
                       class C {
                           //@ public invariant false;
                           void m() {  }};  // Line 10
                       C x;  // Line 10
                       class D { void m() {  }}
                       D y = new D() { /*@ public invariant false;*/ void m() {}};
                       // After execution of D(), D's invariants are assumed, which includes assuming false -- hence the feasibility failure
                       class E { /*@ public invariant false;*/void mm() {  }};
                       E z = new E() {  void mm() {}};
                  }
                  public static class A {
                     //@ public invariant false;
                     public void m2() {
                     }
                  }
                  /*@ pure */ public TestJava() { t = new TestJava(); }
                }
                """
                ,"/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method C",8  // C.<init>
                ,"/TestJava.java:8: verify: Associated declaration",23
                ,"/TestJava.java:9: verify: Invariants+Preconditions appear to be contradictory in method C.m()",17  // The false invariant is triggered as a constructor postcondition
                ,"/TestJava.java:12: verify: Invariants+Preconditions appear to be contradictory in method TestJava.1.m()",59 // m() of anonymous D
                ,"/TestJava.java:14: verify: The prover cannot establish an assertion (InvariantExit) in method E",8  // E.<init>
                ,"/TestJava.java:14: verify: Associated declaration",29
                ,"/TestJava.java:14: verify: Invariants+Preconditions appear to be contradictory in method E.mm()",52 
                ,"/TestJava.java:15: verify: Invariants+Preconditions appear to be contradictory in method TestJava.2.mm()",30
                ,"/TestJava.java:16: verify: There is no feasible path to program point at program exit in method TestJava.m1(TestJava)",3
                ,"/TestJava.java:17: verify: The prover cannot establish an assertion (InvariantExit) in method A",17  // A
                ,"/TestJava.java:18: verify: Associated declaration",17
                ,"/TestJava.java:19: verify: Invariants+Preconditions appear to be contradictory in method TestJava.A.m2()",18
                );
    }
    
    /** This tests that the specs of model classes and methods are checked */
    @Test
    public void testModelSpecs() {
    	addOptions("-show:translated","--check-feasibility=basic");
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { \n"

                +"  public TestJava t;\n"
                +"  public int a;\n"
                +"  public static int b;\n"

                +"  public int m1(TestJava o) {\n"
                +"       /*@ model class C {  \n"  // Invariant is false on exit
                +"           invariant false;\n" 
                +"           pure void mc() {  }};*/ \n"  // Line 10  // Invariants are not satisfiable on entry
                +"       /*@ model class D {  \n"
                +"           ensures false; pure\n" 
                +"           void md() {  }};*/ \n"   // Postcondition is false on exit
                +"       /*@ model class E {  \n"
                +"           pure void me() {  assert false; }};*/ \n" // Assertion is false
                +"       //@ ghost E e;\n"
                +"       return 0;\n"
                +"  }\n"

                +"  /*@ ensures false; pure\n"
                +"      model void mm() {}*/\n"  // Line 20  // Postcondition is false

                +"  /*@ pure model void mn() {  assert false;  }*/\n"  // Assertion is false

                +"  /*@ model public static class A {\n"  // Invariant is false on exit
                +"     invariant false;\n"
                +"     pure public void m2() {\n"  // Invariant is not satisfiable on entrance
                +"     }*/\n"
                +"  }"
                +"  /*@ public normal_behavior ensures t != null; *//*@ pure */ public TestJava() { t = new TestJava(); }\n"
                +"}"
                +"  /*@ model class B {\n" // Invariant is false on exit
                +"     public invariant false; \n"
                +"     pure public void mb() {\n"  // Invariant is not satisfiable on entrance
                +"     }*/\n"
                +"  }\n"

                +"  /*@ model class BB {\n"
                +"     ensures false;\n"
                +"     pure public void mbb() {\n" // Postcondition is false
                +"     }*/\n"
                +"  }\n"


                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (InvariantExit) in method C",18
                ,"/tt/TestJava.java:9: verify: Associated declaration",12
                ,"/tt/TestJava.java:10: verify: Invariants+Preconditions appear to be contradictory in method C.mc()",22
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Postcondition) in method md",17
                ,"/tt/TestJava.java:12: verify: Associated declaration",12
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method me",30
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (Postcondition) in method mm",18
                ,"/tt/TestJava.java:19: verify: Associated declaration",7
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method mn",31
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (InvariantExit) in method A", 27
                ,"/tt/TestJava.java:23: verify: Associated declaration", 6
                ,"/tt/TestJava.java:24: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.A.m2()", 23
                ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (InvariantExit) in method B",14
                ,"/tt/TestJava.java:28: verify: Associated declaration",13
                ,"/tt/TestJava.java:29: verify: Invariants+Preconditions appear to be contradictory in method tt.B.mb()",23
                ,"/tt/TestJava.java:34: verify: The prover cannot establish an assertion (Postcondition) in method mbb",23
                ,"/tt/TestJava.java:33: verify: Associated declaration",6
        );
    }
    
    @Test
    public void testAnon() {
    	expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                                +" import org.jmlspecs.annotation.*; \n"
                                +"@NonNullByDefault public class TestJava { public int x; \n"

                                +"  public void mm() {\n"
                                +"       //@ assert new TestJava() {  public invariant x >= 0; public void mm() { } } != null; \n"  // Line 5
                                +"  }\n"
                                +"}\n"
                                ,"/tt/TestJava.java:5: error: Object allocation is not permitted in specification expressions",19
                                // The above error messaqe is a type-checking message, so no esc checking is done
                                );
    }

    @Test
    public void testAnonX() {
        addOptions("-checkFeasibility=exit");
    	expectedExit = 1;
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { public static int i; \n"

                +"  public int m1(TestJava o) {\n"
                +"       //@ assert new TestJava() {  invariant false; int i; } != null; \n"  // Line 5 
                +"       return 0;\n"
                +"  }\n"
                
                +"  public int m2(TestJava o) {\n"
                +"       //@ assert new TestJava() {  int i; } == null; \n"  // Line 9
                +"       return 0;\n"
                +"  }\n"

                +"  public int m3(TestJava o) {\n"
                +"       //@ assert new TestJava() {  invariant true; int i; } == null; \n"  // Line 13
                +"       return 0;\n"
                +"  }\n"

                +"}\n"
                ,"/tt/TestJava.java:5: error: Object allocation is not permitted in specification expressions",19
                ,"/tt/TestJava.java:9: error: Object allocation is not permitted in specification expressions",19
                ,"/tt/TestJava.java:13: error: Object allocation is not permitted in specification expressions",19
                // The above error messaqe is a type-checking message, so no esc checking is done
        );
    }


    @Test
    public void testAnonZ() {
        addOptions("--check-feasibility=basic");
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { public static int i; \n"

                +"  public int m1(TestJava o) {\n"
                +"       boolean b = new TestJava() {  /*@ invariant false; */ int i; } != null; \n"  // Line 5 // TODO: Perhaps have the column npoint to the invariant
                +"       //@ assert b;\n"
                +"       return 0;\n"
                +"  }\n"
                
                +"  public int m2(TestJava o) {\n"
                +"       boolean b = new TestJava() {  int i; } == null; \n"  // Line 10
                +"       //@ assert b;\n"
                +"       return 0;\n"
                +"  }\n"

                +"  public int m3(TestJava o) {\n"
                +"       boolean b = new TestJava() {  /*@ invariant true; */ int i; } == null; \n"  // Line 15
                +"       //@ assert b;\n"
                +"       return 0;\n"
                +"  }\n"

                +"}\n"
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.m1(tt.TestJava)",12
                ,"/tt/TestJava.java:8: verify: There is no feasible path to program point at program exit in method tt.TestJava.m1(tt.TestJava)",3
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m2",12
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Assert) in method m3",12
        );
    }


    @Test
    public void testAnonY() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { public static int i; \n"

                +"  public int m1(TestJava o) {\n"
                +"       boolean b = new TestJava() {  } != null;\n"
                +"       //@ assert b; \n"  // Line 5
                +"       return 0;\n"
                +"  }\n"
                
                +"  /*@ requires i > 0; pure */public TestJava() {}"
                +"}\n"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Precondition) in method m1",20
                ,"/tt/TestJava.java:9: verify: Associated declaration",7
                ,"/tt/TestJava.java:9: verify: Precondition conjunct is false: i > 0",18
        );
    }


    @Test
    public void testMethodsInSpecs() {
        addOptions("--check-feasibility=precondition,assert,exit");
        helpEsc("tt.TestJava","package tt; "
                +" import org.jmlspecs.annotation.*; \n"
                +" //@ code_java_math spec_java_math \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public int m(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 3; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 2; \n"
                    +"  public int m1bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires m(j) == 3; \n"
                    +"  //@ ensures \\result == 3; \n"
                    +"  public int m3b(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"  // Line 22

                    +"  public void m2(int j) {\n"
                    +"       j = j+1;\n"
                    +"       //@ assert m(j) == \\old(j) + 2;\n"
                    +"  }\n"
                    
                    +"  //@ public normal_behavior\n"
                    +"  //@   requires b;\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public int mm(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == mm(j); \n" // Postcondition error - undefined precondition for mm
                    +"  public int m4bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires b; \n"
                    +"  //@ ensures \\result == mm(j); \n"
                    +"  public int m4(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures b ==> \\result == mm(j); \n"
                    +"  public int m4a(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"}\n"
                    ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",8
                    ,"/tt/TestJava.java:14: verify: Associated declaration",7
                    ,"/tt/TestJava.java:34: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m4bad",28
                    ,"/tt/TestJava.java:31: verify: Associated declaration",14
                    ,"/tt/TestJava.java:36: verify: Associated method exit",8
                    ,optional("/tt/TestJava.java:28: verify: Precondition conjunct is false: b",18)
                );
    }

    @Test
    public void testFunctionsInSpecs() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; //@ code_java_math spec_java_math \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public static int m(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 3; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 2; \n"
                    +"  public int m1bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires m(j) == 3; \n"
                    +"  //@ ensures \\result == 3; \n"
                    +"  public int m3b(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"  // Line 22

                    +"  public void m2(int j) {\n"
                    +"       j = j+1;\n"
                    +"       //@ assert m(j) == \\old(j) + 2;\n"
                    +"  }\n"
                    
                    +"  //@ public normal_behavior\n"
                    +"  //@   requires b;\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  public static int mm(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n" // Line 33

                    +"  //@ ensures \\result == mm(j); \n" // Postcondition error - undefined precondition for mm
                    +"  public int m4bad(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ requires b; \n"
                    +"  //@ ensures \\result == mm(j); \n"
                    +"  public int m4(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ ensures b ==> \\result == mm(j); \n"
                    +"  public int m4a(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"


                    +"}\n"
                    ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m1bad",8
                    ,"/tt/TestJava.java:14: verify: Associated declaration",7
                    ,"/tt/TestJava.java:34: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m4bad",28
                    ,"/tt/TestJava.java:31: verify: Associated declaration",21
                    ,"/tt/TestJava.java:36: verify: Associated method exit",8
                    ,optional("/tt/TestJava.java:28: verify: Precondition conjunct is false: b",18)
                );
    }

    @Test
    public void testMethodsInSpecs2() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures mm(\\result) + 1 == mm(k);\n"
                    +"  //@ pure spec_java_math code_java_math \n"
                    +"  public int m(int k) {\n"
                    +"       return k-1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure spec_java_math code_java_math \n"
                    +"  public int mm(int k) {\n"
                    +"       return k+1;\n"
                    +"  }\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 1; \n"
                    +"  //@ pure spec_java_math code_java_math \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"


                    +"}\n"
                );
    }

    @Test
    public void testMethodsInSpecs3() {
        helpEsc("tt.TestJava","package tt;\n"
                +" import org.jmlspecs.annotation.*; \n"
                +" //@ code_java_math spec_java_math \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 1; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures mm(\\result) + 1 == mm(k);\n"
                    +"  //@ pure\n"
                    +"  public int m(int k) {\n"
                    +"       return k-1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  //@ model public int mm(int k);\n"


                    +"}\n"
                );
    }

    @Test
    public void testMethodsInSpecs3MQ() {
        helpEsc("tt.TestJava","package tt; \n"
                +" import org.jmlspecs.annotation.*; \n"
                +"@NonNullByDefault public class TestJava { static public boolean b; \n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures mm(\\result) + 1 == mm(k);\n"
                    +"  //@ pure\n"
                    +"  public int m(int k) {\n"
                    +"       return k-1;\n"
                    +"  }\n"

                    +"  //@ public normal_behavior\n"
                    +"  //@   ensures \\result == k+1;\n"
                    +"  //@ pure\n"
                    +"  //@ model public int mm(int k);\n"

                    +"  //@ ensures \\result == 2 + m(j+1) - 1; \n"
                    +"  public int m1(int j) {\n"
                    +"       return j+1;\n"
                    +"  }\n"


                    +"}\n"
                );
    }
    
    @Test
    public void havocInit() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends P {
                  public int i;

                  //@ requires 0 <= i < a.length;
                  public void m(int[] a, TestJava t) {
                    int j;
                    //@ havoc j, i;
                    //@ havoc this.i, super.j, t.i;
                    //@ havoc this.*, t.*, super.*;
                    //@ havoc a[i];
                    //@ havoc a[i..i];
                    //@ havoc a[i..];
                    //@ havoc a[*];
                    //@ havoc \\nothing;
                    //@ havoc \\everything;
                  }
                }
                class P { public int j; }
                """
                ,anyorder(
                        seq("/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m", 15)
                        ,seq("/tt/TestJava.java:11: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m", 15)
                        )
                );
    }

        // TODO
        // Need to check anonymous classes within specs
        // Need to check non-static inner classes 
        // Need to check anonymous classes for non-static classes
}