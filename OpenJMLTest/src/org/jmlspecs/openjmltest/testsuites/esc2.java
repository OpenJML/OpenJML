package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esc2 extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--nullable-by-default"); // Because the tests were written this way
        addOptions("--code-math=bigint","--spec-math=bigint");
    	addOptions("--no-require-white-space");
    }

    @Test
    public void testForEach2a4b() {
        addOptions("--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public class TestJava {
                  //@ public behavior  ensures true;
                  public void m4() {
                    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = false;
                    /*@ nullable */ Integer k = null;
                    values.add(k);
                  }
                  public TestJava() {}}
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Precondition) in method m4", 15
                ,"$SPECS/java/util/List.jml:119: verify: Associated declaration", 13
                ,"$SPECS/java/util/Collection.jml:141: verify: Precondition conjunct is false: containsNull || o != null", 33
                ,"$SPECS/java/util/List.jml:109: verify: Precondition conjunct is false: containsNull || o != null", 33
                );

    }
    @Test
    public void testForEach2a3() {
        addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public class TestJava {
                  //@ public normal_behavior  ensures true;
                  public void m3() {
                    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = true;
                    Integer k = Integer.valueOf(1);
                    values.add(k);
                  }
                  public TestJava() {}}
                """
                );
    }
    @Test
    public void testForEach2a4() {
        addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import java.util.*;
                public class TestJava {
                  //@ public normal_behavior  ensures true;
                  public void m4() {
                    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = true;
                    Integer k = 0;
                    values.add(k);
                  }
                  public TestJava() {}}
                """
                );
    }
    @Test
    public void testForEachBad() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1a() {
                    long[] a = { 1,2,3,4};
                    for (long k: a) {
                    }
                    //@ ghost int i = \\count; // Out of scope
                  }
                  public void m2() {
                    long[] a = { 1,2,3,4};
                    //@ ghost int i = \\count; // Out of scope
                  }
                  public void m4() {
                    long[] a = { 1,2,3,4};
                    for (long k: a) {
                      //@ set \\count = 6;  // Syntax error
                    }
                  }
                  public void v1a() {
                    Integer[] a = { 1,2,3,4};
                    for (Integer k: a) {
                    }
                    //@ ghost org.jmlspecs.lang.JMLList i = \\values; // Out of scope
                  }
                  public void v2() {
                    long[] a = { 1,2,3,4};
                    //@ ghost org.jmlspecs.lang.JMLList i = \\values; // Out of scope
                    }
                  public void v4() {
                    Integer[] a = { 1,2,3,4};
                    for (Integer k: a) {
                      //@ set \\values = null; // Syntax error
                    }
                  }
                  public void v10a() {
                    long[] a = { 1,2,3,4};
                    for (long k: a) {
                      //@ ghost org.jmlspecs.lang.JMLList i = \\values;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:7: error: A \\count token is used outside the scope of a foreach loop", 23
                ,"/tt/TestJava.java:11: error: A \\count token is used outside the scope of a foreach loop", 23
                ,"/tt/TestJava.java:16: error: unexpected type\n  required: variable\n  found:    value", 15
                ,"/tt/TestJava.java:16: error: Unexpected kind of LHS in a set statement: \\count", 15
                ,"/tt/TestJava.java:16: error: The LHS in a set statement must be a ghost variable", 15
                ,"/tt/TestJava.java:23: error: A \\values token is used outside the scope of a foreach loop", 45
                ,"/tt/TestJava.java:27: error: A \\values token is used outside the scope of a foreach loop", 45
                ,"/tt/TestJava.java:32: error: unexpected type\n  required: variable\n  found:    value", 15
                ,"/tt/TestJava.java:32: error: Unexpected kind of LHS in a set statement: \\values", 15
                ,"/tt/TestJava.java:32: error: The LHS in a set statement must be a ghost variable", 15
                );
    }
    
    @Test
    public void testNonNullElements0() {
//      Assume.assumeTrue(runLongTests);
      helpEsc("tt.TestJava",
              """
              package tt;
              public class TestJava {
                public void m1x(Object[] a) {
                  //@ assume a == null;
                  //@ check !\\nonnullelements(a); // OK
                  //@ check \\nonnullelements(a);  // NO
                }
              }
              """
              ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1x", 9
              );
  }
    

    @Test
    public void testNonNullElements1() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m1x(Object[] a) {
                    //@ assume \\nonnullelements(a);
                    //@ assume a.length > 1;
                    //@ assert a[0] != null; // OK
                  }
                  //@ modifies \\everything;
                  public void m11(Object[] a) {
                    //@ assume \\nonnullelements(a);
                    //@ assert a != null;   // OK
                  }
                  //@ modifies \\everything;
                  public void m11a(/*@ non_null */ Object[] a) {
                    //@ assume \\nonnullelements(a);
                    //@ assert a == null;   // BAD
                  }
                }
                """
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method m11a", 9
                );
    }

    @Test
    public void testNonNullElements2a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m1a(Object[] a) {
                    //@ assume a != null && a.length > 1;
                    //@ assert a[0] != null; // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1a", 9
                );
    }

    @Test
    public void testNonNullElements2b() {
//      Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m2(Object[] a) {
                    //@ assume a != null && a.length == 0;
                    //@ assert \\nonnullelements(a); // OK
                  }
                }
                """
                );
    }

    @Test
    public void testNonNullElements2c() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m22(Object[] a) {
                    //@ assume a != null && a.length == 0;
                    //@ assert (\\forall int i; 0<=i && i<a.length; a[i] != null); // OK
                  }
                }
                """
                );
    }

    @Test
    public void testNonNullElements3() {
//        Assume.assumeTrue(runLongests);
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires a != null && a.length == 1;
                  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;
                  public void m3(Object[] a) {
                    a[0] = new Object();
                    //@ assert \\nonnullelements(a); // OK
                  }
                  //@ requires a != null && a.length == 1;
                  //@ modifies \\everything;
                  public void m33(Object[] a) {
                    //@ assume a[0] != null;
                    //@ assert \\nonnullelements(a);  // OK
                  }
                  //@ requires a != null && a.length == 2;
                  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;
                  public void m4(Object[] a) {
                    a[0] = new Object();
                    a[1] = new Object();
                    //@ assert \\nonnullelements(a);   // OK
                  }
                }
                """
                );
    }

    @Test
    public void testNonNullElements4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m44(Object[] a) {
                    //@ assume a != null && a.length == 2;
                    //@ assume a[0] != null;
                    //@ assume a[1] != null;
                    //@ assert \\nonnullelements(a); // OK
                  }
                  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;
                  public void m4a(Object[] a) {
                    //@ assume a != null && a.length == 3;
                    a[0] = new Object();
                    a[1] = new Object();
                    //@ assert \\nonnullelements(a); // BAD -- FIXME cannot infer a forall quantifier from the individual statements
                  }
                  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;
                  public void m5(Object[] a) {
                    //@ assume \\nonnullelements(a) && a.length == 3;
                    a[0] = new Object();
                    //@ assert \\nonnullelements(a);  // OK
                  }
                  //@ modifies \\everything;
                  public void m5a(Object[] a) {
                    //@ assume a != null && a.length == 3;
                    a[0] = null;
                    //@ assert \\nonnullelements(a); // ERROR
                  }
                }
                """
                ,anyorder(
                seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (NullArgument) in method m4a", 34)
                ,seq("/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method m4a", 9)
                ,seq("/tt/TestJava.java:17: verify: The prover cannot establish an assertion (NullArgument) in method m5", 34)
                ,seq("/tt/TestJava.java:27: verify: The prover cannot establish an assertion (Assert) in method m5a", 9)
                )
                );
    }

    @Test
    public void testNotModified() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 5;
                  //@ modifies \\everything;
                  public void m1(int i) {
                    i = 5;
                    //@ assert \\not_modified(i); // OK
                  }
                  //@ modifies \\everything;
                  public void m1a(int i) {
                    i = 5;
                    //@ assert \\not_modified(i); // ERROR
                  }
                  public int i;
                  public static int si;
                  //@ ghost public int gi;
                  //@ requires i == 5;
                  //@ modifies \\everything;
                  public void m2() {
                    i = 5;
                    //@ assert \\not_modified(i); // OK
                  }
                  //@ modifies \\everything;
                  public void m2a() {
                    i = 5;
                    //@ assert \\not_modified(i); // ERROR
                  }
                  //@ requires si == 5;
                  //@ modifies \\everything;
                  public void m3() {
                    si = 5;
                    //@ assert \\not_modified(si);  // OK
                  }
                  //@ modifies \\everything;
                  public void m3a() {
                    si = 5;
                    //@ assert \\not_modified(si);  // ERROR
                  }
                  //@ requires gi == 5;
                  //@ modifies \\everything;
                  public void m4() {
                    //@ set gi = 5;
                    //@ assert \\not_modified(gi);   // OK
                  }
                  //@ modifies \\everything;
                  public void m4a() {
                    //@ set gi = 5;
                    //@ assert \\not_modified(gi);   // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m1a", 9
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Assert) in method m2a", 9
                ,"/tt/TestJava.java:37: verify: The prover cannot establish an assertion (Assert) in method m3a", 9
                ,"/tt/TestJava.java:48: verify: The prover cannot establish an assertion (Assert) in method m4a", 9
                );
    }

    // Test well-definedness within the implicit old
    @Test
    public void testNotModified2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int i;
                  public static /*@ nullable */ TestJava t;
                  //@ requires t != null;
                  //@ modifies \\everything;
                  public void m0() {
                    //@ assert \\not_modified(t.i); // OK
                  }
                  //@ requires t != null;
                  //@ modifies \\everything;
                  public void m1a() {
                    t = null;
                    //@ assert \\not_modified(t.i) ? true: true;  // ERROR
                  }
                  //@ requires t == null;
                  //@ modifies \\everything;
                  public void m1b() {
                    t = new TestJava();
                    //@ assert \\not_modified(t.i) ? true: true;   // OK
                  }
                  //@ modifies \\everything;
                  public void m1c() {
                    //@ assert \\not_modified(t.i) ? true: true;   // ERROR
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1a", 31
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1b", 31
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1c", 31
                );
    }

    // TODO - test not_modified and old nested in each other; remember to test
    // definedness



    @Test
    public void testOldJava() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math*/ public class TestJava {
                  static public  int i;
                  //@ static public constraint i > \\old(i);
                  //@ assigns i;
                  //@ ensures true;
                  public static void bok() { i = i - 1; }
                }
                """
                ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (Constraint) in method TestJava", 29
                ,"/tt/TestJava.java:4: verify: Associated declaration", 21
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method bok", 22
                ,"/tt/TestJava.java:4: verify: Associated declaration", 21
                );
    }



    @Test
    public void testOld2Math() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_bigint_math*/ public class TestJava {
                  static public int i;
                  //@ assigns i;
                  //@ ensures i == \\old(i)+2;
                  public static void bok() { i = i + 1; i = i + 1;}
                  //@ assigns i;
                  //@ ensures i == \\old(i+1);
                  public static void bbad() { i = i - 1; }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method bbad", 22
                ,"/tt/TestJava.java:8: verify: Associated declaration", 7
                );
    }

    @Test
    public void testOld2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math spec_java_math*/ public class TestJava {
                  static public int i;
                  //@ assigns i;
                  //@ ensures i == \\old(i)+2;
                  public static void bok() { i = i + 1; i = i + 1;}
                  //@ assigns i;
                  //@ ensures i == \\old(i+1);
                  public static void bbad() { i = i - 1; }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method bbad", 22
                ,"/tt/TestJava.java:8: verify: Associated declaration", 7
                );
    }

    // FIXME
//    @Test
//    public void testAt() {
//        expectedExit = 1;
//        helpEsc("tt.TestJava",
//                          "package tt; \n" 
//                        + "/*@ code_java_math spec_java_math*/ public class TestJava { \n" 
//                        + "  static public int i;\n"
//                        + "  //@ modifies i;\n" 
//                        + "  //@ ensures i == \\old(i)+2;\n"
//                        + "  public static void bok() { x: i = i + 1; /*@ assert i == i@x + 1 && i == (i+1)@x; */ i = i + 1;}\n" 
//                        + "  //@ modifies i;\n"
//                        + "  //@ ensures i == \\old(i+1);\n" 
//                        + "  public static void bbad() { i = i - 1; /*@ assert i == i@x + 1; */ }\n" 
//                        + "  //@ modifies i;\n" 
//                        + "  public void bok2() { x: i = i + 1; /*@ assert i == this.i@x + 1; */ i = i + 1;}\n" 
//                        + "  //@ requires a.length > 10 && a[0] >= 0;\n" 
//                        + "  //@ modifies i;\n" 
//                        + "  public static void bok3(int[] a) { x: i = i + 1; /*@ assert a[0]@x > -1; */ i = i + 1;}\n" 
//                        + "}"
//                ,"/tt/TestJava.java:9: error: There is no label named x", 60
//                );
//    }
//

    @Test
    public void testWhileSpecs() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                /*@ code_bigint_math*/ public class TestJava {
                  public void insta() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }
                  public void instb() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i-2; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }
                  public void instc() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i; */ while (i>0) { i = i+1; } /*@ assert i == 0; */ }
                  public void instd() { int i = 5; /*@ loop_invariant i<=5 && i>0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }
                }
                """
                ,anyorder(
                seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopDecreasesNonNegative) in method instb",69)
                // ,"/tt/TestJava.java:4: verify: Associated declaration",69
                ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopDecreases) in method instc",69)
                // ,"/tt/TestJava.java:5: verify: Associated declaration",69                
                ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopInvariant) in method instc",40)
                ,seq("/tt/TestJava.java:6: verify: The prover cannot establish an assertion (LoopInvariant) in method instd",40)
                )
                // ,"/tt/TestJava.java:6: verify: Associated declaration",40
                // FIXME - adjust to have the location + associated declaration
                );
    }

    @Test
    public void testWhileSpecs2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void insta() { int i = 5; /*@ loop_invariant i> 0; decreases i; */ while (--i > 0) { } /*@ assert i == 0; */ }
                  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i-- > 0) { } /*@ assert i == -1; */ }
                  public void instc() { int i = 5; /*@ loop_invariant i> 1; decreases i; */ while (--i > 1) { } /*@ assert i == 1; */ }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method insta", 40
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method instb", 40
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method instc", 40
                );
    }

    @Test
    public void testIncDec() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst1() { int i = 5; i++; /*@ assert i == 6; */ }
                  public void inst1b() { int i = 5; i++; /*@ assert i == 5; */ }
                  public void inst2() { int i = 5; i--; /*@ assert i == 4; */ }
                  public void inst2b() { int i = 5; i--; /*@ assert i == 5; */ }
                  public void inst3() { int i = 5; ++i; /*@ assert i == 6; */ }
                  public void inst3b() { int i = 5; ++i; /*@ assert i == 5; */ }
                  public void inst4() { int i = 5; --i; /*@ assert i == 4; */ }
                  public void inst4b() { int i = 5; --i; /*@ assert i == 5; */ }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1b", 46
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst2b", 46
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method inst3b", 46
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method inst4b", 46
                );
    }

    @Test
    public void testIncDec2() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public void inst1() { int i = 5; int j = i++; /*@ assert j == 5; */ }
                  public void inst1b() { int i = 5; int j = i++; /*@ assert j == 6; */ }
                  public void inst2() { int i = 5; int j = i--; /*@ assert j == 5; */ }
                  public void inst2b() { int i = 5; int j = i--; /*@ assert j == 4; */ }
                  public void inst3() { int i = 5; int j = ++i; /*@ assert j == 6; */ }
                  public void inst3b() { int i = 5; int j = ++i; /*@ assert j == 5; */ }
                  public void inst4() { int i = 5; int j = --i; /*@ assert j == 4; */ }
                  public void inst4b() { int i = 5; int j = --i; /*@ assert j == 5; */ }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1b", 54
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst2b", 54
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method inst3b", 54
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method inst4b", 54
                );
    }

    @Test
    public void testFieldsOK() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;/*@ nullable_by_default */
                public class TestJava {
                  int f; static int sf;
                  int g; static int sg;
                  public static TestJava t;  //@ public static invariant t != null;
                  public void inst2(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 2; */ }
                  public void inst2a(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 3; */ }
                  public void inst3(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */ }
                  public void inst3a(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 4; */ }
                  public void inst4(int/*@non_null*/[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 2; */ }
                  public void inst4a(int/*@non_null*/[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 4; */ }
                  public void inst5(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 4; */}
                  public void inst5a(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 5; */}
                  public void inst6(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f == b.f; */}
                  public void inst6a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f != b.f; */}
                  public void inst7(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 7; */}
                  public void inst7a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 8; */}
                  public void inst8(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf == b.sf; */}
                  public void inst8a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf != b.sf; */}
                  public void inst9(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 == b.sf; */}
                  public void inst9a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 != b.sf; */}
                  public void inst10(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a == this ==> a.f == f; */}
                  public void inst10a(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a.f == f; */}
                  public void inst11(/*@non_null*/TestJava a) { /*@ assert sf == this.sf; */ /*@ assert a.sf == sf; */}
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method inst2a", 75
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method inst3a", 84
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method inst4a", 84
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method inst5a", 118
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method inst6a", 85
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method inst7a", 103
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assert) in method inst8a", 78
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method inst9a", 88
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method inst10a", 81
                );
    }
    
    @Test
    public void testFieldsErr() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ writes this.*.*, this.*[*];
                    //@ writes this.*.*
                    public void m() {}
                }
                """
                ,"/tt/TestJava.java:3: error: Further selection is not permitted after a wild-card field", 22
                ,"/tt/TestJava.java:3: error: Further selection is not permitted after a wild-card field", 32
                ,"/tt/TestJava.java:4: error: Further selection is not permitted after a wild-card field", 22
                ,"/tt/TestJava.java:4: error: Invalid expression or missing semicolon here",24
                );
    }

    @Test
    public void testSwitch() {
        addOptions("--esc--max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  int f; static int sf;
                  int g; static int sg;
                  static TestJava t;
                  public void inst1a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j!=0; */ }
                  public void inst1b(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j==1; */ }
                  public void inst2(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert j>0; */ }
                  public void inst2a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert i==0 ==> j==-1; */ }
                  public void inst3(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }
                  public void inst3a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; break; case 2: j = 2; } /*@ assert j>0; */ }
                  public void inst4(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {} break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method inst1b", 148
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method inst2a", 141
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method inst3a", 170
                );
    }

    @Test
    public void testTry() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  static public int i;
                  //@ ensures i == 2;
                  public void inst1() { i=0; try { i = 1; return; } finally { i = 2; } }
                  //@ ensures i == 1;
                  public void inst1a() { i=0; try { i = 1; return; } finally { i = 2; } }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition) in method inst1a", 44
                ,"/tt/TestJava.java:6: verify: Associated declaration", 7
                );
    }

    @Test
    public void testTryWithMethodCall() {
        addOptions("--esc--max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava  {
                //@ public exceptional_behavior requires b;  signals (Exception e) true; signals (RuntimeException e) true;
                //@ also
                //@ public normal_behavior requires !b; ensures true;
                public static void ex(boolean b) throws RuntimeException {
                    if (b) throw new RuntimeException();
                }
                public static int sk; public int k;
                
                //@ requires k < 0;
                //@ ensures true;
                //@ also
                //@ requires k > 0;
                //@ ensures \\result == 1;
                public int m1() {
                    int i = 1;
                    try {
                        ex(true);
                        i = 1;
                    } catch (Exception e) {
                        //@ assert e != null;
                        i = 2;
                    }
                    return i;
                }
                
                //@ requires k < 0;
                //@ ensures true;
                //@ also
                //@ requires k > 0;
                //@ ensures \\result == 1;
                public int m2() {
                    int i = 1;
                    try {
                        ex(false);
                        i = 0;
                    } catch (Exception e) {
                        //@ assert e != null;
                        i = 1;
                    }
                    return i;
                }
                }
                """
                ,"/tt/TestJava.java:25: verify: The prover cannot establish an assertion (Postcondition) in method m1", 5
                ,"/tt/TestJava.java:15: verify: Associated declaration", 5
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (Postcondition) in method m2", 5
                ,"/tt/TestJava.java:32: verify: Associated declaration", 5
                );
    }

    @Test
    public void testMisc() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  static public int i;
                  //@ requires i > 0;
                  //@ ensures i > 0;
                  public static void m() { i = i -1; }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m", 22
                ,"/tt/TestJava.java:5: verify: Associated declaration", 7
                );
    }

    @Test
    public void testArith() { // TODO - need more arithmetic support
        Assume.assumeTrue(runLongTests);
        addOptions("-logic=AUFNIRA");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  public static void m1(int a, int b) { /*@ assert a*2 == a + a; */ }
                  public static void m3(int a, int b) { /*@ assert (2*a)/2 == a; */ }
                  public static void m4(int a, int b) { /*@ assert a >= 0 ==> (a%3) < 3; */ }
                  public static void m5(int a, int b) { /*@ assert a >= 0 ==> (a%3) >= 0; */ }
                  public static void m8(int a, int b) { /*@ assert (a >= 0 ) ==> ((5*a)%5) == 0; */ }
                }
                """
                );
        // +" public static void m2(int a, int b) { /*@ assert a * b ==
        // a *(b-1) + a; */ }\n"
        // +" public static void m6(int a, int b) { /*@ assert (a >= 0
        // && b > 0) ==> (a%b) >= 0; */ }\n"
        // +" public static void m7(int a, int b) { /*@ assert (a >= 0
        // && b > 0) ==> ((a*b)%b) == 0; */ }\n"
    }

    @Test
    public void testPureMethodStatic() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires i < 1000; ensures \\result == i+1;
                  //@ pure
                  public static int m(int i) { return i+1; }
                  public static void m1(int a, int b) { /*@ assume a < 100; */ int k = a+1; /*@ assert k == m(a); */ }
                  public static void m1a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(a); */ }
                  public static void m2(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }
                  public static void m2a(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }
                  public static void m3(int a, int b) { /*@ assume a < 100; */ int k = a+3; /*@ assert k == m(m(a+1)); */ }
                  public static void m3a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(m(a+1)); */ }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1a", 82
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2a", 84
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m3a", 82
                );
    }

    @Test
    public void testPureMethod() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                public class TestJava {
                  //@ requires i < 1000; ensures \\result == i+1;
                  //@ pure
                  public int m(int i) { return i+1; }
                  public void m1(int a, int b) { /*@ assume a < 100; */ int k = a+1; /*@ assert k == m(a); */ }
                  public void m1a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(a); */ }
                  public void m2(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }
                  public void m2a(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }
                  public void m3(int a, int b) { /*@ assume a < 100; */ int k = a+3; /*@ assert k == m(m(a+1)); */ }
                  public void m3a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(m(a+1)); */ }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1a", 75
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2a", 77
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m3a", 75
                );
    }

    @Test
    public void testPureNonFunction() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                /*@ code_bigint_math*/ public class TestJava {
                  public int z;
                  //@ ensures \\result == z+1;
                  //@ pure
                  public int m() { return z+1; }
                  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }
                  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }
                  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }
                  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }
                  public void m3(int a, int b) { z = 7; int k = z+1; /*@ assert k == m(); */ }
                  public void m3a(int a, int b) { z = 7; int k = z+2; /*@ assert k == m(); */ }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m1a", 52
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m2a", 54
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m3a", 59
                );
    }

    @Test
    public void testPureNoArguments() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                /*@ code_bigint_math*/ public class TestJava {
                  public static int z;
                  //@ ensures \\result == z+1;
                  //@ pure
                  public static int m() { return z+1; }
                  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }
                  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }
                  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }
                  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m1a", 52
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m2a", 54
                );
    }

    @Test
    public void testInheritedPost() {
        addOptions("-code-math=bigint","--check-feasibility=exit");
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                abstract class TestJavaA {
                
                  //@ ensures \\result > 0;
                  abstract public int m(int iii);
                }
                abstract class TestJavaB extends TestJavaA {
                  //@ also
                  //@ ensures \\result > ii;
                  abstract public int m(int ii);
                }
                /*@ code_bigint_math*/ public class TestJava extends TestJavaB {
                  //@ also public normal_behavior
                  //@ ensures \\result == i+1;
                  //@ pure
                  public int m(int i) { return i+1; }
                  //@ requires a >= 0;
                  //@ ensures \\result == a+1;
                  public int n1(int a) { return m(a); }
                  public int n1a(int a) { return m(-1); }
                }
                """
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m", 25
                ,"/tt/TestJava.java:4: verify: Associated declaration", 7
                ,"/tt/TestJava.java:20: verify: There is no feasible path to program point at program exit in method tt.TestJava.n1a(int)", 41
                );
    }

    @Test
    public void testInheritedPostA() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                abstract class TestJavaA {
                  //@ requires iii > 0;
                  //@ ensures \\result > 0;
                  abstract public int m(int iii);
                }
                abstract class TestJavaB extends TestJavaA {
                  //@ also
                  //@ ensures \\result > ii;
                  abstract public int m(int ii);
                }
                /*@ code_bigint_math*/ public class TestJava extends TestJavaB {
                  //@ also
                  //@ ensures \\result == i+1;
                  //@ pure
                  public int m(int i) { return i+1; }
                  //@ ensures \\result == a+1;
                  public int n1(int a) { return m(a); }
                  public int n1a(int a) { return m(-1); }
                }
                """
                );
    }

    @Test
    public void testInheritedPostB() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                abstract class TestJavaA {
                  //@ requires iii > 0;
                  //@ ensures \\result > 0;
                  abstract public int m(int iii);
                }
                abstract class TestJavaB extends TestJavaA {
                  //@ also
                  //@ requires ii > 0;
                  //@ ensures \\result > ii;
                  abstract public int m(int ii);
                }
                /*@ code_bigint_math*/ public class TestJava extends TestJavaB {
                  //@ also
                  //@ requires i > 0;
                  //@ ensures \\result == i+1;
                  //@ pure
                  public int m(int i) { return i+1; }
                }
                """
                );
    }

    @Test
    public void testInheritedPre() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                abstract class TestJavaA {
                  //@ requires iii == 1;
                  //@ ensures \\result == iii;
                  abstract public int m(int iii);
                }
                abstract class TestJavaB extends TestJavaA {
                  //@ also
                  //@ requires ii == 2;
                  //@ ensures \\result == ii;
                  abstract public int m(int ii);
                }
                /*@ code_bigint_math*/ public class TestJava extends TestJavaB {
                  //@ also
                  //@ requires i == 3;
                  //@ ensures \\result == i;
                  //@ pure
                  public int m(int i) { return i; }
                  //@ requires a >= 1 && a <= 3;
                  //@ ensures \\result == a;
                  public int m1(int a) { return m(a); }
                  //@ ensures \\result == a;
                  public int m1a(int a) { return m(-1); }
                }
                """
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Precondition) in method m1a", 35
                ,"/tt/TestJava.java:18: verify: Associated declaration", 14
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: iii == 1", 20
                ,"/tt/TestJava.java:9: verify: Precondition conjunct is false: ii == 2", 19
                ,"/tt/TestJava.java:15: verify: Precondition conjunct is false: i == 3", 18
                );
    }

    @Test
    public void testTrace() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires 0<=ii && ii <=3;
                  //@ ensures \\result < 0;
                  public static int m(int ii) {
                    if (ii==1) return -1;
                    if (ii==2) return -2;
                    if (ii==3) return -3;
                    ii = 7;
                    return 0; }
                  //@ requires ii == 2;
                  //@ ensures \\result == 0;
                  public static int mm(int ii) {
                    if (ii==1) return -1;
                    if (ii==2) return -2;
                    if (ii==3) return -3;
                    ii = 7;
                    return 0; }
                  public static int is;
                  //@ ensures is == 6;
                  public static int m3(int ii) {
                    try { ii = 0;
                      if (ii == 0) return -2;
                    } finally {
                      is = 7;
                    }    return 0; }
                  //@ ensures \\result == 1;
                  public static int m4(int ii) {
                    try { ii = 0;
                      if (ii == 0) return -2;
                    } finally {
                      is = 7;
                    }    return 0; }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method m", 5
                ,"/tt/TestJava.java:4: verify: Associated declaration", 7
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Postcondition) in method mm", 16
                ,"/tt/TestJava.java:12: verify: Associated declaration", 7
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Postcondition) in method m3", 20
                ,"/tt/TestJava.java:20: verify: Associated declaration", 7
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Postcondition) in method m4", 20
                ,"/tt/TestJava.java:27: verify: Associated declaration", 7
                );
    }

    @Test
    public void testForwardInit() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int m() {
                    int c = c+1;
                    //@ assert c == 1;
                    return c;
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: variable c might not have been initialized", 13
                );
    }

    @Test
    public void testGhostVars() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int m() {
                    int c = 4;
                    //@ ghost int d = c+1;
                    //@ assert d + c == 9;
                    return c;
                  }
                  public static int mm() {
                    int c = 4;
                    //@ ghost int d = c+1;
                    //@ assert d + c == 10;
                    return c;
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method mm", 9
                );
    }

    @Test
    public void testSet() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int m() {
                    int c = 4;
                    //@ ghost int d = c+1;
                    //@ set d = 10;
                    //@ assert d + c == 14;
                    return c;
                  }
                  public static int mm() {
                    int c = 4;
                    //@ ghost int d = c+1;
                    //@ set d = 10;
                    //@ assert d + c == 15;
                    return c;
                  }
                  public static int q() {
                    int c = 4;
                    //@ ghost int d = c+1;
                    //@ set   d = 10;
                    //@ assert d + c == 14;
                    return c;
                  }
                  public static int qq() {
                    int c = 4;
                    //@ ghost int d = c+1;
                    //@ set   d = 10;
                    //@ assert d + c == 15;
                    return c;
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method mm", 9
                ,"/tt/TestJava.java:28: verify: The prover cannot establish an assertion (Assert) in method qq", 9
                );
    }

    /**
     * Tests whether various ways of guarding a field reference are successful
     * in avoiding a failed assertion.
     */
    @Test
    public void testUndefinedInJava() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  int j;
                  public static void m0(TestJava o) {
                    int i = o.j;
                  }
                  public static void m1(/*@non_null*/ TestJava o) {
                    int i = o.j;
                  }
                  //@ requires o != null;
                  public static void m2(TestJava o) {
                    int i = o.j;
                  }
                  public static void m3(TestJava o) {
                    boolean i = o != null && o.j == 1;
                  }
                  public static void m4(TestJava o) {
                    boolean i = o == null || o.j == 1;
                  }
                  public static void m5(TestJava o) {
                    int i = ( o != null ? o.j : 6);
                  }
                  public static void m6(TestJava o) {
                    int i = ( o == null ? 7 : o.j);
                  }
                  public static void m6a(TestJava o) {
                    int i = ( o != null ? 7 : o.j);
                  }
                  //@ public normal_behavior  ensures \\result == (oo != null);
                  public static boolean p(TestJava oo) {
                    return oo != null;
                  }
                  public static void m7(TestJava o) {
                    boolean i = p(o) && o.j == 0;
                  }
                  public static void m7a(TestJava o) {
                    boolean i = p(o) || o.j == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m0", 14
                ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m6a", 32
                ,"/tt/TestJava.java:37: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m7a", 26
                );
    }

    /**
     * Tests whether various ways of guarding a method call are successful in
     * avoiding a failed assertion.
     */
    @Test
    public void testUndefinedMInJava() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  int j;
                  public static void m0(TestJava o) {
                    int i = o.z();
                  }
                  public static void m1(/*@non_null*/ TestJava o) {
                    int i = o.z();
                  }
                  //@ requires o != null;
                  public static void m2(TestJava o) {
                    int i = o.z();
                  }
                  public static void m3(TestJava o) {
                    boolean i = o != null && o.z() == 1;
                  }
                  public static void m4(TestJava o) {
                    boolean i = o == null || o.z() == 1;
                  }
                  public static void m5(TestJava o) {
                    int i = ( o != null ? o.z() : 6);
                  }
                  public static void m6(TestJava o) {
                    int i = ( o == null ? 7 : o.z());
                  }
                  public static void m6a(TestJava o) {
                    int i = ( o != null ? 7 : o.z());
                  }
                  //@ public normal_behavior  ensures \\result == (oo != null);
                  public static boolean p(TestJava oo) {
                    return oo != null;
                  }
                  public static void m7(TestJava o) {
                    boolean i = p(o) && o.z() == 0;
                  }
                  public static void m7a(TestJava o) {
                    boolean i = p(o) || o.z() == 0;
                  }
                  //@ signals_only \\nothing;
                 public int z() { return 0; }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m0", 14
                ,"/tt/TestJava.java:27: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m6a", 32
                ,"/tt/TestJava.java:37: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m7a", 26
                );
    }

    /**
     * Tests whether various ways of guarding a method call are successful in
     * avoiding a failed assertion.
     */
    @Test
    public void testUndefinedSMInJava() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int j;
                  public static void m0(TestJava o) {
                    int i = o.z();
                  }
                  public static void m1(/*@non_null*/ TestJava o) {
                    int i = o.z();
                  }
                  //@ requires o != null;
                  public static void m2(TestJava o) {
                    int i = o.z();
                  }
                  public static void m3(TestJava o) {
                    boolean i = o != null && o.z() == 1;
                  }
                  public static void m4(TestJava o) {
                    boolean i = o == null || o.z() == 1;
                  }
                  public static void m5(TestJava o) {
                    int i = ( o != null ? o.z() : 6);
                  }
                  public static void m6(TestJava o) {
                    int i = ( o == null ? 7 : o.z());
                  }
                  public static void m6a(TestJava o) {
                    int i = ( o != null ? 7 : o.z());
                  }
                  //@ public normal_behavior  ensures \\result == (oo != null);
                  public static boolean p(TestJava oo) {
                    return oo != null;
                  }
                  public static void m7(TestJava o) {
                    boolean i = p(o) && o.z() == 0;
                  }
                  public static void m7a(TestJava o) {
                    boolean i = p(o) || o.z() == 0;
                  }
                  //@ signals_only \\nothing;
                 public static int z() { return 0; }
                }
                """
                );
    }

    /**
     * Tests whether the various kinds of undefined constructs are actually
     * detected.
     */
    @Test
    public void testUndefinedInJava2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ /*@ code_java_math spec_java_math*/ public class TestJava {
                  int j;
                  public static void m(TestJava o) {
                    int i = o.j;
                  }
                    public static void m1(int[] a) {
                    int i = a[0];
                  }
                  //@ requires a != null;
                  public static void m2(int[] a) {
                    int i = a[-1];
                  }
                  //@ requires a != null;
                  public static void m3(int[] a) {
                    //@ assume a.length == 1;
                    int i = a[1];
                  }
                  public static void m4(int i, int j) {
                    int k = i/j;
                  }
                  public static void m5(int i, int j) {
                    int k = i%j;
                  }
                  public static void m6( RuntimeException r) {
                    Throwable t = r;
                    Exception rr = ((Exception)t);
                  }
                  public static void m6a(Exception r) {
                    Throwable t = r;
                    RuntimeException rr = ((RuntimeException)t) ;
                  }
                  public static void m7(/*@ non_null*/ RuntimeException r) {
                    Throwable t = r;
                    Exception rr = ((Exception)t);
                  }
                  public static void m7a(/*@ non_null*/Exception r) {
                    Throwable t = r;
                    RuntimeException rr = ((RuntimeException)t) ;
                  }
                }
                """
                ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m", 14,
                        anyorder(
                                seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",
                                        14),
                                seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",
                                        14)),
                        "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2", 14,
                        "/tt/TestJava.java:17: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3", 14,
                        "/tt/TestJava.java:20: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4",
                        14,
                        "/tt/TestJava.java:23: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m5",
                        14,
                        "/tt/TestJava.java:31: verify: The prover cannot establish an assertion (PossiblyBadCast) in method m6a: a Throwable cannot be proved to be a RuntimeException",
                        28,
                        "/tt/TestJava.java:39: verify: The prover cannot establish an assertion (PossiblyBadCast) in method m7a: a Throwable cannot be proved to be a RuntimeException",
                        28)
                );
    }

    /**
     * Tests whether various ways of guarding a field reference are successful
     * in avoiding a failed assertion.
     */
    @Test
    public void testUndefinedInSpec() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  int j;
                  public static void m(TestJava o) {
                    //@ assume o.j == 1;
                  }
                  public static void m1(/*@non_null*/ TestJava o) {
                    //@ assume o.j == 1;
                  }
                  //@ requires o != null;
                  public static void m2(TestJava o) {
                    //@ assume o.j == 1;
                  }
                  public static void m3(TestJava o) {
                    //@ assume o != null && o.j == 1;
                  }
                  public static void m4(TestJava o) {
                    //@ assume o == null || o.j == 1;
                  }
                  public static void m5(TestJava o) {
                    //@ assume o != null ==> o.j == 1;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m", 17
                );
    }

    // FIXME - problem with types
    /**
     * Tests whether the various kinds of undefined constructs are actually
     * detected.
     */ // TODO - need pure method violating preconditions, bad array element
        // assignment
    @Test
    public void testUndefinedInSpec2() {
        //addOptions("-logic=AUFNIA");
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  int j;
                  public static void m(TestJava o) {
                    //@ assume o.j == 1;
                  }
                    public static void m1(int[] a) {
                    //@ assume a[0] == 1;
                  }
                  //@ requires a != null;
                  public static void m2(int[] a) {
                    //@ assume a[-1] == 1;
                  }
                  //@ requires a != null;
                  public static void m3(int[] a) {
                    //@ assume a.length == 1;
                    //@ assume a[1] == 1;
                  }
                  public static void m4(int i, int j) {
                    //@ assume i/j == 4;
                  }
                  public static void m5(int i, int j) {
                    //@ assume i%j == 4;
                  }
                  public static void m6(RuntimeException r) {
                    Throwable t = r;
                    //@ assume ((Exception)t) != null ? true : true;
                  }
                  public static void m6a(Exception r) {
                    Throwable t = r;
                    //@ assume ((RuntimeException)t) != null ? true : true ;
                  }
                  public static void m7(/*@ non_null*/RuntimeException r) {
                    Throwable t = r;
                    //@ assume ((Exception)t) != null ? true : true;
                  }
                  public static void m7a(/*@ non_null*/Exception r) {
                    Throwable t = r;
                    //@ assume ((RuntimeException)t) != null ? true : true ;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m", 17
                ,anyorder(
                        seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1",
                                17),
                        seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",
                                17))
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m2", 17
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3", 17
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4", 17
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5", 17
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (UndefinedBadCast) in method m6a: a Throwable cannot be proved to be a RuntimeException", 17
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (UndefinedBadCast) in method m7a: a Throwable cannot be proved to be a RuntimeException", 17
                );
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - loop invariants, variants, represents, signals, modifies
    // TODO - old constructs, quantifications, set comprehension, pure methods -
    // check other JMl expressions
    @Test
    public void testUndefinedInSpec3() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.annotation.*;
                /*@ nullable_by_default */ public class TestJava {
                  public int j = 1;
                  public static @Nullable TestJava t;
                  public static void m(TestJava o) {
                    //@ assume o.j == 1;  // ERROR
                  }
                    public static void m1(TestJava o) {
                    //@ assert o.j == 1 ? true : true; // ERROR
                  }
                    public static void m2(TestJava o) {
                    //@ ghost int i = o.j;  // ERROR
                  }
                    public static void m3(TestJava o) {
                    //@ ghost int i; set   i = o.j;  // ERROR
                  }
                    //@ requires o.j == 1;          // ERROR
                  public static void m4(@Nullable TestJava o) {
                  }
                    //@ ensures t.j == 1 ? true : true;  // ERROR
                  public static void m5(TestJava o) {
                  }
                    public static void m6(TestJava o) { // ERROR
                    //@ ghost int i; set i = o.j;
                  }
                  }
                """    // FIXME - all of these should be PossiblylNullDereference
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m", 17
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1", 17
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m2", 24
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m3", 33
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m4", 19
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m5", 18
                ,"/tt/TestJava.java:22: verify: Associated method exit", 4
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m6", 31
                );
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - readable writable, represents, assert, other clauses
    @Test
    public void testUndefinedInSpec4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  int j = 1;
                  static TestJava t;
                  public void m(TestJava o) {
                    //@ assume o.j == 1;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m", 17
                );
    }

    @Test
    public void testUndefinedInSpec4d() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  public int j = 1;
                  public static TestJava t;
                  public void m(TestJava o) {
                  }
                  //@ public invariant t.j ==1 ? true: true;
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method TestJava", 25
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m", 25
                );
    }

    /** Check to catch undefinedness in an initially clause */
    @Test
    public void testUndefinedInSpec4a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  public boolean j = true;
                  static TestJava t;
                  public TestJava() {
                  }
                  //@ public initially t.j ? true : true;
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method TestJava", 25
                );
    }

    /** Check to catch undefinedness in a constraint clause */
    @Test
    public void testUndefinedInSpec4b() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  public int j = 1;
                  public static TestJava t;
                  public void m(TestJava o) {
                  }
                    //@ public constraint t.j ==1 ? true: true;
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m", 28
                );
    }

    /** Check to catch undefinedness in a axiom clause */
    @Test
    public void testUndefinedInSpec4c() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int j = 1;
                  public static TestJava t;
                  public void m(TestJava o) {
                  }
                    // @ axiom (\\forall TestJava q;; q.j ==1); // FIXME
                }
                """
                );
    }

    @Test
    public void testUndefinedInSpec5() {
        addOptions("--nullable-by-default", "--no-checkAccessible");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static TestJava t;
                  int j = t.j;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method TestJava", 12
                );
    }

    @Test
    public void testUndefinedInJava6() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  static TestJava t;
                  int j = 1;
                  public void m1(TestJava o) {
                    int i = t.j;
                  }
                    public void m2(TestJava o) {
                    t.j = 1;
                  }
                    public void m3(TestJava o) {
                    t.j += 1;
                  }
                    public void m4(TestJava o) {
                    int i = 0; i += t.j;
                  }
                    public void m5(TestJava o) {
                    assert t.j == 1 ? true : true;
                  }
                  }
                """
                // TODO for, while, foreach, do, switch, case, if,
                // throw, method call, index, conditional,
                // annotation, binary, unary, conditional, new array,
                // new class, return, synchronized
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1", 14
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2", 6
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3", 6
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4", 22
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m5", 13
                );
    }

    // TODO - need tests within various Java constructs, including with
    // short-circuits

    /** This test tests catch blocks */
    @Test
    public void testCatch() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    int i = 0;
                    try {
                      throw new RuntimeException();
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    }
                    //@ assert i == 1;
                  }
                  public void ma() {
                    int i = 0;
                    try {
                      throw new RuntimeException();
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    }
                    //@ assert i == 2;
                  }
                }
                """
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method ma", 9
                );
    }

    @Test
    public void testCatch2() {
        addOptions("-method=ma");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void mx() {
                    int i = 0;
                    try {
                      throw new Exception();
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    }
                    //@ assert i == 2;
                  }
                  public void mp() {
                    int i = 0; int j = 0;
                    try {
                      throw new Exception();
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    } finally {
                      j=3;
                    }
                    //@ assert i == 2 && j == 3;
                  }
                  public void ma() {
                    int i = 0;
                    try {
                      throw new Exception();
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    }
                    //@ assert i == 1;
                  }
                  public void m1(int k) {
                    int i = 0; int j = 0; //@ assume k == 0;
                    try {
                      try {
                         if (k == 0) throw new Exception();
                      } finally {
                         j = 50;
                      }
                      j = 60;
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    }
                    //@ assert i == 2 && j == 50;
                  }
                  public void m11(int k) throws Exception {
                    int i = 0; int j = 0; //@ assume k == 0;
                    try {
                    try {
                      try {
                         if (k == 0) throw new Exception();
                      } finally {
                         j = 50;
                      }
                      j = 60;
                    } catch (RuntimeException e) {
                      i=1;
                    } finally {
                      i=2;
                    }
                    } finally {
                    //@ assert i == 2 && j == 50;
                    }
                  }
                  public void m2() {
                    int i = 20;
                    try {
                      i=10;
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    }
                    i = 0;
                    //@ assert i == 0;
                  }
                  public void m3() {
                    int i = 20;
                    try {
                      i=10;
                    } catch (RuntimeException e) {
                      i=1;
                    } catch (Exception e) {
                      i=2;
                    } finally {
                      i = 0;
                    }
                    //@ assert i == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Assert) in method ma", 9
                );
        // FIXME - enventually rejuvenate dead branch detection
        // ,"/tt/TestJava.java:42: verify: else branch apparently never taken
        // in method tt.TestJava.m1(int)",14
        // ,"/tt/TestJava.java:59: verify: else branch apparently never taken
        // in method tt.TestJava.m11(int)",14
    }

    @Test
    public void testCatch3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  //@ public normal_behavior
                  //@   requires i != 1 & i != 2;
                  //@   ensures \\result == 0;
                  //@ also public exceptional_behavior
                  //@   requires i == 2 && ee != null;
                  //@   signals (ArrayIndexOutOfBoundsException ex) true;
                  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {
                    try {
                      if (i == 1) throw e;
                      if (i == 2) throw ee;
                      return 0;
                    } catch (NullPointerException exx) {
                      throw ae;
                    }
                  }
                }
                """
                );
    }


    @Test
    public void testCatch3a() {
        helpEsc("tt.TestJava",
                """
                package tt; //@ non_null_by_default
                public class TestJava  {
                  //@ public normal_behavior
                  //@   requires i != 1 & i != 2;
                  //@   ensures \\result == 0;
                  //@ also public exceptional_behavior
                  //@   requires i == 2;
                  //@   signals (ArrayIndexOutOfBoundsException ex) true;
                  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {
                    try {
                      if (i == 1) throw e;
                      if (i == 2) throw ee;
                      return 0;
                    } catch (NullPointerException exx) {
                      throw ae;
                    }
                  }
                }
                """
                );
    }

    @Test
    public void testCatch4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  //@ public normal_behavior
                  //@   requires e != null & ee != null & ae != null;
                  //@   requires i != 1 & i != 2;
                  //@   ensures \\result == 0;
                  //@ also public exceptional_behavior
                  //@   requires e != null & ee != null & ae != null;
                  //@   requires i == 2;
                  //@   signals (ArrayIndexOutOfBoundsException ex) true;
                  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {
                    try {
                      if (i == 1) throw e;
                      if (i == 2) throw ee;
                      return 0;
                    } catch (NullPointerException exx) {
                      throw ae;
                    }
                  }
                }
                """
                );
    }

    @Test
    public void testTypes() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(/*@non_null*/Object o) {
                    //@ assume \\typeof(o) == \\type(Object);
                    //@ check \\typeof(o) == \\typeof(o);
                    //@ check \\typeof(o) == \\type(Object);
                    //@ check !(\\typeof(o) <: \\type(Object));
                    //@ check \\typeof(o) <:= \\type(Object);
                  }
                  public void m1a(/*@non_null*/Object o) {
                    //@ assume \\typeof(o) == \\type(Object);
                    //@ check \\typeof(o) != \\type(Object);
                  }
                  public void m2(/*@non_null*/Object o) {
                    //@ assume \\typeof(o) == \\type(Object);
                    //@ check \\typeof(o) == \\type(Object);
                  }
                  public void m2a(/*@non_null*/Object o) {
                    //@ assume \\typeof(o) == \\type(Object);
                    //@ check \\typeof(o) == \\type(TestJava);
                  }
                  public void m3(/*@non_null*/Object o) {
                    //@ assume \\typeof(o) == \\type(Object);
                    //@ check \\type(TestJava) <: \\typeof(o);
                    //@ check \\type(TestJava) <:= \\typeof(o);
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m1a", 9
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (Assert) in method m2a", 9
                );
    }

    @Test
    public void testTypes2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(/*@non_null*/TestJava o) {
                    //@ assume \\typeof(o) == \\type(TestJava);
                    //@ assert \\typeof(o) <:= \\type(Object);
                  }
                  public void m2(/*@non_null*/TestJava o) {
                    //@ assert \\typeof(o) <:= \\type(Object);
                  }
                }
                """
                );
    }

    @Test
    public void testTypes3() {
        helpEsc("tt.TestJava",
                """
                package tt; import org.jmlspecs.lang.JML;
                public class TestJava {
                  public void m1(/*@non_null*/Object o) {
                    //@ assert JML.erasure(\\typeof(o)) == o.getClass();
                  }
                }
                """
                );
    }

    @Test
    public void testSignals1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ requires i >= 0;
                  //@ ensures i>0;
                  //@ signals (Exception e) i == 0;
                  public void m1() throws Exception {
                    if (i==0) throw new Exception();
                  }
                  //@ requires i >= 0;
                  //@ ensures i>0;
                  //@ signals (Exception e) i == 1;
                  public void m1a() throws Exception {
                    if (i==0) throw new Exception();
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1a", 15
                ,"/tt/TestJava.java:12: verify: Associated declaration", 7
                );
    }

    @Test
    public void testSignals2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ requires i >= 0;
                  //@ ensures i>0;
                  //@ signals (Exception e) i == 0;
                  public void m2() throws Exception {
                    if (i==0) throw new Exception();
                  }
                  //@ requires i >= 0;
                  //@ ensures i>0;
                  //@ signals (RuntimeException e) i == 1;
                  public void m2a() throws Exception {
                    if (i==0) throw new RuntimeException();
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2a", 15
                ,"/tt/TestJava.java:12: verify: Associated declaration", 7
                );
    }

    @Test
    public void testSignals3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ requires i >= 0;
                  //@ ensures i>0;
                  //@ signals (Exception e) i == 0;
                  public void m3() throws RuntimeException {
                    if (i==0) throw new RuntimeException();
                  }
                  //@ requires i >= 0;
                  //@ ensures i>0;
                  //@ signals (Exception e) i == 1;
                  public void m3a() throws RuntimeException {
                    if (i==0) throw new RuntimeException();
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a", 15
                ,"/tt/TestJava.java:12: verify: Associated declaration", 7
                );
    }

    @Test
    public void testSignals4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ requires i >= 0;
                  //@ ensures i>0;
                  //@ signals (RuntimeException e) i == 1;
                  public void m4() throws Exception {
                    if (i==0) throw new Exception();
                  }
                }
                """
                );
    }

    @Test
    public void testSignalsOnly() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int i;
                  //@ signals_only java.io.IOException;
                  public void m1a() throws Exception {
                    if (i==0) throw new Exception();
                  }
                  //@ signals_only \\nothing;
                  public void m2a() {
                    if (i==0) throw new RuntimeException();
                  }
                  //@ signals_only Exception;
                  public void m3() {
                    if (i==0) throw new RuntimeException();
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (ExceptionList) in method m1a", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 7
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (ExceptionList) in method m2a", 15
                ,"/tt/TestJava.java:8: verify: Associated declaration", 7
                );
    }

    @Test
    public void testConstraint() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for m1();
                  public void m1() {
                  }
                  public void m2() {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                );
    }

    @Test
    public void testConstraint2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for ! m1();
                  public void m1() {
                  }
                  public void m2() {
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                );
    }

    @Test
    public void testConstraint3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for \\everything;
                  public void m1() {
                  }
                  public void m2() {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                );
    }

    @Test
    public void testConstraint3a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for !\\nothing;
                  public void m1() {
                  }
                  public void m2() {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                );
    }

    @Test
    public void testConstraint4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for \\nothing;
                  public void m1() {
                  }
                  public void m2() {
                  }
                }
                """
                );
    }

    @Test
    public void testConstraint4a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for !\\everything;
                  public void m1() {
                  }
                  public void m2() {
                  }
                }
                """
                );
    }

    @Test
    public void testConstraint6() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i);
                  public void m1() {
                  }
                  public void m2() {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                );
    }

    @Test
    public void testConstraint7() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for m1(), m1(int);
                  public void m1() {
                  }
                  public void m1(int j) {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m1", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 14
                );
    }

    @Test
    public void testConstraint7a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for m1(), m1(int);
                  public static void m1() {
                  }
                  public static void m1(int j) {
                  }
                }
                """
                );
    }

    @Test
    public void testConstraint8() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for ! m1(), m1(int);
                  public void m1() {
                  }
                  public void m1(int j) {
                  }
                }
                """
                );
    }

    @Test
    public void testConstraint9() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i) for TestJava();
                  public TestJava() {
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: Constructors are not allowed as methods in non-static constraint clauses", 41
                );
    }

    @Test
    public void testConstraint9a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public constraint i > \\old(i);
                  public TestJava() {
                  }
                }
                """
                );
    }

    @Test
    public void testConstraint10() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public static constraint i > \\old(i) for TestJava();
                  public TestJava() {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method TestJava", 10
                ,"/tt/TestJava.java:4: verify: Associated declaration", 21
                );
    }

    @Test
    public void testConstraint10a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  //@ public static constraint i > \\old(i);
                  public TestJava() {
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method TestJava", 10
                ,"/tt/TestJava.java:4: verify: Associated declaration", 21
                );
    }

    @Test
    public void testConstraint11() {
        helpEsc("tt.TestJava",
                """
                package tt;
                interface A {
                  //@ ghost static public int i = 0;
                  //@ public static constraint i > \\old(i);
                }
                public class TestJava implements A {
                   public TestJava() {
                   }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method TestJava", 11
                ,"/tt/TestJava.java:4: verify: Associated declaration", 21
                );
    }

    @Test
    public void testConstraint11a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                interface A {
                  //@ ghost static public int i = 0;
                  //@ public constraint i > \\old(i);
                }
                public class TestJava implements A {
                  public TestJava() {
                  }
                }
                """
                );
    }

    @Test
    public void testConstraint12() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                   public int i;
                   public int j;
                   //@ public constraint i > \\old(i) for m;
                   public void m() {
                   }
                   public void q() {
                   }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Constraint) in method m", 16
                ,"/tt/TestJava.java:5: verify: Associated declaration", 15
                );
    }

    @Test
    public void testConstraint12a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                   public int i;
                   public int j;
                   //@ public constraint j > \\old(j) for ! m;
                   public void m() {
                   }
                   public void q() {
                   }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Constraint) in method q", 16
                ,"/tt/TestJava.java:5: verify: Associated declaration", 15
                );
    }
    
    // FIXME - test duplicate matches for signatures; no matches; sigs with type names

    @Test // FIXME - for reasons unknown, this test appears to be
            // non-deterministic - sometimes succeeding sometimes failing
    public void testMethodAxioms() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (i > 0 && i < 10);
                  //@ pure
                  //@ model public boolean m(int i);
                  public void mm() {
                  //@ check (\\forall int k; 3<k && k <7; m(k));
                  //@ check (\\forall int k; 3<k && k <7; m(k-1));
                  //@ check !(\\forall int k; -3<k && k <7; m(k));
                  }
                }
                """
                );
    }

    @Test
    public void testMethodAxioms2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (0 < i < 10);
                  //@ no_state
                  //@ model public static boolean m(int i);
                  //@ pure
                  public void mm() {  //@ assert !m(10);
                  //@ assert !(\\forall int k; 3 < k < 11; m(k));
                  }
                }
                """
                );
    }

    @Test
    public void testMethodAxioms2a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (0 < i < 10);
                  //@ pure
                  //@ model public boolean m(int i);
                  //@ pure
                  public void mm() {
                  //@ assert (\\forall int k; 3 < k < 11; m(k));
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method mm", 7
                );
    }

    @Test
    public void testMethodAxioms2b() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  //@ normal_behavior
                  //@ ensures \\result == (0 < i < 10);
                  //@ pure
                  //@ model public boolean m(int i);
                  //@ pure
                  public void mm() {
                  //@ assert (\\forall int k; 3 < k < 10; m(k));
                  }
                }
                """
                );
    }

    @Test 
    public void testNullityAndConstructors() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  private /*@ spec_public */ char[] o;
                
                  //@ assignable \\everything;
                   public TestJava(final char /*@ non_null */ [] the_array) {
                      o = new char[the_array.length];
                  }
                }
                """
                );
    }

    @Test
    public void testNullityAndConstructors2() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  private /*@ spec_public */ char[] o;
                
                  //@ assignable \\everything;
                   public TestJava(final char  /*@ non_null */[] the_array) {
                      o = new char[the_array.length]; //@ assert o != null;
                  //@ show the_array instanceof char[], o instanceof char[], the_array.length;
                      System.arraycopy(the_array, 0, o, 0, the_array.length);
                  }
                }
                """
                );
    }

    @Test 
    public void testNullityAndConstructors3() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  private /*@ spec_public */ char[] o;
                  private /*@ spec_public */ int[] oo;
                
                  //@ assignable \\everything;
                   public TestJava(final char /*@ non_null */ [] the_array) {
                      o = the_array;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (NullField) in method TestJava", 36
                );
    }

    @Test
    public void testArrayLength() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public void m(final byte[] array) {
                      //@ assert array.length >= 0;
                      //@ assert array.length <= Integer.MAX_VALUE;
                  }
                }
                """
                );
    }

    @Test
    public void testArrayLength2() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  //@ requires k >= 0;
                  public void m(int k) {
                      short[] array = new short[k];
                      //@ assert array.length >= 0;
                      //@ assert array.length <= Integer.MAX_VALUE;
                      //@ assert array.length == k;
                  }
                }
                """
                );
    }

    @Test
    public void testArrayLength3() {
        addOptions("--nonnull-by-default","--method=m");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  long[] array;
                  public void m() {
                      //@ assert array.length >= 0;
                      //@ assert array.length <= Integer.MAX_VALUE;
                  }
                }
                """
                );
    }

    @Test
    public void testArrayLength4() {
        addOptions("--nonnull-by-default","--method=m");
        helpEsc("tt.TestJava",
                """
                package tt;
                public abstract class TestJava  {
                  public void m() {
                      char[] array = mm();
                      //@ assert array.length >= 0;
                      //@ assert array.length <= Integer.MAX_VALUE;
                  }
                  public abstract char[] mm();
                }
                """
                );
    }

    @Test
    public void testVarargs() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public abstract class TestJava  {
                  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);
                  public void mm(int... args) {  }
                  public void m0() {
                      mm();
                  }
                  public void m1() {
                      mm(1);
                  }
                  public void m1b() {
                      mm(-1);
                  }
                  public void m2() {
                      mm(1,2);
                  }
                  public void m2b() {
                      mm(-1,2);
                  }
                  public void m3() {
                      mm(new int[]{1,2});
                  }
                  public void m3b() {
                      mm(new int[]{1,-2});
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                );
    }

    @Test
    public void testVarargsX() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public abstract class TestJava  {
                  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0); requires n == -2;
                  public void mm(int n, int... args) {  }
                  public void m0() {
                      mm(-2);
                  }
                  public void m1() {
                      mm(-2,1);
                  }
                  public void m1b() {
                      mm(-2,-1);
                  }
                  public void m2() {
                      mm(-2,1,2);
                  }
                  public void m2b() {
                      mm(-2,-1,2);
                  }
                  public void m3() {
                      mm(-2,new int[]{1,2});
                  }
                  public void m3b() {
                      mm(-2,new int[]{1,-2});
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                );
    }

    @Test
    public void testVarargs2() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public abstract class TestJava  {
                  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);
                  public void mm(Integer... args) {  }
                  public void m0() {
                      mm();
                  }
                  public void m1() {
                      mm(1);
                  }
                  public void m1b() {
                      mm(-1);
                  }
                  public void m2() {
                      mm(1,2);
                  }
                  public void m2b() {
                      mm(-1,2);
                  }
                  public void m3() {
                      mm(new Integer[]{1,2});
                  }
                  public void m3b() {
                      mm(new Integer[]{1,-2});
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                );
    }

    @Test
    public void testVarargs2X() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public abstract class TestJava  {
                  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);      requires n == -2;
                  public void mm(int n, Integer... args) {  }
                  public void m0() {
                      mm(-2);
                  }
                  public void m1() {
                      mm(-2,1);
                  }
                  public void m1b() {
                      mm(-2,-1);
                  }
                  public void m2() {
                      mm(-2,1,2);
                  }
                  public void m2b() {
                      mm(-2,-1,2);
                  }
                  public void m3() {
                      mm(-2,new Integer[]{1,2});
                  }
                  public void m3b() {
                      mm(-2,new Integer[]{1,-2});
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b", 9
                ,"/tt/TestJava.java:4: verify: Associated declaration", 15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)", 16
                );
    }

    @Test // Incorrect syntax for \lbl produced an exception, but I could not reproduce that behavior here
    public void testLblError() {
        expectedExit = 1;
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public abstract class TestJava  {
                  public void m0(int i, int j) {
                      //@ assert (\\lbl I i) + \\lbl(J j) == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:4: error: Missing comma or right parenthesis or otherwise ill-formed expression", 38
                );
    }

    @Test // This test has lots of solutions, hence the precondition
    public void testNewLblSyntax() {
        expectedExit = 0;
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                """
                package tt;
                public abstract class TestJava {
                  //@ requires i == 1;
                  public void m0(int i, int j) {
                      //@ assert (\\lbl I i) + \\lbl(J,j) != 0;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: Label I has value 1",24
                ,"/tt/TestJava.java:5: verify: Label J has value ( - 1 )",36
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Assert) in method m0",11
                );
    }

    @Test
    public void testExitInfo2() {
        expectedExit = 0;
        addOptions("--esc-max-warnings=10");
        helpEsc("tt.TestJava",
                        """
                        package tt; //@ nullable_by_default
                        public class TestJava  {
                          /*@ requires o != null;
                              ensures \\result == (j>=0);
                             spec_pure */ public static boolean positive(Object o, int j) {
                                 return j >= 0; }
                          public int j;
                          //@ signals (NullPointerException e) positive(null,j);
                          //@ signals (NegativeArraySizeException e) positive(null,j);
                          public void m0(int i, Object o) {
                              if (i == 1) { j = -2; throw new NullPointerException(); }
                              if (i == 2) { j = -1; throw new NegativeArraySizeException(); }
                          }
                        }
                        """
                ,anyorder(seq(
                 "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m0",54
                ,"/tt/TestJava.java:5: verify: Associated declaration",41
                ,"/tt/TestJava.java:12: verify: Associated method exit",29
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: o != null",18
                ),seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (UndefinedCalledMethodPrecondition) in method m0",48
                ,"/tt/TestJava.java:5: verify: Associated declaration",41
                ,"/tt/TestJava.java:11: verify: Associated method exit",29
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: o != null",18
                ))
                );
    }

    @Test
    public void testExitInfo() {
        expectedExit = 0;
        addOptions("--esc-max-warnings=3");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int j;
                  //@ ensures j >= 0;
                  public void m0(int i, Object o) {
                      j = -1;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition) in method m0", 15
                ,"/tt/TestJava.java:4: verify: Associated declaration", 7
                );
    }

    @Test
    public void testFinalInvariant2() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static final int ii = mm();
                 //@ ensures ii == 19; static_initializer   //@ public final invariant ii == 19;
                  //@ public normal_behavior ensures \\result == 10 + 9; pure
                  public static int mm() { return 19; }  //@ public normal_behavior ensures \\result == 19; pure
                  public int mmm() { return ii; }}
                """
                );
    }

    @Test
    public void testFinalInvariant1() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static final int jj = 21;
                  public static final int ii = mm();
                 //@ ensures ii == 19 && jj == 21; static_initializer   //@ public final invariant ii == 19;
                  //@ public normal_behavior ensures \\result == 10 + 9; pure
                  public static int mm() { return 19; }  //@ public normal_behavior ensures \\result == 21; pure
                  public int mmm() { return jj; }}
                """
                );
    }


    @Test
    public void testFinalInvariant3() { 
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static final int ii = mm();
                 //@ ensures ii == mm(); static_initializer   //@ public final invariant ii == 19;
                  //@ public normal_behavior ensures \\result == 10 + 9; pure
                  public static int mm() { return 19; }  //@ public normal_behavior ensures \\result == 19; pure
                  public int mmm() { return ii; }}
                """
                );
    }

    @Test
    public void testFinalInvariant() { // FIXME - determine why this works without the commented out errors
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static final int ii = mm();
                  //@ public final invariant ii == 19;
                  //@ public normal_behavior ensures \\result == 10 + 9; pure
                  public static int mm() { return 19; }}
                """
                ,"/tt/TestJava.java:3: warning: Use a static_initializer clause to specify the values of static final fields: tt.TestJava.ii (translating tt.TestJava.TestJava())", 27
                ,"/tt/TestJava.java:3: warning: Use a static_initializer clause to specify the values of static final fields: tt.TestJava.ii (translating tt.TestJava.mm())", 27
//              ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (InvariantExit) in method TestJava",8
//              ,"/tt/TestJava.java:4: verify: Associated declaration",20
                );
    }

    @Test
    public void testEnumStaticInitializer() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public enum TestJava  {
                    A(1), B(2), C(3);   private TestJava(int i) {bit = i; }
                    private int bit;
                    static /*@ spec_public */ private int num = 10;
                  //@ public normal_behavior
                  //@   ensures num == 10;
                  //@   ensures A.bit == 1;
                  //@   ensures B.bit == 2;
                  //@ static_initializer
                  public void m() {}}
                """
                ,"/tt/TestJava.java:8: error: An identifier with private visibility may not be used in a ensures clause with public visibility", 18
                ,"/tt/TestJava.java:9: error: An identifier with private visibility may not be used in a ensures clause with public visibility", 18
                );
    }

    @Test
    public void testEnumStaticInitializer2() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                """
                package tt;
                public enum TestJava  {
                    A(1), B(2), C(3);   private TestJava(int i) {bit = i; }
                    /*@ spec_public */ private int bit;
                    static /*@ spec_public */ private int num = 10;
                  //@ public normal_behavior
                  //@   ensures num == 10;
                  //@   ensures A.bit == 1;
                  //@   ensures B.bit == 2;
                  //@ static_initializer
                  public void m() {}}
                """
                );
    }
    
    @Test
    public void testNonNullElements() {
        expectedExit = 0;
        addOptions("-code-math=bigint");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static class Key { public int k; }
                  //@ public normal_behavior
                  //@   requires \\nonnullelements(arr);
                  public static void m( Key... arr) {
                     int s = 0;
                     for (Key i: arr) {
                        s = s + i.k;
                     }
                  }
                }
                """
                );
    }

    @Test // tests show statement; watch out for nondeterministic behavior
    public void testShowStatementESC() {
        expectedExit = 0;
        addOptions("--code-math=java","--method=m","--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static class Key { public int k; }
                  //@ public normal_behavior
                  //@   requires i <= 1 && j >= 0;
                  public static void m(int i, int j) {
                     //@ show i, j+1;
                     int k = i+j;
                     //@ show k;
                     //@ assert k > 0;
                     int m = i-j;
                     //@ show m,k;
                     //@ assert m >= 0;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: Show statement expression i has value 0", 15
                ,"/tt/TestJava.java:7: verify: Show statement expression j + 1 has value 2", 18
                ,"/tt/TestJava.java:9: verify: Show statement expression k has value 1", 15
                ,"/tt/TestJava.java:12: verify: Show statement expression m has value ( - 1 )", 15
                ,"/tt/TestJava.java:12: verify: Show statement expression k has value 1", 17
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method m", 10
                );
    }

    @Test
    public void testShowStatement() {
        expectedExit = 0;
        addOptions("--lang=jml");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static class Key { public int k; }
                  //@ public normal_behavior
                  //@   requires true;
                  public static void m(int i, int j) {
                     //@ show i;
                  }
                }
                """
                ,"/tt/TestJava.java:7: warning: [strict-jml] The show statement construct is an OpenJML extension to JML and not allowed under --lang=jml", 10
                );
    }

    @Test
    public void testShowStatementErrors() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static class Key { public int k; }
                  //@ public normal_behavior
                  //@   requires true;
                  public static void m(int i, int j) {
                     //@ show i;
                     //@ show ijk
                     //@ show i ijk;
                     //@ show;
                     //@ show ijk
                     //@ show %;
                     //@ show ijk show ijk;
                  }
                }
                """
                ,"/tt/TestJava.java:8: error: Incorrectly formed or terminated show statement near here -- perhaps a missing semicolon", 18
                ,"/tt/TestJava.java:9: error: Incorrectly formed or terminated show statement near here", 17
                ,"/tt/TestJava.java:11: error: Incorrectly formed or terminated show statement near here -- perhaps a missing semicolon", 18
                ,"/tt/TestJava.java:12: error: illegal start of expression", 15
                ,"/tt/TestJava.java:13: error: Incorrectly formed or terminated show statement near here -- perhaps a missing semicolon", 18
                );
    }

    @Test
    public void testArrayCopy() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static class Key { public int k; }
                  //@ public normal_behavior
                  //@   requires k != null && \\nonnullelements(k) && \\elemtype(\\typeof(k)) <:= \\type(Key);
                  public static void m(Key[] k) {
                  //@   assert k != null;
                     Key[] kk = java.util.Arrays.copyOfRange(k,0,k.length);
                     //@ assert kk != null;
                     //@ assert \\nonnullelements(kk);
                     //@ assert \\elemtype(\\typeof(kk)) == \\type(Key);
                  }
                }
                """
                );
    }

    @Test
    public void testArrayCopy2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public static class Key { public int k; }
                  //@ public normal_behavior
                  //@   requires k != null && \\nonnullelements(k) && \\elemtype(\\typeof(k)) <:= \\type(Key);
                  public static void m(Key[] k) {
                     Key[] kk = java.util.Arrays.<Key>copyOfRange(k,0,k.length);
                     //@ assert kk != null;
                     //@ assert \\nonnullelements(kk);
                     //@ assert \\elemtype(\\typeof(kk)) == \\type(Key);
                  }
                }
                """
                );
    }


    @Test
    public void testDuplicateGhost() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public void m() {
                  //@ ghost int k = 1;
                  //@ ghost int k = 2;
                  }
                }
                """
                ,"/tt/TestJava.java:5: error: variable k is already defined in method m()", 17
                );
    }

    @Test
    public void testChainedCompare() {
    	expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public void m() {
                  //@ ghost int i = 2;
                  //@ check  0 <= i < 10 < 12;
                  //@ set i = 10;
                  //@ check  !(0 <= i < 10);
                  //@ check  0 <= i < 11 == 2 <= i <= 12;
                  //@ check  11 >= i+1 > 1 == 12 >= i > 2;
                  //@ check  11 >= i+1 < 12;
                  //@ check  11 >= i+1 <= 12 == true;
                  //@ check  11 > i+1 < 12;
                  //@ check  11 > i+1 <= 12 == true;
                  //@ check  11 >= i+1 > 1 != 12 <= i <= 22;
                  //@ check  11 < i+1 > 12;
                  //@ check  11 < i+1 >= 12;
                  //@ check  11 <= i+1 > 12;
                  //@ check  11 <= i+1 >= 12;
                  }
                }
                """
                ,"/tt/TestJava.java:10: error: Cannot chain comparisons that are in different directions", 17
                ,"/tt/TestJava.java:11: error: Cannot chain comparisons that are in different directions", 17
                ,"/tt/TestJava.java:12: error: Cannot chain comparisons that are in different directions", 17
                ,"/tt/TestJava.java:13: error: Cannot chain comparisons that are in different directions", 17
                ,"/tt/TestJava.java:15: error: Cannot chain comparisons that are in different directions", 17
                ,"/tt/TestJava.java:16: error: Cannot chain comparisons that are in different directions", 17
                ,"/tt/TestJava.java:17: error: Cannot chain comparisons that are in different directions", 17
                ,"/tt/TestJava.java:18: error: Cannot chain comparisons that are in different directions", 17
                );
    }

    @Test
    public void testAllowForbid2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  //@ signals_only \\nothing;
                  public void m(/*@ nullable */ TestJava t) {
                    int i = t.iii //@ allow NullPointerException;
                    ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (ExceptionList) in method m", 14
                ,"/tt/TestJava.java:4: verify: Associated declaration", 7
                );
    }

    @Test
    public void testAllowForbid3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  public void m(/*@ nullable */ TestJava t) {
                    int i = t.iii //@ forbid NullPointerException;
                    ;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m", 14
                );
    }

    @Test
    public void testAllowForbid5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {
                    int i = t.iii; //@ ignore NullPointerException;
                    i = t.iii;
                  }
                }
                """
                );
    }

    @Test
    public void testAllowForbid4() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {
                    int i = t.iii; //@ ignore java.lang.XX;
                    i = t.iii;
                  }
                }
                """
                ,"/tt/TestJava.java:5: error: cannot find symbol\n" + 
                                                "  symbol:   class XX\n" + 
                                                "  location: package java.lang", 41

                ,"/tt/TestJava.java:5: error: cannot find symbol\n" +  
                                                "  symbol:   class XX\n" + 
                                                "  location: package java.lang", 41

                );
    }

    @Test
    public void testAllowForbid6() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {
                    int i = t.iii;
                    i = t.iii;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m", 14
                );
    }

    @Test
    public void testAllowForbid7() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  //@ signals_only NullPointerException;
                  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {
                    int i = t.iii;   // OK NullPointerException permitted
                    i = t.iii;
                  }
                }
                """
                );
    }

    @Test
    public void testAllowForbid8() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {
                    try {
                      int i = t.iii;    // OK NullPointerException permitted
                      i = t.iii;
                 } catch (NullPointerException e) {}
                  }
                }
                """
                );
    }

    @Test
    public void testAllowForbid9() {
        addOptions("--check-feasibility=reachable");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava  {
                  public int iii;
                  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {
                     //@ assume t == null;
                    int i = t.iii; //@ ignore NullPointerException;
                    //@ reachable; // ERROR    i = t.iii;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: There is no feasible path to program point at reachable statement in method tt.TestJava.m(tt.@org.jmlspecs.annotation.Nullable TestJava,tt.@org.jmlspecs.annotation.Nullable TestJava)", 9
                );
    }


    @Test
    public void testAllowForbid() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int iii;
                  public void m(/*@ nullable */ TestJava t) {
                    int i = t.iii //@ allow NullPointerException;
                    ;
                    int j = t.iii; //@ forbid NullPointerException;
                    k = t.iii; //@ forbid ;
                    k = t.iii; //@ forbid NullPointerException
                    ;
                    k = t.iii; //@ forbid NullPointerException, ArrayIndexOutOfBoundsException;
                    k = t.iii; //@ forbid NullPointerException ArrayIndexOutOfBoundsException;
                    k = t.iii; //@ forbid NullPointerException; allow NullPointerException
                    k = t.iii; //@ ignore NullPointerException; allow NullPointerException
                    k = t.iii; //@ ignore NullPointerException; forbid NullPointerException
                    k = t.iii; //@ forbid java.lang.NullPointerException
                    k = t.iii //@ forbid java.lang.
                    ;
                  }
                }
                """
                        ,"/tt/TestJava.java:17: error: Expected an identifier here in the line annotation",36
                        // When there is an error, no attribution is performed
                        );
    }
    
    @Test
    public void testdatagroup() {
    	helpEsc("tt.C",
    	        """
    	        package tt; /*@ non_null_by_default */ public class C {
    	            //@ public model \\datagroup g;
    	        }
    	        """
    	        );
    }
    
    @Test
    public void testBRC() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void m1() {
                    //@ refining
                    //@   returns true;
                    //@   continues false;
                    //@   breaks true;
                    {}
                  }
                }
                """
                ,"/tt/TestJava.java:5: warning: Not implemented for static checking: returns clause", 11
                ,"/tt/TestJava.java:6: warning: Not implemented for static checking: continues clause", 11
                ,"/tt/TestJava.java:7: warning: Not implemented for static checking: breaks clause", 11
                );
        
    }

    @Test
    public void testAccessibleDefault() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ accessible \\nothing;
                  int m() { return i; }
                  int i;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible) in method m: i", 20
                ,"/tt/TestJava.java:3: verify: Associated declaration", 7
                );
    }

    @Test
    public void testVerifyExit() {
        helpEsc("tt.TestJava",
            """
            package tt;
            public class TestJava {
              public void m() {
                //@ assert false;
              }
            }
            """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m", 9
        );
    }

    @Test
    public void testVerifyLegacy() {
        expectedExit = 0;
        addOptions("--verify-exit=-1");
        helpEsc("tt.TestJava",
            """
            package tt;
            public class TestJava {
              public void m() {
                //@ assert false;
              }
            }
            """
                ,"/tt/TestJava.java:4: warning: The prover cannot establish an assertion (Assert) in method m", 9
        );
    }

    @Test
    public void testVerifyCustom() {
        expectedExit = 4;
        addOptions("--verify-exit=4");
        helpEsc("tt.TestJava",
            """
            package tt;
            public class TestJava {
              public void m() {
                //@ assert false;
              }
            }
            """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m", 9
        );
    }
    
    @Test
    public void testVerifyWarnWerror() {
        expectedExit = 1;
        addOptions("-Werror");
        helpEsc("tt.TestJava",
            """
            package tt;
            public class TestJava {
              public void m() {
                //@ assert false
              }
            }
            """
                ,"/tt/TestJava.java:4: warning: Inserting missing semicolon at the end of a assert statement", 21
                ,"error: warnings found and -Werror specified"
        );
    }
    
    @Test
    public void testVerifyWerror() {
        expectedExit = 0;
        addOptions("-Werror","--verify-exit=0");
        helpEsc("tt.TestJava",
            """
            package tt;
            public class TestJava {
              public void m() {
                //@ assert false;
              }
            }
            """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m", 9
        );
    }

    @Test
    public void testVerifyWerrorB() {
        expectedExit = 6;
        addOptions("-Werror");
        helpEsc("tt.TestJava",
            """
            package tt;
            public class TestJava {
              public void m() {
                //@ assert false;
              }
            }
            """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m", 9
        );
    }

    @Test
    public void verifyExitA() {
        expectedExit = 2;
        addOptions("--verify-exit=7");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"error: Invalid value for --verify-exit: 7", -1
        );
    }

    @Test
    public void verifyExitB() {
        expectedExit = 2;
        addOptions("--verify-exit=x");
        helpEsc("tt.TestJava", "package tt; public class TestJava {}"
                ,"error: Invalid value for --verify-exit: x", -1
        );
    }

    @Test
    public void verifyExitC() {
        expectedExit = 6;
        addOptions("--verify-exit=");
        helpEsc("tt.TestJava", "package tt; public class TestJava { public void m() { /*@ assert false; */ } }"
                ,"/tt/TestJava.java:1: verify: The prover cannot establish an assertion (Assert) in method m", 59
        );
    }

    // THE FOLLOWING WERE ALL COMMENTED OUT AT ONE POINT
    
    // TODO: Parser has trouble distinguishing an @ for \old from an @ for a type annotation. Is the complexity worth the feature?
    @Test @Ignore
    public void testAt() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ code_java_math spec_java_math*/ public class TestJava {
                  static public int i;
                  //@ assigns i;
                  //@ ensures i == \\old(i)+2;
                  public static void bok() { x: i = i + 1; /*@ assert i == i@x + 1 && i == (i+1)@x; */ i = i + 1;}
                  //@ assigns i;
                  //@ ensures i == \\old(i+1);
                  public static void bbad() { i = i - 1; /*@ assert i == i@x + 1; */ }
                  //@ assigns i;
                  public void bok2() { x: i = i + 1; /*@ assert i == this.i@x + 1; */ i = i + 1;}
                  //@ requires a.length > 10 && a[0] >= 0;
                  //@ assigns i;
                  public static void bok3(int[] a) { x: i = i + 1; /*@ assert a[0]@x > -1; */ i = i + 1;}
                }
                """
                ,"/tt/TestJava.java:9: error: There is no label named x", 60
                );
    }

}
