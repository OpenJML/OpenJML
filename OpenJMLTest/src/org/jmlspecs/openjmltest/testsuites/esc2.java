package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
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
        helpEsc("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"

              + "  //@ public behavior  ensures true;\n"
              + "  public void m4() {\n"
              + "    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = false; \n"
              + "    /*@ nullable */ Integer k = null;\n" 
              + "    values.add(k);\n" 
              + "  }\n"

              + "  public TestJava() {}"

              + "}"
              ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Precondition) in method m4",15
              ,"$SPECS/java/util/List.jml:119: verify: Associated declaration",13
              ,"$SPECS/java/util/Collection.jml:153: verify: Precondition conjunct is false: o != null",19
              ,"$SPECS/java/util/List.jml:109: verify: Precondition conjunct is false: containsNull || o != null",33

                );

    }
    @Test
    public void testForEach2a3() {
        addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"

                + "  //@ public normal_behavior  ensures true;\n" 
                + "  public void m3() {\n" 
                + "    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = true; \n"
                + "    Integer k = Integer.valueOf(1);\n"
                + "    values.add(k);\n" 
                + "  }\n"

                + "  public TestJava() {}"

                + "}"

        );
    }
    @Test
    public void testForEach2a4() {
        addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava", "package tt; import java.util.*; \n" 
                + "public class TestJava { \n"

                + "  //@ public normal_behavior  ensures true;\n"
                + "  public void m4() {\n"
                + "    List<Integer> values = new LinkedList<Integer>(); //@ set values.containsNull = true; \n"
                + "    Integer k = 0;\n" 
                + "    values.add(k);\n" 
                + "  }\n"

                + "  public TestJava() {}"

                + "}"

        );
    }
    @Test
    public void testForEachBad() {
        expectedExit = 1;
        helpEsc("tt.TestJava", 
                  "package tt; \n" 
                + "public class TestJava { \n"

                + "  public void m1a() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    for (long k: a) {\n" 
                + "    }\n"
                + "    //@ ghost int i = \\count;\n" // Out of scope
                + "  }\n"

                + "  public void m2() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    //@ ghost int i = \\count;\n" // Out of scope
                + "  }\n"

                + "  public void m4() {\n" 
                + "    long[] a = { 1,2,3,4};\n" 
                + "    for (long k: a) {\n"
                + "      //@ set \\count = 6;\n" // Syntax error
                + "    }\n"
                + "  }\n"

                + "  public void v1a() {\n"
                + "    Integer[] a = { 1,2,3,4};\n"
                + "    for (Integer k: a) {\n"
                + "    }\n"
                + "    //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n" // Out of scope
                + "  }\n"

                + "  public void v2() {\n"
                + "    long[] a = { 1,2,3,4};\n"
                + "    //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n" // Out of scope
                + "    }\n"

                + "  public void v4() {\n"
                + "    Integer[] a = { 1,2,3,4};\n"
                + "    for (Integer k: a) {\n"
                + "      //@ set \\values = null;\n" // Syntax error
                + "    }\n"
                + "  }\n"

                + "  public void v10a() {\n" + "    long[] a = { 1,2,3,4};\n"
                + "    for (long k: a) {\n"
                + "      //@ ghost org.jmlspecs.lang.JMLList i = \\values;\n" // OK
                + "    }\n" + "  }\n"

                + "}"

                , "/tt/TestJava.java:7: error: A \\count token is used outside the scope of a foreach loop", 23
                ,"/tt/TestJava.java:11: error: A \\count token is used outside the scope of a foreach loop", 23
                ,"/tt/TestJava.java:16: error: unexpected type\n  required: variable\n  found:    value", 15
                ,"/tt/TestJava.java:16: error: Unexpected kind of LHS in a set statement: \\count",15
                ,"/tt/TestJava.java:16: error: The LHS in a set statement must be a ghost variable",15
                ,"/tt/TestJava.java:23: error: A \\values token is used outside the scope of a foreach loop", 45
                ,"/tt/TestJava.java:27: error: A \\values token is used outside the scope of a foreach loop", 45
                ,"/tt/TestJava.java:32: error: unexpected type\n  required: variable\n  found:    value", 15
                ,"/tt/TestJava.java:32: error: Unexpected kind of LHS in a set statement: \\values",15
                ,"/tt/TestJava.java:32: error: The LHS in a set statement must be a ghost variable",15
                );
    }

    @Test
    public void testNonNullElements1() {
//        Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m1x(Object[] a) {\n"
                + "    //@ assume \\nonnullelements(a);\n" 
                + "    //@ assume a.length > 1;\n"
                + "    //@ assert a[0] != null;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m11(Object[] a) {\n"
                + "    //@ assume \\nonnullelements(a);\n" 
                + "    //@ assert a != null;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m11a(/*@ non_null */ Object[] a) {\n"
                + "    //@ assume \\nonnullelements(a);\n" 
                + "    //@ assert a == null;\n" // BAD
                + "  }\n"

                + "}"
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method m11a", 9
                );
    }

    @Test
    public void testNonNullElements2a() {
        helpEsc("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m1a(Object[] a) {\n"
                + "    //@ assume a != null && a.length > 1;\n" 
                + "    //@ assert a[0] != null;\n" // BAD
                + "  }\n"

                + "}"
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m1a", 9
                );
    }

    @Test
    public void testNonNullElements2b() {
//      Assume.assumeTrue(runLongTests);
        helpEsc("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m2(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 0;\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "}"
                );
    }

    @Test
    public void testNonNullElements2c() {
        helpEsc("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m22(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 0;\n"
                + "    //@ assert (\\forall int i; 0<=i && i<a.length; a[i] != null);\n" // OK
                + "  }\n"

                + "}"
                );
    }

    @Test
    public void testNonNullElements3() {
//        Assume.assumeTrue(runLongests);
        helpEsc("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"

                + "  //@ requires a != null && a.length == 1;\n"
                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m3(Object[] a) {\n" 
                + "    a[0] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ requires a != null && a.length == 1;\n"
                + "  //@ modifies \\everything;\n" 
                + "  public void m33(Object[] a) {\n"
                + "    //@ assume a[0] != null;\n"
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ requires a != null && a.length == 2;\n"
                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m4(Object[] a) {\n" 
                + "    a[0] = new Object();\n" 
                + "    a[1] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "}"
                );
    }

    @Test
    public void testNonNullElements4() {
        helpEsc("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"


                + "  //@ modifies \\everything;\n" 
                + "  public void m44(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 2;\n" 
                + "    //@ assume a[0] != null;\n"
                + "    //@ assume a[1] != null;\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m4a(Object[] a) {\n" 
                + "    //@ assume a != null && a.length == 3;\n"
                + "    a[0] = new Object();\n" 
                + "    a[1] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // BAD -- FIXME cannot infer a forall quantifier from the individual statements
                + "  }\n"

                + "  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;\n"
                + "  public void m5(Object[] a) {\n" 
                + "    //@ assume \\nonnullelements(a) && a.length == 3;\n"
                + "    a[0] = new Object();\n" 
                + "    //@ assert \\nonnullelements(a);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m5a(Object[] a) {\n"
                + "    //@ assume a != null && a.length == 3;\n" 
                + "    a[0] = null;\n"
                + "    //@ assert \\nonnullelements(a);\n" // BAD
                + "  }\n"

                + "}"
                ,anyorder(
                seq("/tt/TestJava.java:10: verify: The prover cannot establish an assertion (NullArgument) in method m4a", 34)
                ,seq("/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method m4a", 9)
                ,seq("/tt/TestJava.java:17: verify: The prover cannot establish an assertion (NullArgument) in method m5", 34)
                ,seq("/tt/TestJava.java:27: verify: The prover cannot establish an assertion (Assert) in method m5a", 9)
                ));
    }

    @Test
    public void testNotModified() {
        helpEsc("tt.TestJava", "package tt; \n" + "public class TestJava { \n"

                + "  //@ requires i == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m1(int i) {\n"
                + "    i = 5;\n" + "    //@ assert \\not_modified(i);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m1a(int i) {\n" + "    i = 5;\n"
                + "    //@ assert \\not_modified(i);\n" // BAD
                + "  }\n"

                + "  public int i;\n" + "  public static int si;\n" + "  //@ ghost public int gi;\n"

                + "  //@ requires i == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m2() {\n"
                + "    i = 5;\n" + "    //@ assert \\not_modified(i);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m2a() {\n" + "    i = 5;\n"
                + "    //@ assert \\not_modified(i);\n" // BAD
                + "  }\n"

                + "  //@ requires si == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m3() {\n"
                + "    si = 5;\n" + "    //@ assert \\not_modified(si);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m3a() {\n" + "    si = 5;\n"
                + "    //@ assert \\not_modified(si);\n" // BAD
                + "  }\n"

                + "  //@ requires gi == 5;\n" + "  //@ modifies \\everything;\n" + "  public void m4() {\n"
                + "    //@ set gi = 5;\n" + "    //@ assert \\not_modified(gi);\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" + "  public void m4a() {\n" + "    //@ set gi = 5;\n"
                + "    //@ assert \\not_modified(gi);\n" // BAD
                + "  }\n"

                + "}", "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m1a",
                9, "/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Assert) in method m2a", 9,
                "/tt/TestJava.java:37: verify: The prover cannot establish an assertion (Assert) in method m3a", 9,
                "/tt/TestJava.java:48: verify: The prover cannot establish an assertion (Assert) in method m4a", 9);
    }

    // Test well-definedness within the implicit old
    @Test
    public void testNotModified2() {
        helpEsc("tt.TestJava", "package tt; \n" + "public class TestJava { \n"

                + "  public int i;\n" 
                + "  public static /*@ nullable */ TestJava t;\n"

                + "  //@ requires t != null;\n" 
                + "  //@ modifies \\everything;\n" 
                + "  public void m0() {\n"
                + "    //@ assert \\not_modified(t.i);\n" // OK
                + "  }\n"

                + "  //@ requires t != null;\n" 
                + "  //@ modifies \\everything;\n" 
                + "  public void m1a() {\n"
                + "    t = null;\n" 
                + "    //@ assert \\not_modified(t.i) ? true: true;\n" // BAD
                + "  }\n"

                + "  //@ requires t == null;\n" 
                + "  //@ modifies \\everything;\n" 
                + "  public void m1b() {\n"
                + "    t = new TestJava();\n" 
                + "    //@ assert \\not_modified(t.i) ? true: true;\n" // OK
                + "  }\n"

                + "  //@ modifies \\everything;\n" 
                + "  public void m1c() {\n"
                + "    //@ assert \\not_modified(t.i) ? true: true;\n" // BAD
                + "  }\n"

                + "}"
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1a",31
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1b",31
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1c",31);
    }

    // TODO - test not_modified and old nested in each other; remember to test
    // definedness



    @Test
    public void testOldJava() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                 + "/*@ code_java_math*/ public class TestJava { \n" 
                 + "  static public  int i;\n"
                 + "  //@ static public constraint i > \\old(i);\n" 
                 + "  //@ assigns i;\n"
                 + "  //@ ensures true;\n" 
                 + "  public static void bok() { i = i - 1; }\n" 
                 + "}"
                ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (Constraint) in method TestJava",29
                ,"/tt/TestJava.java:4: verify: Associated declaration", 21
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method bok", 22
                ,"/tt/TestJava.java:4: verify: Associated declaration", 21
                );
    }



    @Test
    public void testOld2Math() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "/*@ code_bigint_math*/ public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ assigns i;\n" + "  //@ ensures i == \\old(i)+2;\n"
                        + "  public static void bok() { i = i + 1; i = i + 1;}\n" + "  //@ assigns i;\n"
                        + "  //@ ensures i == \\old(i+1);\n" 
                        + "  public static void bbad() { i = i - 1; }\n" 
                        + "}"
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method bbad",22
                ,"/tt/TestJava.java:8: verify: Associated declaration", 7
                );
    }

    @Test
    public void testOld2() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "/*@ code_java_math spec_java_math*/ public class TestJava { \n" 
                        + "  static public int i;\n"
                        + "  //@ assigns i;\n" 
                        + "  //@ ensures i == \\old(i)+2;\n"
                        + "  public static void bok() { i = i + 1; i = i + 1;}\n" 
                        + "  //@ assigns i;\n"
                        + "  //@ ensures i == \\old(i+1);\n" 
                        + "  public static void bbad() { i = i - 1; }\n" 
                        + "}"
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method bbad",22
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
                "package tt; import org.jmlspecs.annotation.*; \n" 
                        + "/*@ code_bigint_math*/ public class TestJava { \n"
                        + "  public void insta() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                        + "  public void instb() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i-2; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                        + "  public void instc() { int i = 5; /*@ loop_invariant i<=5 && i>=0; decreases i; */ while (i>0) { i = i+1; } /*@ assert i == 0; */ }\n"
                        + "  public void instd() { int i = 5; /*@ loop_invariant i<=5 && i>0; decreases i; */ while (i>0) { i = i-1; } /*@ assert i == 0; */ }\n"
                        + "}"
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
                "package tt; import org.jmlspecs.annotation.*; \n" 
              + "public class TestJava { \n"
              + "  public void insta() { int i = 5; /*@ loop_invariant i> 0; decreases i; */ while (--i > 0) { } /*@ assert i == 0; */ }\n"
              + "  public void instb() { int i = 5; /*@ loop_invariant i>=0; decreases i; */ while (i-- > 0) { } /*@ assert i == -1; */ }\n"
              + "  public void instc() { int i = 5; /*@ loop_invariant i> 1; decreases i; */ while (--i > 1) { } /*@ assert i == 1; */ }\n"
              + "}"
              ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method insta", 40
              ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method instb", 40
              ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (LoopInvariantAfterLoop) in method instc", 40
              );
    }

    @Test
    public void testIncDec() {
        helpEsc("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst1() { int i = 5; i++; /*@ assert i == 6; */ }\n"
                        + "  public void inst1b() { int i = 5; i++; /*@ assert i == 5; */ }\n"
                        + "  public void inst2() { int i = 5; i--; /*@ assert i == 4; */ }\n"
                        + "  public void inst2b() { int i = 5; i--; /*@ assert i == 5; */ }\n"
                        + "  public void inst3() { int i = 5; ++i; /*@ assert i == 6; */ }\n"
                        + "  public void inst3b() { int i = 5; ++i; /*@ assert i == 5; */ }\n"
                        + "  public void inst4() { int i = 5; --i; /*@ assert i == 4; */ }\n"
                        + "  public void inst4b() { int i = 5; --i; /*@ assert i == 5; */ }\n" + "}",
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1b", 46,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst2b", 46,
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method inst3b", 46,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method inst4b",
                46);
    }

    @Test
    public void testIncDec2() {
        helpEsc("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  public void inst1() { int i = 5; int j = i++; /*@ assert j == 5; */ }\n"
                        + "  public void inst1b() { int i = 5; int j = i++; /*@ assert j == 6; */ }\n"
                        + "  public void inst2() { int i = 5; int j = i--; /*@ assert j == 5; */ }\n"
                        + "  public void inst2b() { int i = 5; int j = i--; /*@ assert j == 4; */ }\n"
                        + "  public void inst3() { int i = 5; int j = ++i; /*@ assert j == 6; */ }\n"
                        + "  public void inst3b() { int i = 5; int j = ++i; /*@ assert j == 5; */ }\n"
                        + "  public void inst4() { int i = 5; int j = --i; /*@ assert j == 4; */ }\n"
                        + "  public void inst4b() { int i = 5; int j = --i; /*@ assert j == 5; */ }\n" + "}",
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method inst1b", 54,
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method inst2b", 54,
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method inst3b", 54,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method inst4b",
                54);
    }

    @Test
    public void testFieldsOK() {
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*;/*@ nullable_by_default */  \n"
                + "public class TestJava { \n" + "  int f; static int sf;\n" + "  int g; static int sg;\n"
                + "  public static TestJava t;  //@ public static invariant t != null; \n"
                + "  public void inst2(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 2; */ }\n" // OK
                + "  public void inst2a(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  /*@ assert t.f == 3; */ }\n" // BAD
                + "  public void inst3(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */ }\n" // OK
                + "  public void inst3a(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 4; */ }\n" // BAD
                + "  public void inst4(int/*@non_null*/[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 2; */ }\n" // OK
                + "  public void inst4a(int/*@non_null*/[] a) { /*@ assume t.g == 2; */  t.f = 3; /*@ assert t.g == 4; */ }\n" // BAD
                + "  public void inst5(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 4; */}\n" // OK
                + "  public void inst5a(int/*@non_null*/[] a) { /*@ assume t.f == 2; */  t.f = 3; /*@ assert t.f == 3; */  t.f = 4; /*@ assert t.f == 5; */}\n" // BAD
                + "  public void inst6(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f == b.f; */}\n" // OK
                + "  public void inst6a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b = a; /*@ assert a.f != b.f; */}\n" // BAD
                + "  public void inst7(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 7; */}\n" // OK
                + "  public void inst7a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { b.f = 0; b = a; a.f = 7; /*@ assert b.f == 8; */}\n" // BAD
                + "  public void inst8(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf == b.sf; */}\n" // OK
                + "  public void inst8a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { /*@ assert a.sf != b.sf; */}\n" // BAD
                + "  public void inst9(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 == b.sf; */}\n" // OK
                + "  public void inst9a(/*@non_null*/TestJava a, /*@non_null*/TestJava b) { a.sf = 3; /*@ assert 3 != b.sf; */}\n" // BAD
                + "  public void inst10(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a == this ==> a.f == f; */}\n" // OK
                + "  public void inst10a(/*@non_null*/TestJava a) { /*@ assert f == this.f; */ /*@ assert a.f == f; */}\n" // BAD
                + "  public void inst11(/*@non_null*/TestJava a) { /*@ assert sf == this.sf; */ /*@ assert a.sf == sf; */}\n" // OK
                + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method inst2a", 75,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method inst3a", 84,
                "/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method inst4a", 84,
                "/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method inst5a",
                118,
                "/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Assert) in method inst6a", 85,
                "/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method inst7a",
                103,
                "/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assert) in method inst8a", 78,
                "/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method inst9a", 88,
                "/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method inst10a",
                81);
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
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  int f; static int sf;\n" + "  int g; static int sg;\n" + "  static TestJava t;\n"
                + "  public void inst1a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j!=0; */ }\n" // OK
                + "  public void inst1b(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; break; case 2: j = 2; } /*@ assert j==1; */ }\n" // BAD
                + "  public void inst2(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                + "  public void inst2a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: j=1; break; default: j=-1; case 2: j = 2; } /*@ assert i==0 ==> j==-1; */ }\n" // BAD
                + "  public void inst3(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                + "  public void inst3a(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {default: i=4; } break; default: j=-1; break; case 2: j = 2; } /*@ assert j>0; */ }\n" // OK
                + "  public void inst4(int i) { /*@ assume i>=-1 && i <=1; */ int j=0; switch (i+1) { case 1: switch(i) {} break; default: j=-1; case 2: j = 2; } /*@ assert j>=0; */ }\n" // OK
                + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method inst1b", 148,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method inst2a", 141,
                "/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method inst3a",
                170);
    }

    @Test
    public void testTry() {
        helpEsc("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  static public int i;\n" + "  //@ ensures i == 2;\n"
                        + "  public void inst1() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // OK
                        + "  //@ ensures i == 1;\n"
                        + "  public void inst1a() { i=0; try { i = 1; return; } finally { i = 2; } }\n" // BAD
                        + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Postcondition) in method inst1a",
                44, "/tt/TestJava.java:6: verify: Associated declaration", 7);
    }

    @Test
    public void testTryWithMethodCall() {
        addOptions("--esc--max-warnings=1");
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava  {\n"
                + "//@ public exceptional_behavior requires b;  signals (Exception e) true; signals (RuntimeException e) true;\n"
                + "//@ also\n" + "//@ public normal_behavior requires !b; ensures true;\n"
                + "public static void ex(boolean b) throws RuntimeException {\n"
                + "    if (b) throw new RuntimeException();\n" + "}\n" + "public static int sk; public int k;\n" + "\n" // Line
                                                                                                                        // 10
                + "//@ requires k < 0;\n" + "//@ ensures true;\n" + "//@ also\n" + "//@ requires k > 0;\n"
                + "//@ ensures \\result == 1;\n" + "public int m1() {\n" + "    int i = 1;\n" + "    try {\n"
                + "        ex(true);\n" + "        i = 1;\n" // Line 20
                + "    } catch (Exception e) {\n" + "        //@ assert e != null;\n" + "        i = 2;\n" + "    }\n"
                + "    return i;\n" + "}\n" + "\n" + "//@ requires k < 0;\n" + "//@ ensures true;\n" + "//@ also\n" // Line
                                                                                                                    // 30
                + "//@ requires k > 0;\n" + "//@ ensures \\result == 1;\n" + "public int m2() {\n" + "    int i = 1;\n"
                + "    try {\n" + "        ex(false);\n" + "        i = 0;\n" + "    } catch (Exception e) {\n"
                + "        //@ assert e != null;\n" + "        i = 1;\n" // Line
                                                                            // 40
                + "    }\n" + "    return i;\n" + "}\n" + "}",
                "/tt/TestJava.java:25: verify: The prover cannot establish an assertion (Postcondition) in method m1",
                5, "/tt/TestJava.java:15: verify: Associated declaration", 5,
                "/tt/TestJava.java:42: verify: The prover cannot establish an assertion (Postcondition) in method m2",
                5, "/tt/TestJava.java:32: verify: Associated declaration", 5);
    }

    @Test
    public void testMisc() {
        helpEsc("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                        + "  static public int i;\n" + "  //@ requires i > 0;\n" + "  //@ ensures i > 0;\n"
                        + "  public static void m() { i = i -1; }\n" // OK
                        + "}",
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Postcondition) in method m",
                22, "/tt/TestJava.java:5: verify: Associated declaration", 7);
    }

    @Test
    public void testArith() { // TODO - need more arithmetic support
        Assume.assumeTrue(runLongTests);
        addOptions("-logic=AUFNIRA");
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "public class TestJava { \n"
                + "  public static void m1(int a, int b) { /*@ assert a*2 == a + a; */ }\n"
                // +" public static void m2(int a, int b) { /*@ assert a * b ==
                // a *(b-1) + a; */ }\n"
                + "  public static void m3(int a, int b) { /*@ assert (2*a)/2 == a; */ }\n"
                + "  public static void m4(int a, int b) { /*@ assert a >= 0 ==> (a%3) < 3; */ }\n"
                + "  public static void m5(int a, int b) { /*@ assert a >= 0 ==> (a%3) >= 0; */ }\n"
                // +" public static void m6(int a, int b) { /*@ assert (a >= 0
                // && b > 0) ==> (a%b) >= 0; */ }\n"
                // +" public static void m7(int a, int b) { /*@ assert (a >= 0
                // && b > 0) ==> ((a*b)%b) == 0; */ }\n"
                + "  public static void m8(int a, int b) { /*@ assert (a >= 0 ) ==> ((5*a)%5) == 0; */ }\n" + "}");
    }

    @Test
    public void testPureMethodStatic() {
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n"
                + "public class TestJava { \n" 
                + "  //@ requires i < 1000; ensures \\result == i+1;\n"
                + "  //@ pure \n" 
                + "  public static int m(int i) { return i+1; }\n"
                + "  public static void m1(int a, int b) { /*@ assume a < 100; */ int k = a+1; /*@ assert k == m(a); */ }\n"
                + "  public static void m1a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(a); */ }\n"
                + "  public static void m2(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                + "  public static void m2a(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                + "  public static void m3(int a, int b) { /*@ assume a < 100; */ int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                + "  public static void m3a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(m(a+1)); */ }\n" + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1a", 82,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2a", 84,
                "/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m3a", 82);
    }

    @Test
    public void testPureMethod() {
        helpEsc("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" 
                        + "public class TestJava { \n"
                        + "  //@ requires i < 1000; ensures \\result == i+1;\n" 
                        + "  //@ pure \n"
                        + "  public int m(int i) { return i+1; }\n"
                        + "  public void m1(int a, int b) { /*@ assume a < 100; */ int k = a+1; /*@ assert k == m(a); */ }\n"
                        + "  public void m1a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(a); */ }\n"
                        + "  public void m2(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == m(a) + m(a); */ }\n"
                        + "  public void m2a(int a, int b) { /*@ assume a < 100; */ int k = 2*a+2; /*@ assert k == 1 + m(a) + m(a); */ }\n"
                        + "  public void m3(int a, int b) { /*@ assume a < 100; */ int k = a+3; /*@ assert k == m(m(a+1)); */ }\n"
                        + "  public void m3a(int a, int b) { /*@ assume a < 100; */ int k = a+2; /*@ assert k == m(m(a+1)); */ }\n" + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m1a", 75,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m2a", 77,
                "/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m3a", 75);
    }

    @Test
    public void testPureNonFunction() {
        helpEsc("tt.TestJava",
                "package tt; import org.jmlspecs.annotation.*; \n" + "/*@ code_bigint_math*/ public class TestJava { \n"
                        + "  public int z;\n" + "  //@ ensures \\result == z+1;\n" + "  //@ pure \n"
                        + "  public int m() { return z+1; }\n"
                        + "  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                        + "  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                        + "  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                        + "  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n"
                        + "  public void m3(int a, int b) { z = 7; int k = z+1; /*@ assert k == m(); */ }\n"
                        + "  public void m3a(int a, int b) { z = 7; int k = z+2; /*@ assert k == m(); */ }\n" + "}",
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m1a", 52,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m2a", 54,
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m3a", 59);
    }

    @Test
    public void testPureNoArguments() {
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n"
                + "/*@ code_bigint_math*/ public class TestJava { \n" 
                + "  public static int z;\n"
                + "  //@ ensures \\result == z+1;\n" 
                + "  //@ pure \n" 
                + "  public static int m() { return z+1; }\n"
                + "  public void m1(int a, int b) { int k = z+1; /*@ assert k == m(); */ }\n"
                + "  public void m1a(int a, int b) { int k = z+2; /*@ assert k == m(); */ }\n"
                + "  public void m2(int a, int b) { int k = 2*z+2; /*@ assert k == m() + m(); */ }\n"
                + "  public void m2a(int a, int b) { int k = 2*z+2; /*@ assert k == 1 + m() + m(); */ }\n" + "}",
                "/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assert) in method m1a", 52,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m2a", 54);
    }

    @Test
    public void testInheritedPost() {
        addOptions("-code-math=bigint","--check-feasibility=exit");
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" 
                + "abstract class TestJavaA { \n"
                + "  \n" 
                + "  //@ ensures \\result > 0;\n" 
                + "  abstract public int m(int iii);\n" 
                + "}\n"
                + "abstract class TestJavaB extends TestJavaA { \n" 
                + "  //@ also\n" 
                + "  //@ ensures \\result > ii;\n"
                + "  abstract public int m(int ii);\n" 
                + "}\n"
                + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" 
                + "  //@ also public normal_behavior\n"
                + "  //@ ensures \\result == i+1;\n" 
                + "  //@ pure\n" 
                + "  public int m(int i) { return i+1; }\n"
                + "  //@ requires a >= 0;\n" 
                + "  //@ ensures \\result == a+1;\n" 
                + "  public int n1(int a) { return m(a); }\n"
                + "  public int n1a(int a) { return m(-1); }\n" 
                + "}"
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (Postcondition) in method m",25
                ,"/tt/TestJava.java:4: verify: Associated declaration", 7
                ,"/tt/TestJava.java:20: verify: There is no feasible path to program point at program exit in method tt.TestJava.n1a(int)",41
                );
    }

    @Test
    public void testInheritedPostA() {
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "abstract class TestJavaA { \n"
                + "  //@ requires iii > 0;\n" + "  //@ ensures \\result > 0;\n" + "  abstract public int m(int iii);\n"
                + "}\n" + "abstract class TestJavaB extends TestJavaA { \n" + "  //@ also\n"
                + "  //@ ensures \\result > ii;\n" + "  abstract public int m(int ii);\n" + "}\n"
                + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" + "  //@ also\n"
                + "  //@ ensures \\result == i+1;\n" + "  //@ pure\n" + "  public int m(int i) { return i+1; }\n"
                + "  //@ ensures \\result == a+1;\n" + "  public int n1(int a) { return m(a); }\n"
                + "  public int n1a(int a) { return m(-1); }\n" + "}");
    }

    @Test
    public void testInheritedPostB() {
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" + "abstract class TestJavaA { \n"
                + "  //@ requires iii > 0;\n" + "  //@ ensures \\result > 0;\n" + "  abstract public int m(int iii);\n"
                + "}\n" + "abstract class TestJavaB extends TestJavaA { \n" + "  //@ also\n"
                + "  //@ requires ii > 0;\n" + "  //@ ensures \\result > ii;\n" + "  abstract public int m(int ii);\n"
                + "}\n" + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" + "  //@ also\n"
                + "  //@ requires i > 0;\n" + "  //@ ensures \\result == i+1;\n" + "  //@ pure\n"
                + "  public int m(int i) { return i+1; }\n" + "}");
    }

    @Test
    public void testInheritedPre() {
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n" 
                + "abstract class TestJavaA { \n"
                + "  //@ requires iii == 1;\n" 
                + "  //@ ensures \\result == iii;\n"
                + "  abstract public int m(int iii);\n" 
                + "}\n" 
                + "abstract class TestJavaB extends TestJavaA { \n"
                + "  //@ also\n" 
                + "  //@ requires ii == 2;\n" 
                + "  //@ ensures \\result == ii;\n"
                + "  abstract public int m(int ii);\n" 
                + "}\n"
                + "/*@ code_bigint_math*/ public class TestJava extends TestJavaB { \n" 
                + "  //@ also\n"
                + "  //@ requires i == 3;\n" 
                + "  //@ ensures \\result == i;\n" 
                + "  //@ pure\n"
                + "  public int m(int i) { return i; }\n" // OK
                + "  //@ requires a >= 1 && a <= 3;\n" 
                + "  //@ ensures \\result == a;\n"
                + "  public int m1(int a) { return m(a); }\n" // OK
                + "  //@ ensures \\result == a;\n" 
                + "  public int m1a(int a) { return m(-1); }\n" // Precondition
                                                                                                    // ERROR
                + "}"
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Precondition) in method m1a",35
                ,"/tt/TestJava.java:18: verify: Associated declaration",14
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: iii == 1",20
                ,"/tt/TestJava.java:9: verify: Precondition conjunct is false: ii == 2",19
                ,"/tt/TestJava.java:15: verify: Precondition conjunct is false: i == 3",18
                );
    }

    @Test
    public void testTrace() {
        helpEsc("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  //@ requires 0<=ii && ii <=3;\n"
                + "  //@ ensures \\result < 0;\n" + "  public static int m(int ii) { \n"
                + "    if (ii==1) return -1; \n" + "    if (ii==2) return -2; \n" + "    if (ii==3) return -3; \n"
                + "    ii = 7;\n" + "    return 0; }\n" + "  //@ requires ii == 2;\n" + "  //@ ensures \\result == 0;\n"
                + "  public static int mm(int ii) { \n" + "    if (ii==1) return -1; \n"
                + "    if (ii==2) return -2; \n" + "    if (ii==3) return -3; \n" + "    ii = 7;\n"
                + "    return 0; }\n" + "  public static int is;\n" + "  //@ ensures is == 6;\n"
                + "  public static int m3(int ii) { \n" + "    try { ii = 0; \n" + "      if (ii == 0) return -2; \n"
                + "    } finally { \n" + "      is = 7;\n" + "    }" + "    return 0; }\n"
                + "  //@ ensures \\result == 1;\n" + "  public static int m4(int ii) { \n" + "    try { ii = 0; \n"
                + "      if (ii == 0) return -2; \n" + "    } finally { \n" + "      is = 7;\n" + "    }"
                + "    return 0; }\n" + "}",
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Postcondition) in method m",
                5, "/tt/TestJava.java:4: verify: Associated declaration", 7,
                "/tt/TestJava.java:15: verify: The prover cannot establish an assertion (Postcondition) in method mm",
                16, "/tt/TestJava.java:12: verify: Associated declaration", 7,
                "/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Postcondition) in method m3",
                20, "/tt/TestJava.java:20: verify: Associated declaration", 7,
                "/tt/TestJava.java:30: verify: The prover cannot establish an assertion (Postcondition) in method m4",
                20, "/tt/TestJava.java:27: verify: Associated declaration", 7);
    }

    @Test
    public void testForwardInit() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                "package tt; \n"
                		+ "public class TestJava { \n"
                		+ "  public static int m() { \n"
                		+ "    int c = c+1; \n"
                        + "    //@ assert c == 1; \n"
                		+ "    return c; \n"
                        + "  }\n"
                        + "}",
                "/tt/TestJava.java:4: error: variable c might not have been initialized", 13);
    }

    @Test
    public void testGhostVars() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public static int m() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ assert d + c == 9; \n" + "    return c; \n"
                        + "  }\n" + "  public static int mm() { \n" + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" + "    //@ assert d + c == 10; \n" + "    return c; \n"
                        + "  }\n" + "}",
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method mm", 9);
    }

    @Test
    public void testSet() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" 
                        + "  public static int m() { \n" 
                        + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" 
                        + "    //@ set d = 10;\n" 
                        + "    //@ assert d + c == 14; \n"
                        + "    return c; \n" + "  }\n" 
                        + "  public static int mm() { \n" 
                        + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" 
                        + "    //@ set d = 10;\n" 
                        + "    //@ assert d + c == 15; \n"
                        + "    return c; \n" + "  }\n" 
                        + "  public static int q() { \n" 
                        + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" 
                        + "    //@ set   d = 10;\n" 
                        + "    //@ assert d + c == 14; \n"
                        + "    return c; \n" + "  }\n" 
                        + "  public static int qq() { \n" 
                        + "    int c = 4; \n"
                        + "    //@ ghost int d = c+1;\n" 
                        + "    //@ set   d = 10;\n" 
                        + "    //@ assert d + c == 15; \n"
                        + "    return c; \n" 
                        + "  }\n" 
                        + "}",
                "/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assert) in method mm", 9,
                "/tt/TestJava.java:28: verify: The prover cannot establish an assertion (Assert) in method qq", 9);
    }

    /**
     * Tests whether various ways of guarding a field reference are successful
     * in avoiding a failed assertion.
     */
    @Test
    public void testUndefinedInJava() {
        helpEsc("tt.TestJava", "package tt; \n" 
                + "/*@ nullable_by_default */ public class TestJava { \n" 
                + "  int j;\n"
                + "  public static void m0(TestJava o) { \n" 
                + "    int i = o.j; \n" 
                + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" 
                + "    int i = o.j; \n" 
                + "  }\n"
                + "  //@ requires o != null;\n" 
                + "  public static void m2(TestJava o) { \n" 
                + "    int i = o.j; \n"
                + "  }\n" 
                + "  public static void m3(TestJava o) { \n" 
                + "    boolean i = o != null && o.j == 1; \n"
                + "  }\n" 
                + "  public static void m4(TestJava o) { \n" 
                + "    boolean i = o == null || o.j == 1; \n"
                + "  }\n" 
                + "  public static void m5(TestJava o) { \n" 
                + "    int i = ( o != null ? o.j : 6); \n"
                + "  }\n" 
                + "  public static void m6(TestJava o) { \n" 
                + "    int i = ( o == null ? 7 : o.j); \n"
                + "  }\n" 
                + "  public static void m6a(TestJava o) { \n" 
                + "    int i = ( o != null ? 7 : o.j); \n"
                + "  }\n" 
                + "  //@ public normal_behavior  ensures \\result == (oo != null);\n"
                + "  public static boolean p(TestJava oo) { \n" + "    return oo != null; \n" + "  }\n"
                + "  public static void m7(TestJava o) { \n" 
                + "    boolean i = p(o) && o.j == 0; \n" 
                + "  }\n"
                + "  public static void m7a(TestJava o) { \n" 
                + "    boolean i = p(o) || o.j == 0; \n" 
                + "  }\n" 
                + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m0",
                14,
                "/tt/TestJava.java:27: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m6a",
                32,
                "/tt/TestJava.java:37: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m7a",
                26);
    }

    /**
     * Tests whether various ways of guarding a method call are successful in
     * avoiding a failed assertion.
     */
    @Test
    public void testUndefinedMInJava() {
        helpEsc("tt.TestJava", "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  int j;\n"
                + "  public static void m0(TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  //@ requires o != null;\n" + "  public static void m2(TestJava o) { \n" + "    int i = o.z(); \n"
                + "  }\n" + "  public static void m3(TestJava o) { \n" + "    boolean i = o != null && o.z() == 1; \n"
                + "  }\n" + "  public static void m4(TestJava o) { \n" + "    boolean i = o == null || o.z() == 1; \n"
                + "  }\n" + "  public static void m5(TestJava o) { \n" + "    int i = ( o != null ? o.z() : 6); \n"
                + "  }\n" + "  public static void m6(TestJava o) { \n" + "    int i = ( o == null ? 7 : o.z()); \n"
                + "  }\n" + "  public static void m6a(TestJava o) { \n" + "    int i = ( o != null ? 7 : o.z()); \n"
                + "  }\n" + "  //@ public normal_behavior  ensures \\result == (oo != null);\n"
                + "  public static boolean p(TestJava oo) { \n" + "    return oo != null; \n" + "  }\n"
                + "  public static void m7(TestJava o) { \n" + "    boolean i = p(o) && o.z() == 0; \n" + "  }\n"
                + "  public static void m7a(TestJava o) { \n" + "    boolean i = p(o) || o.z() == 0; \n" + "  }\n"
                + "  //@ signals_only \\nothing; \n public int z() { return 0; }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m0",
                14,
                "/tt/TestJava.java:27: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m6a",
                32,
                "/tt/TestJava.java:37: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m7a",
                26);
    }

    /**
     * Tests whether various ways of guarding a method call are successful in
     * avoiding a failed assertion.
     */
    @Test
    public void testUndefinedSMInJava() {
        helpEsc("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  int j;\n"
                + "  public static void m0(TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" + "    int i = o.z(); \n" + "  }\n"
                + "  //@ requires o != null;\n" + "  public static void m2(TestJava o) { \n" + "    int i = o.z(); \n"
                + "  }\n" + "  public static void m3(TestJava o) { \n" + "    boolean i = o != null && o.z() == 1; \n"
                + "  }\n" + "  public static void m4(TestJava o) { \n" + "    boolean i = o == null || o.z() == 1; \n"
                + "  }\n" + "  public static void m5(TestJava o) { \n" + "    int i = ( o != null ? o.z() : 6); \n"
                + "  }\n" + "  public static void m6(TestJava o) { \n" + "    int i = ( o == null ? 7 : o.z()); \n"
                + "  }\n" + "  public static void m6a(TestJava o) { \n" + "    int i = ( o != null ? 7 : o.z()); \n"
                + "  }\n" + "  //@ public normal_behavior  ensures \\result == (oo != null);\n"
                + "  public static boolean p(TestJava oo) { \n" + "    return oo != null; \n" + "  }\n"
                + "  public static void m7(TestJava o) { \n" + "    boolean i = p(o) && o.z() == 0; \n" + "  }\n"
                + "  public static void m7a(TestJava o) { \n" + "    boolean i = p(o) || o.z() == 0; \n" + "  }\n"
                + "  //@ signals_only \\nothing; \n public static int z() { return 0; }\n" + "}");
    }

    /**
     * Tests whether the various kinds of undefined constructs are actually
     * detected.
     */
    @Test
    public void testUndefinedInJava2() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ /*@ code_java_math spec_java_math*/ public class TestJava { \n"
                        + "  int j;\n" 
                        + "  public static void m(TestJava o) { \n" 
                        + "    int i = o.j; \n" 
                        + "  }\n  "
                        + "  public static void m1(int[] a) { \n" 
                        + "    int i = a[0]; \n" 
                        + "  }\n"
                        + "  //@ requires a != null;\n" 
                        + "  public static void m2(int[] a) { \n"
                        + "    int i = a[-1]; \n" 
                        + "  }\n" 
                        + "  //@ requires a != null;\n"
                        + "  public static void m3(int[] a) { \n" 
                        + "    //@ assume a.length == 1; \n"
                        + "    int i = a[1]; \n" 
                        + "  }\n" 
                        + "  public static void m4(int i, int j) { \n"
                        + "    int k = i/j; \n" 
                        + "  }\n" 
                        + "  public static void m5(int i, int j) { \n"
                        + "    int k = i%j; \n" 
                        + "  }\n" 
                        + "  public static void m6( RuntimeException r) { \n"
                        + "    Throwable t = r;\n" 
                        + "    Exception rr = ((Exception)t); \n" 
                        + "  }\n"
                        + "  public static void m6a(Exception r) { \n" 
                        + "    Throwable t = r;\n"
                        + "    RuntimeException rr = ((RuntimeException)t) ; \n" 
                        + "  }\n"
                        + "  public static void m7(/*@ non_null*/ RuntimeException r) { \n" 
                        + "    Throwable t = r;\n"
                        + "    Exception rr = ((Exception)t); \n" + "  }\n"
                        + "  public static void m7a(/*@ non_null*/Exception r) { \n" + "    Throwable t = r;\n"
                        + "    RuntimeException rr = ((RuntimeException)t) ; \n" + "  }\n" + "}",
                seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",
                        14,
                        anyorder(
                                seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",
                                        14),
                                seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",
                                        14)),
                        "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m2",
                        14,
                        "/tt/TestJava.java:17: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m3",
                        14,
                        "/tt/TestJava.java:20: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m4",
                        14,
                        "/tt/TestJava.java:23: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method m5",
                        14,
                        "/tt/TestJava.java:31: verify: The prover cannot establish an assertion (PossiblyBadCast) in method m6a: a Throwable cannot be proved to be a RuntimeException",
                        28,
                        "/tt/TestJava.java:39: verify: The prover cannot establish an assertion (PossiblyBadCast) in method m7a: a Throwable cannot be proved to be a RuntimeException",
                        28));
    }

    /**
     * Tests whether various ways of guarding a field reference are successful
     * in avoiding a failed assertion.
     */
    @Test
    public void testUndefinedInSpec() {
        helpEsc("tt.TestJava", "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  int j;\n"
                + "  public static void m(TestJava o) { \n" + "    //@ assume o.j == 1; \n" + "  }\n"
                + "  public static void m1(/*@non_null*/ TestJava o) { \n" + "    //@ assume o.j == 1; \n" + "  }\n"
                + "  //@ requires o != null;\n" + "  public static void m2(TestJava o) { \n"
                + "    //@ assume o.j == 1; \n" + "  }\n" + "  public static void m3(TestJava o) { \n"
                + "    //@ assume o != null && o.j == 1; \n" + "  }\n" + "  public static void m4(TestJava o) { \n"
                + "    //@ assume o == null || o.j == 1; \n" + "  }\n" + "  public static void m5(TestJava o) { \n"
                + "    //@ assume o != null ==> o.j == 1; \n" + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                17);
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
                "package tt; \n"
                		+ "/*@ nullable_by_default */ public class TestJava { \n"
                		+ "  int j;\n"
                        + "  public static void m(TestJava o) { \n"
                		+ "    //@ assume o.j == 1; \n"
                        + "  }\n  "
                        + "  public static void m1(int[] a) { \n"
                        + "    //@ assume a[0] == 1; \n"
                        + "  }\n"
                        + "  //@ requires a != null;\n"
                        + "  public static void m2(int[] a) { \n"
                        + "    //@ assume a[-1] == 1; \n"
                        + "  }\n"
                        + "  //@ requires a != null;\n"
                        + "  public static void m3(int[] a) { \n"
                        + "    //@ assume a.length == 1; \n"
                        + "    //@ assume a[1] == 1; \n"
                        + "  }\n"
                        + "  public static void m4(int i, int j) { \n"
                        + "    //@ assume i/j == 4; \n"
                        + "  }\n"
                        + "  public static void m5(int i, int j) { \n"
                        + "    //@ assume i%j == 4; \n"
                        + "  }\n"
                        + "  public static void m6(RuntimeException r) { \n"
                        + "    Throwable t = r;\n"
                        + "    //@ assume ((Exception)t) != null ? true : true; \n" // OK
                        + "  }\n"
                        + "  public static void m6a(Exception r) { \n"
                        + "    Throwable t = r;\n"
                        + "    //@ assume ((RuntimeException)t) != null ? true : true ; \n"
                        + "  }\n"
                        + "  public static void m7(/*@ non_null*/RuntimeException r) { \n"
                        + "    Throwable t = r;\n"
                        + "    //@ assume ((Exception)t) != null ? true : true; \n"
                        + "  }\n"
                        + "  public static void m7a(/*@ non_null*/Exception r) { \n"
                        + "    Throwable t = r;\n"
                        + "    //@ assume ((RuntimeException)t) != null ? true : true ; \n"
                        + "  }\n"
                        + "}"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",17
                ,anyorder(
                        seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1",
                                17),
                        seq("/tt/TestJava.java:8: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",
                                17))
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method m2",17
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m3",17
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m4",17
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (UndefinedDivideByZero) in method m5",17
                ,"/tt/TestJava.java:31: verify: The prover cannot establish an assertion (UndefinedBadCast) in method m6a: a Throwable cannot be proved to be a RuntimeException",17
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (UndefinedBadCast) in method m7a: a Throwable cannot be proved to be a RuntimeException",17
                );
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - loop invariants, variants, represents, signals, modifies
    // TODO - old constructs, quantifications, set comprehension, pure methods -
    // check other JMl expressions
    @Test
    public void testUndefinedInSpec3() {
        helpEsc("tt.TestJava", "package tt; import org.jmlspecs.annotation.*; \n"
                + "/*@ nullable_by_default */ public class TestJava { \n" 
                + "  public int j = 1;\n"
                + "  public static @Nullable TestJava t;\n" 
                + "  public static void m(TestJava o) { \n"
                + "    //@ assume o.j == 1; \n"    // ERROR
                + "  }\n  " 
                + "  public static void m1(TestJava o) { \n"
                + "    //@ assert o.j == 1 ? true : true; \n"  // ERROR 
                + "  }\n  " 
                + "  public static void m2(TestJava o) { \n"
                + "    //@ ghost int i = o.j; \n"    // ERROR
                + "  }\n  " 
                + "  public static void m3(TestJava o) { \n"
                + "    //@ ghost int i; set   i = o.j; \n"  // ERROR
                + "  }\n  " 
                + "  //@ requires o.j == 1;\n"              // ERROR
                + "  public static void m4(@Nullable TestJava o) { \n" 
                + "  }\n  "
                + "  //@ ensures t.j == 1 ? true : true;\n"   // ERROR
                + "  public static void m5(TestJava o) { \n" 
                + "  }\n  "
                + "  public static void m6(TestJava o) { \n" 
                + "    //@ ghost int i; set i = o.j; \n"   // ERROR
                + "  }\n  " 
                + "}",  // FIXME - all of these should be PossiblylNullDereference
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                17,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1",
                17,
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m2",
                24,
                "/tt/TestJava.java:15: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m3",
                33,
                "/tt/TestJava.java:17: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m4",
                19,
                "/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m5",
                18,
                "/tt/TestJava.java:22: verify: Associated method exit",
                4,
                "/tt/TestJava.java:24: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m6",
                31);
    }

    /** Tests whether undefinedness is caught in various JML constructions */
    // TODO - readable writable, represents, assert, other clauses
    @Test
    public void testUndefinedInSpec4() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  int j = 1;\n"
                        + "  static TestJava t;\n" + "  public void m(TestJava o) { \n" + "    //@ assume o.j == 1; \n"
                        + "  }\n" + "}",
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                17);
    }

    @Test
    public void testUndefinedInSpec4d() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  public int j = 1;\n"
                        + "  public static TestJava t;\n" + "  public void m(TestJava o) { \n" + "  }\n"
                        + "  //@ public invariant t.j ==1 ? true: true;\n" + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method TestJava",
                25,
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                25);
    }

    /** Check to catch undefinedness in an initially clause */
    @Test
    public void testUndefinedInSpec4a() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n"
                        + "  public boolean j = true;\n" + "  static TestJava t;\n" + "  public TestJava() { \n"
                        + "  }\n" + "  //@ public initially t.j ? true : true;\n" + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method TestJava",
                25);
    }

    /** Check to catch undefinedness in a constraint clause */
    @Test
    public void testUndefinedInSpec4b() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  public int j = 1;\n"
                        + "  public static TestJava t;\n" + "  public void m(TestJava o) { \n" + "  }\n  "
                        + "  //@ public constraint t.j ==1 ? true: true;\n" + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m",
                28);
    }

    /** Check to catch undefinedness in a axiom clause */
    @Test
    public void testUndefinedInSpec4c() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public int j = 1;\n"
                        + "  public static TestJava t;\n" + "  public void m(TestJava o) { \n" + "  }\n  "
                        + "  // @ axiom (\\forall TestJava q;; q.j ==1);\n" // FIXME
                        + "}");
    }

    @Test
    public void testUndefinedInSpec5() {
        addOptions("--nullable-by-default", "--no-checkAccessible");
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static TestJava t;\n" + "  int j = t.j;\n" + "}",
                "/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method TestJava",
                12);
    }

    @Test
    public void testUndefinedInJava6() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "/*@ nullable_by_default */ public class TestJava { \n" + "  static TestJava t;\n"
                        + "  int j = 1;\n" + "  public void m1(TestJava o) { \n" + "    int i = t.j; \n" + "  }\n  "
                        + "  public void m2(TestJava o) { \n" + "    t.j = 1; \n" + "  }\n  "
                        + "  public void m3(TestJava o) { \n" + "    t.j += 1; \n" + "  }\n  "
                        + "  public void m4(TestJava o) { \n" + "    int i = 0; i += t.j; \n" + "  }\n  "
                        + "  public void m5(TestJava o) { \n" + "    assert t.j == 1 ? true : true; \n" + "  }\n  "
                        // TODO for, while, foreach, do, switch, case, if,
                        // throw, method call, index, conditional,
                        // annotation, binary, unary, conditional, new array,
                        // new class, return, synchronized
                        + "}",
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m1",
                14,
                "/tt/TestJava.java:9: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m2",
                6,
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m3",
                6,
                "/tt/TestJava.java:15: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m4",
                22,
                "/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m5",
                13);
    }

    // TODO - need tests within various Java constructs, including with
    // short-circuits

    /** This test tests catch blocks */
    @Test
    public void testCatch() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava { \n" 
                        + "  public void m() {\n" 
                        + "    int i = 0;\n"
                        + "    try {\n" 
                        + "      throw new RuntimeException();\n"
                        + "    } catch (RuntimeException e) {\n" 
                        + "      i=1;\n" 
                        + "    } catch (Exception e) {\n"
                        + "      i=2;\n" 
                        + "    }\n" 
                        + "    //@ assert i == 1;\n" 
                        + "  }\n" 
                        + "  public void ma() {\n"
                        + "    int i = 0;\n" 
                        + "    try {\n" 
                        + "      throw new RuntimeException();\n"
                        + "    } catch (RuntimeException e) {\n" 
                        + "      i=1;\n" 
                        + "    } catch (Exception e) {\n"
                        + "      i=2;\n" 
                        + "    }\n" 
                        + "    //@ assert i == 2;\n" 
                        + "  }\n" 
                        + "}",
                "/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assert) in method ma", 9);
    }

    @Test
    public void testCatch2() {
        addOptions("-method=ma");
        helpEsc("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  public void mx() {\n"
                + "    int i = 0;\n" + "    try {\n" + "      throw new Exception();\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    }\n" + "    //@ assert i == 2;\n" + "  }\n" + "  public void mp() {\n"
                + "    int i = 0; int j = 0;\n" + "    try {\n" + "      throw new Exception();\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    } finally {\n" + "      j=3;\n" + "    }\n"
                + "    //@ assert i == 2 && j == 3;\n" + "  }\n" + "  public void ma() {\n" + "    int i = 0;\n"
                + "    try {\n" + "      throw new Exception();\n" + "    } catch (RuntimeException e) {\n"
                + "      i=1;\n" + "    } catch (Exception e) {\n" + "      i=2;\n" + "    }\n"
                + "    //@ assert i == 1;\n" + "  }\n" + "  public void m1(int k) {\n"
                + "    int i = 0; int j = 0; //@ assume k == 0; \n" + "    try {\n" + "      try {\n"
                + "         if (k == 0) throw new Exception();\n" + "      } finally {\n" + "         j = 50;\n"
                + "      }\n" + "      j = 60;\n" + "    } catch (RuntimeException e) {\n" + "      i=1;\n"
                + "    } catch (Exception e) {\n" + "      i=2;\n" + "    }\n" + "    //@ assert i == 2 && j == 50;\n"
                + "  }\n" + "  public void m11(int k) throws Exception {\n"
                + "    int i = 0; int j = 0; //@ assume k == 0; \n" + "    try {\n" + "    try {\n" + "      try {\n"
                + "         if (k == 0) throw new Exception();\n" + "      } finally {\n" + "         j = 50;\n"
                + "      }\n" + "      j = 60;\n" + "    } catch (RuntimeException e) {\n" + "      i=1;\n"
                + "    } finally {\n" + "      i=2;\n" + "    }\n" + "    } finally {\n"
                + "    //@ assert i == 2 && j == 50;\n" + "    }\n"

                + "  }\n" + "  public void m2() {\n" + "    int i = 20;\n" + "    try {\n" + "      i=10;\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    }\n" + "    i = 0;\n" + "    //@ assert i == 0;\n" + "  }\n"
                + "  public void m3() {\n" + "    int i = 20;\n" + "    try {\n" + "      i=10;\n"
                + "    } catch (RuntimeException e) {\n" + "      i=1;\n" + "    } catch (Exception e) {\n"
                + "      i=2;\n" + "    } finally {\n" + "      i = 0;\n" + "    }\n" + "    //@ assert i == 0;\n"
                + "  }\n" + "}",
                "/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Assert) in method ma", 9
        // FIXME - enventually rejuvenate dead branch detection
        // ,"/tt/TestJava.java:42: verify: else branch apparently never taken
        // in method tt.TestJava.m1(int)",14
        // ,"/tt/TestJava.java:59: verify: else branch apparently never taken
        // in method tt.TestJava.m11(int)",14
        );
    }

    @Test
    public void testCatch3() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires i != 1 & i != 2;\n"
                        + "  //@   ensures \\result == 0;\n"
                        + "  //@ also public exceptional_behavior \n"
                        + "  //@   requires i == 2 && ee != null; \n"
                        + "  //@   signals (ArrayIndexOutOfBoundsException ex) true; \n"
                        + "  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {\n"
                        + "    try {\n"
                        + "      if (i == 1) throw e;\n"
                        + "      if (i == 2) throw ee;\n"
                        + "      return 0;\n"
                        + "    } catch (NullPointerException exx) {\n"
                        + "      throw ae;\n"
                        + "    }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }


    @Test
    public void testCatch3a() {
        helpEsc("tt.TestJava",
                "package tt; //@ non_null_by_default \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires i != 1 & i != 2;\n"
                        + "  //@   ensures \\result == 0;\n"
                        + "  //@ also public exceptional_behavior \n"
                        + "  //@   requires i == 2; \n"
                        + "  //@   signals (ArrayIndexOutOfBoundsException ex) true; \n"
                        + "  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {\n"
                        + "    try {\n"
                        + "      if (i == 1) throw e;\n"
                        + "      if (i == 2) throw ee;\n"
                        + "      return 0;\n"
                        + "    } catch (NullPointerException exx) {\n"
                        + "      throw ae;\n"
                        + "    }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testCatch4() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires e != null & ee != null & ae != null;\n"
                        + "  //@   requires i != 1 & i != 2;\n"
                        + "  //@   ensures \\result == 0;\n"
                        + "  //@ also public exceptional_behavior \n"
                        + "  //@   requires e != null & ee != null & ae != null;\n"
                        + "  //@   requires i == 2; \n"
                        + "  //@   signals (ArrayIndexOutOfBoundsException ex) true; \n"
                        + "  public int m(int i, NullPointerException e, ArrayIndexOutOfBoundsException ee, AssertionError ae) {\n"
                        + "    try {\n"
                        + "      if (i == 1) throw e;\n"
                        + "      if (i == 2) throw ee;\n"
                        + "      return 0;\n"
                        + "    } catch (NullPointerException exx) {\n"
                        + "      throw ae;\n"
                        + "    }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testTypes() {
        helpEsc("tt.TestJava", "package tt; \n" 
                + "public class TestJava { \n"
                + "  public void m1(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ check \\typeof(o) == \\typeof(o);\n" 
                + "    //@ check \\typeof(o) == \\type(Object);\n"
                + "    //@ check !(\\typeof(o) <: \\type(Object));\n" 
                + "    //@ check \\typeof(o) <:= \\type(Object);\n" 
                + "  }\n"
                + "  public void m1a(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ check \\typeof(o) != \\type(Object);\n" 
                + "  }\n"
                + "  public void m2(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ check \\typeof(o) == \\type(Object);\n" 
                + "  }\n"
                + "  public void m2a(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ check \\typeof(o) == \\type(TestJava);\n" 
                + "  }\n"
                + "  public void m3(/*@non_null*/Object o) {\n" 
                + "    //@ assume \\typeof(o) == \\type(Object);\n"
                + "    //@ check \\type(TestJava) <: \\typeof(o);\n" 
                + "    //@ check \\type(TestJava) <:= \\typeof(o);\n" 
                + "  }\n" 
                + "}",
                "/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m1a", 9,
                "/tt/TestJava.java:20: verify: The prover cannot establish an assertion (Assert) in method m2a", 9);
    }

    @Test
    public void testTypes2() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  public void m1(/*@non_null*/TestJava o) {\n"
                        + "    //@ assume \\typeof(o) == \\type(TestJava);\n"
                        + "    //@ assert \\typeof(o) <:= \\type(Object);\n" + "  }\n"
                        + "  public void m2(/*@non_null*/TestJava o) {\n"
                        + "    //@ assert \\typeof(o) <:= \\type(Object);\n" + "  }\n" + "}");
    }

    @Test
    public void testTypes3() {
        helpEsc("tt.TestJava",
                "package tt; import org.jmlspecs.lang.JML; \n" 
                        + "public class TestJava { \n"
                        + "  public void m1(/*@non_null*/Object o) {\n"
                        + "    //@ assert JML.erasure(\\typeof(o)) == o.getClass();\n" 
                        + "  }\n" 
                        + "}");
    }

    @Test
    public void testSignals1() {
        helpEsc("tt.TestJava",
                  "package tt; \n"
                + "public class TestJava { \n"
                + "  static public int i;\n"
                + "  //@ requires i >= 0;\n"
                + "  //@ ensures i>0;\n"
                + "  //@ signals (Exception e) i == 0;\n"
                + "  public void m1() throws Exception {\n"
                + "    if (i==0) throw new Exception();\n" + "  }\n"
                + "  //@ requires i >= 0;\n"
                + "  //@ ensures i>0;\n"
                + "  //@ signals (Exception e) i == 1;\n" // FAILS
                + "  public void m1a() throws Exception {\n"
                + "    if (i==0) throw new Exception();\n"
                + "  }\n"
                + "}"
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m1a", 15
                ,"/tt/TestJava.java:12: verify: Associated declaration", 7
                );
    }

    @Test
    public void testSignals2() {
        helpEsc("tt.TestJava", "package tt; \n"
                + "public class TestJava { \n"
                + "  static public int i;\n"
                + "  //@ requires i >= 0;\n"
                + "  //@ ensures i>0;\n"
                + "  //@ signals (Exception e) i == 0;\n" // OK
                + "  public void m2() throws Exception {\n"
                + "    if (i==0) throw new Exception();\n"
                + "  }\n"
                + "  //@ requires i >= 0;\n"
                + "  //@ ensures i>0;\n"
                + "  //@ signals (RuntimeException e) i == 1;\n" // FAILS
                + "  public void m2a() throws Exception {\n"
                + "    if (i==0) throw new RuntimeException();\n"
                + "  }\n"
                + "}",
                "/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m2a",
                15, "/tt/TestJava.java:12: verify: Associated declaration", 7);
    }

    @Test
    public void testSignals3() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (Exception e) i == 0;\n"
                        + "  public void m3() throws RuntimeException {\n"
                        + "    if (i==0) throw new RuntimeException();\n" + "  }\n" + "  //@ requires i >= 0;\n"
                        + "  //@ ensures i>0;\n" + "  //@ signals (Exception e) i == 1;\n" // FAILS
                        + "  public void m3a() throws RuntimeException {\n"
                        + "    if (i==0) throw new RuntimeException();\n" + "  }\n" + "}",
                "/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m3a",
                15, "/tt/TestJava.java:12: verify: Associated declaration", 7);
    }

    @Test
    public void testSignals4() {
        helpEsc("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                + "  //@ requires i >= 0;\n" + "  //@ ensures i>0;\n" + "  //@ signals (RuntimeException e) i == 1;\n" // OK
                                                                                                                        // because
                                                                                                                        // a
                                                                                                                        // RuntimeException
                                                                                                                        // is
                                                                                                                        // never
                                                                                                                        // thrown
                + "  public void m4() throws Exception {\n" + "    if (i==0) throw new Exception();\n" + "  }\n" + "}");
    }

    @Test
    public void testSignalsOnly() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static int i;\n"
                        + "  //@ signals_only java.io.IOException;\n" // FAILS
                        + "  public void m1a() throws Exception {\n" + "    if (i==0) throw new Exception();\n"
                        + "  }\n" + "  //@ signals_only \\nothing;\n" // FAILS
                        + "  public void m2a() {\n" + "    if (i==0) throw new RuntimeException();\n" + "  }\n"
                        + "  //@ signals_only Exception;\n" // OK
                        + "  public void m3() {\n" + "    if (i==0) throw new RuntimeException();\n" + "  }\n" + "}",
                "/tt/TestJava.java:6: verify: The prover cannot establish an assertion (ExceptionList) in method m1a",
                15, "/tt/TestJava.java:4: verify: Associated declaration", 7,
                "/tt/TestJava.java:10: verify: The prover cannot establish an assertion (ExceptionList) in method m2a",
                15, "/tt/TestJava.java:8: verify: Associated declaration", 7);
    }

    @Test
    public void testConstraint() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for m1();\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14);
    }

    @Test
    public void testConstraint2() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for ! m1();\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14);
    }

    @Test
    public void testConstraint3() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for \\everything;\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14,
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14);
    }

    @Test
    public void testConstraint3a() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for !\\nothing;\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14,
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14);
    }

    @Test
    public void testConstraint4() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for \\nothing;\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint4a() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for !\\everything;\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m2() {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint6() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i);\n" + "  public void m1() {\n" + "  }\n"
                        + "  public void m2() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14,
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m2", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14);
    }

    @Test
    public void testConstraint7() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for m1(), m1(int);\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m1(int j) {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14,
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method m1", 15,
                "/tt/TestJava.java:4: verify: Associated declaration", 14);
    }

    @Test
    public void testConstraint7a() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for m1(), m1(int);\n" + "  public static void m1() {\n"
                        + "  }\n" + "  public static void m1(int j) {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint8() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public constraint i > \\old(i) for ! m1(), m1(int);\n" + "  public void m1() {\n"
                        + "  }\n" + "  public void m1(int j) {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint9() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
        		  "package tt; \n"
                + "public class TestJava { \n"
        	    + "  static public int i;\n"
                + "  //@ public constraint i > \\old(i) for TestJava();\n"
        	    + "  public TestJava() {\n"
                + "  }\n"
        	    + "}",
                "/tt/TestJava.java:4: error: Constructors are not allowed as methods in non-static constraint clauses", 41);
    }

    @Test
    public void testConstraint9a() {
        helpEsc("tt.TestJava", "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                + "  //@ public constraint i > \\old(i);\n" + "  public TestJava() {\n" + "  }\n" + "}");
    }

    @Test
    public void testConstraint10() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public static constraint i > \\old(i) for TestJava();\n" + "  public TestJava() {\n"
                        + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method TestJava",
                10, "/tt/TestJava.java:4: verify: Associated declaration", 21);
    }

    @Test
    public void testConstraint10a() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "public class TestJava { \n" + "  static public int i;\n"
                        + "  //@ public static constraint i > \\old(i);\n" + "  public TestJava() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method TestJava",
                10, "/tt/TestJava.java:4: verify: Associated declaration", 21);
    }

    @Test
    public void testConstraint11() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "interface A { \n" + "  //@ ghost static public int i = 0;\n"
                        + "  //@ public static constraint i > \\old(i);\n" + "}\n"
                        + "public class TestJava implements A { \n" + "  public TestJava() {\n" + "  }\n" + "}",
                "/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Constraint) in method TestJava",
                10, "/tt/TestJava.java:4: verify: Associated declaration", 21);
    }

    @Test
    public void testConstraint11a() {
        helpEsc("tt.TestJava",
                "package tt; \n" + "interface A { \n" + "  //@ ghost static public int i = 0;\n"
                        + "  //@ public constraint i > \\old(i);\n" + "}\n" + "public class TestJava implements A { \n"
                        + "  public TestJava() {\n" + "  }\n" + "}");
    }

    @Test // FIXME - for reasons unknown, this test appears to be
            // non-deterministic - sometimes succeeding sometimes failing
    public void testMethodAxioms() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ normal_behavior \n"
                        + "  //@ ensures \\result == (i > 0 && i < 10);\n" 
                        + "  //@ pure\n"
                        + "  //@ model public boolean m(int i);\n"

                        + "  public void mm() {\n" 
                        + "  //@ check (\\forall int k; 3<k && k <7; m(k));\n"
                        + "  //@ check (\\forall int k; 3<k && k <7; m(k-1));\n"
                        + "  //@ check !(\\forall int k; -3<k && k <7; m(k));\n" 
                        + "  }\n" 
                        + "}");
    }

    @Test
    public void testMethodAxioms2() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ normal_behavior \n"
                        + "  //@ ensures \\result == (0 < i < 10);\n" 
                        + "  //@ no_state\n"
                        + "  //@ model public static boolean m(int i);\n"

                        + "  //@ pure\n" 
                        + "  public void mm() {  //@ assert !m(10); \n" // Assertion serves as a lemma that aids in quickly proving the following assert
                        + "  //@ assert !(\\forall int k; 3 < k < 11; m(k));\n" // Should be OK because m(10) is false
                        + "  }\n" + "}"
                        );
    }

    @Test
    public void testMethodAxioms2a() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ normal_behavior \n"
                        + "  //@ ensures \\result == (0 < i < 10);\n" 
                        + "  //@ pure\n"
                        + "  //@ model public boolean m(int i);\n"

                        + "  //@ pure\n" 
                        + "  public void mm() {\n" 
                        + "  //@ assert (\\forall int k; 3 < k < 11; m(k));\n" // ERROR because m(10) is false
                        + "  }\n" + "}"
                        ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method mm", 7
                        );
    }

    @Test
    public void testMethodAxioms2b() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ normal_behavior \n"
                        + "  //@ ensures \\result == (0 < i < 10);\n" 
                        + "  //@ pure\n"
                        + "  //@ model public boolean m(int i);\n"

                        + "  //@ pure\n" 
                        + "  public void mm() {\n"
                        + "  //@ assert (\\forall int k; 3 < k < 10; m(k));\n" // OK
                        + "  }\n" + "}"
                        );
    }

    @Test 
    public void testNullityAndConstructors() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  private /*@ spec_public */ char[] o; \n"
                        + "  \n" 
                        + "  //@ assignable \\everything;\n "
                        + "  public TestJava(final char /*@ non_null */ [] the_array) {\n"
                        + "      o = new char[the_array.length]; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testNullityAndConstructors2() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  private /*@ spec_public */ char[] o; \n"
                        + "  \n" 
                        + "  //@ assignable \\everything;\n "
                        + "  public TestJava(final char  /*@ non_null */[] the_array) {\n"
                        + "      o = new char[the_array.length]; //@ assert o != null;\n"
                        +"  //@ show the_array instanceof char[], o instanceof char[], the_array.length;\n"
                        + "      System.arraycopy(the_array, 0, o, 0, the_array.length); \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test 
    public void testNullityAndConstructors3() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                    "package tt; \n" 
                            + "public class TestJava  { \n" 
                            + "  private /*@ spec_public */ char[] o; \n"
                            + "  private /*@ spec_public */ int[] oo; \n" 
                            + "  \n" 
                            + "  //@ assignable \\everything;\n "
                            + "  public TestJava(final char /*@ non_null */ [] the_array) {\n"
                            + "      o = the_array; \n" 
                            + "  }\n" 
                            + "}"
                    ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (NullField) in method TestJava", 36
                    );
    }

    @Test
    public void testArrayLength() {
        addOptions("-nonnullByDefault");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public void m(final byte[] array) {\n"
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testArrayLength2() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  //@ requires k >= 0;\n"
                        + "  public void m(int k) {\n"
                        + "      short[] array = new short[k]; \n" 
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "      //@ assert array.length == k; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testArrayLength3() {
        addOptions("--nonnull-by-default","--method=m");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  long[] array;\n"
                        + "  public void m() {\n"
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "  }\n" 
                        + "}"
                );
    }

    @Test
    public void testArrayLength4() {
        addOptions("--nonnull-by-default","--method=m");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  public void m() {\n"
                        + "      char[] array = mm(); \n" 
                        + "      //@ assert array.length >= 0; \n" 
                        + "      //@ assert array.length <= Integer.MAX_VALUE; \n" 
                        + "  }\n" 
                        + "  public abstract char[] mm();\n" 
                        + "}"
                );
    }

    @Test
    public void testVarargs() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);\n"
                        + "  public void mm(int... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(new int[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(new int[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test
    public void testVarargsX() {
        addOptions("--nonnull-by-default");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0); requires n == -2;\n"
                        + "  public void mm(int n, int... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(-2); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(-2,1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-2,-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(-2,1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-2,-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(-2,new int[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(-2,new int[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test
    public void testVarargs2() {
        addOptions("-nonnullByDefault");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);\n"
                        + "  public void mm(Integer... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(new Integer[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(new Integer[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test
    public void testVarargs2X() {
        addOptions("-nonnullByDefault");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  //@ requires (\\forall int i; 0 <= i && i < args.length; args[i] >= 0);"
                        + "      requires n == -2;\n"
                        + "  public void mm(int n, Integer... args) {  }\n"
                        + "  public void m0() {\n"
                        + "      mm(-2); \n" 
                        + "  }\n" 
                        + "  public void m1() {\n"
                        + "      mm(-2,1); \n" 
                        + "  }\n" 
                        + "  public void m1b() {\n"
                        + "      mm(-2,-1); \n" 
                        + "  }\n" 
                        + "  public void m2() {\n"
                        + "      mm(-2,1,2); \n" 
                        + "  }\n" 
                        + "  public void m2b() {\n"
                        + "      mm(-2,-1,2); \n" 
                        + "  }\n" 
                        + "  public void m3() {\n"
                        + "      mm(-2,new Integer[]{1,2}); \n" 
                        + "  }\n" 
                        + "  public void m3b() {\n"
                        + "      mm(-2,new Integer[]{1,-2}); \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Precondition) in method m1b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Precondition) in method m2b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Precondition) in method m3b",9
                ,"/tt/TestJava.java:4: verify: Associated declaration",15
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: (\\forall int i; 0 <= i && i < args.length; args[i] >= 0)",16
                );
    }

    @Test // Incorrect syntax for \lbl produced an exception, but I could not reproduce that behavior here
    public void testLblError() {
        expectedExit = 1;
        addOptions("-nonnullByDefault");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public abstract class TestJava  { \n" 
                        + "  public void m0(int i, int j) {\n"
                        + "      //@ assert (\\lbl I i) + \\lbl(J j) == 0; \n" 
                        + "  }\n" 
                        + "}"
                        ,"/tt/TestJava.java:4: error: Missing comma or right parenthesis or otherwise ill-formed expression",38
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
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int j; \n"
                        + "  //@ ensures j >= 0; \n"
                        + "  public void m0(int i, Object o) {\n"
                        + "      j = -1; \n" 
                        + "  }\n" 
                        + "}"
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition) in method m0",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testFinalInvariant2() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int ii = mm(); \n"
                        +  " //@ ensures ii == 19; static_initializer "
                        
                        + "  //@ public final invariant ii == 19; \n"
                        
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        
                        + "  //@ public normal_behavior ensures \\result == 19; pure\n"
                        + "  public int mmm() { return ii; }"
                        + "}"
                );
    }

    @Test
    public void testFinalInvariant1() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int jj = 21; \n"
                        + "  public static final int ii = mm(); \n"
                        +  " //@ ensures ii == 19 && jj == 21; static_initializer "
                        
                        + "  //@ public final invariant ii == 19; \n"
                        
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        
                        + "  //@ public normal_behavior ensures \\result == 21; pure\n"
                        + "  public int mmm() { return jj; }"
                        + "}"
                );
    }


    @Test
    public void testFinalInvariant3() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int ii = mm(); \n"
                        +  " //@ ensures ii == mm(); static_initializer "
                        
                        + "  //@ public final invariant ii == 19; \n"
                        
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        
                        + "  //@ public normal_behavior ensures \\result == 19; pure\n"
                        + "  public int mmm() { return ii; }"
                        + "}"
                );
    }

    @Test
    public void testFinalInvariant() { // FIXME - determine why this works without the commented out errors
        expectedExit = 0;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static final int ii = mm(); \n"
                        + "  //@ public final invariant ii == 19; \n"
                        + "  //@ public normal_behavior ensures \\result == 10 + 9; pure\n"
                        + "  public static int mm() { return 19; }"
                        + "}"
                        ,"/tt/TestJava.java:3: warning: Use a static_initializer clause to specify the values of static final fields: tt.TestJava.ii (translating tt.TestJava.TestJava())",27
                        ,"/tt/TestJava.java:3: warning: Use a static_initializer clause to specify the values of static final fields: tt.TestJava.ii (translating tt.TestJava.mm())",27
//                        ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (InvariantExit) in method TestJava",8
//                        ,"/tt/TestJava.java:4: verify: Associated declaration",20
                                );
    }

    @Test
    public void testEnumStaticInitializer() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public enum TestJava  { \n" 
                        + "    A(1), B(2), C(3);   private TestJava(int i) {bit = i; }\n"
                        + "    private int bit;\n"
                        + "    static /*@ spec_public */ private int num = 10;\n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   ensures num == 10; \n"
                        + "  //@   ensures A.bit == 1; \n"
                        + "  //@   ensures B.bit == 2; \n"
                        + "  //@ static_initializer \n"
                        + "  public void m() {}"
                        + "}\n"
                        ,"/tt/TestJava.java:8: error: An identifier with private visibility may not be used in a ensures clause with public visibility",18
                        ,"/tt/TestJava.java:9: error: An identifier with private visibility may not be used in a ensures clause with public visibility",18
                        );
    }

    @Test
    public void testEnumStaticInitializer2() {
        expectedExit = 0;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public enum TestJava  { \n" 
                        + "    A(1), B(2), C(3);   private TestJava(int i) {bit = i; }\n"
                        + "    /*@ spec_public */ private int bit;\n"
                        + "    static /*@ spec_public */ private int num = 10;\n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   ensures num == 10; \n"
                        + "  //@   ensures A.bit == 1; \n"
                        + "  //@   ensures B.bit == 2; \n"
                        + "  //@ static_initializer \n"
                        + "  public void m() {}"
                        + "}\n"
                        );
    }
    
    @Test
    public void testNonNullElements() {
        expectedExit = 0;
        addOptions("-code-math=bigint");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires \\nonnullelements(arr); \n"
                        + "  public static void m( Key... arr) {\n"
                        + "     int s = 0;\n"
                        + "     for (Key i: arr) {\n"
                        + "        s = s + i.k;\n"
                        + "     }\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test // tests show statement; watch out for nondeterministic behavior
    public void testShowStatementESC() {
        expectedExit = 0;
        addOptions("--code-math=java","--method=m","--esc-max-warnings=1");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires i <= 1 && j >= 0; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i, j+1;\n"
                        + "     int k = i+j;\n"
                        + "     //@ show k;\n"
                        + "     //@ assert k > 0;\n"
                        + "     int m = i-j;\n"
                        + "     //@ show m,k;\n"
                        + "     //@ assert m >= 0;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:7: verify: Show statement expression i has value 0",15
                        ,"/tt/TestJava.java:7: verify: Show statement expression j + 1 has value 2",18
                        ,"/tt/TestJava.java:9: verify: Show statement expression k has value 1",15
                        ,"/tt/TestJava.java:12: verify: Show statement expression m has value ( - 1 )",15
                        ,"/tt/TestJava.java:12: verify: Show statement expression k has value 1",17
                        ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assert) in method m",10
                        );
    }

    @Test
    public void testShowStatement() {
        expectedExit = 0;
        addOptions("--lang=jml");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires true; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:7: warning: [strict-jml] The show statement construct is an OpenJML extension to JML and not allowed under --lang=jml",10
                  ); 
    }

    @Test
    public void testShowStatementErrors() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires true; \n"
                        + "  public static void m(int i, int j) {\n"
                        + "     //@ show i;\n"
                        + "     //@ show ijk\n"  // ERROR
                        + "     //@ show i ijk;\n" // ERROR
                        + "     //@ show;\n"     
                        + "     //@ show ijk\n"  // ERROR
                        + "     //@ show %;\n"   // ERROR
                        + "     //@ show ijk show ijk;\n"   // ERROR
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:8: error: Incorrectly formed or terminated show statement near here -- perhaps a missing semicolon",18
                        ,"/tt/TestJava.java:9: error: Incorrectly formed or terminated show statement near here",17
                        ,"/tt/TestJava.java:11: error: Incorrectly formed or terminated show statement near here -- perhaps a missing semicolon",18
                        ,"/tt/TestJava.java:12: error: illegal start of expression",15
                        ,"/tt/TestJava.java:13: error: Incorrectly formed or terminated show statement near here -- perhaps a missing semicolon",18
                        );
    }

    @Test
    public void testArrayCopy() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires k != null && \\nonnullelements(k) && \\elemtype(\\typeof(k)) <:= \\type(Key); \n"
                        + "  public static void m(Key[] k) {\n"
                        + "  //@   assert k != null; \n"
                        + "     Key[] kk = java.util.Arrays.copyOfRange(k,0,k.length);\n"
                        + "     //@ assert kk != null;\n"
                        + "     //@ assert \\nonnullelements(kk);\n"
                        + "     //@ assert \\elemtype(\\typeof(kk)) == \\type(Key);\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testArrayCopy2() {
        helpEsc("tt.TestJava",
                          "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public static class Key { public int k; } \n"
                        + "  //@ public normal_behavior \n"
                        + "  //@   requires k != null && \\nonnullelements(k) && \\elemtype(\\typeof(k)) <:= \\type(Key); \n"
                        + "  public static void m(Key[] k) {\n"
                        + "     Key[] kk = java.util.Arrays.<Key>copyOfRange(k,0,k.length);\n"
                        + "     //@ assert kk != null;\n"
                        + "     //@ assert \\nonnullelements(kk);\n"
                        + "     //@ assert \\elemtype(\\typeof(kk)) == \\type(Key);\n"
                        + "  }\n"
                        + "}\n"
                        );
    }


    @Test
    public void testDuplicateGhost() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                          "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public void m() {\n"
                        + "  //@ ghost int k = 1;\n"
                        + "  //@ ghost int k = 2;\n"
                        + "  }\n"
                        + "}\n"
                 ,"/tt/TestJava.java:5: error: variable k is already defined in method m()",17
                        );
    }

    @Test
    public void testChainedCompare() {
    	expectedExit = 1;
        helpEsc("tt.TestJava",
                          "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public void m() {\n"
                        + "  //@ ghost int i = 2;\n"
                        + "  //@ check  0 <= i < 10 < 12;\n"
                        + "  //@ set i = 10;\n"
                        + "  //@ check  !(0 <= i < 10);\n"
                        + "  //@ check  0 <= i < 11 == 2 <= i <= 12;\n"
                        + "  //@ check  11 >= i+1 > 1 == 12 >= i > 2;\n"
                        + "  //@ check  11 >= i+1 < 12;\n" // ERROR
                        + "  //@ check  11 >= i+1 <= 12 == true;\n" // ERROR
                        + "  //@ check  11 > i+1 < 12;\n" // ERROR
                        + "  //@ check  11 > i+1 <= 12 == true;\n" // ERROR
                        + "  //@ check  11 >= i+1 > 1 != 12 <= i <= 22;\n" // OK but bad style
                        + "  //@ check  11 < i+1 > 12;\n" // ERROR
                        + "  //@ check  11 < i+1 >= 12;\n" // ERROR
                        + "  //@ check  11 <= i+1 > 12;\n" // ERROR
                        + "  //@ check  11 <= i+1 >= 12;\n" // ERROR
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:10: error: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:11: error: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:12: error: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:13: error: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:15: error: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:16: error: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:17: error: Cannot chain comparisons that are in different directions",17
                        ,"/tt/TestJava.java:18: error: Cannot chain comparisons that are in different directions",17
                        );
    }

    @Test
    public void testAllowForbid2() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  //@ signals_only \\nothing;\n"
                        + "  public void m(/*@ nullable */ TestJava t) {\n"
                        + "    int i = t.iii //@ allow NullPointerException; \n"
                        + "    ;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (ExceptionList) in method m",14
                        ,"/tt/TestJava.java:4: verify: Associated declaration",7
                        );
    }

    @Test
    public void testAllowForbid3() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t) {\n"
                        + "    int i = t.iii //@ forbid NullPointerException; \n"
                        + "    ;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m",14
                        );
    }

    @Test
    public void testAllowForbid5() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "    int i = t.iii; //@ ignore NullPointerException; \n"
                        + "    i = t.iii;\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testAllowForbid4() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "    int i = t.iii; //@ ignore java.lang.XX; \n"
                        + "    i = t.iii;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:5: error: cannot find symbol\n" + 
                                                "  symbol:   class XX\n" + 
                                                "  location: package java.lang",41
                        ,"/tt/TestJava.java:5: error: cannot find symbol\n" +  // TODO: It is a OpenJDK problem that this error message is repeated
                                                "  symbol:   class XX\n" + 
                                                "  location: package java.lang",41
                        );
    }

    @Test
    public void testAllowForbid6() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "    int i = t.iii;\n"
                        + "    i = t.iii;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method m", 14
                        );
    }

    @Test
    public void testAllowForbid7() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  //@ signals_only NullPointerException;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "    int i = t.iii;\n"  // OK NullPointerException permitted
                        + "    i = t.iii;\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testAllowForbid8() {
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "    try { \n"
                        + "      int i = t.iii;\n"  // OK NullPointerException permitted
                        + "      i = t.iii;\n"
                        + " } catch (NullPointerException e) {}\n"
                        + "  }\n"
                        + "}\n"
                        );
    }

    @Test
    public void testAllowForbid9() {
        addOptions("--check-feasibility=reachable");
        helpEsc("tt.TestJava",
                "package tt; \n" 
                        + "public class TestJava  { \n" 
                        + "  public int iii;\n"
                        + "  public void m(/*@ nullable */ TestJava t, /*@ nullable */ TestJava tt) {\n"
                        + "     //@ assume t == null;\n"
                        + "    int i = t.iii; //@ ignore NullPointerException; \n"
                        + "    //@ reachable; // ERROR"
                        + "    i = t.iii;\n"
                        + "  }\n"
                        + "}\n"
                        ,"/tt/TestJava.java:7: verify: There is no feasible path to program point at reachable statement in method tt.TestJava.m(tt.@org.jmlspecs.annotation.Nullable TestJava,tt.@org.jmlspecs.annotation.Nullable TestJava)",9
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
    			"package tt; /*@ non_null_by_default */ public class C {\n"
    			+ "    //@ public model \\datagroup g;\n"
    			+ "}\n"
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
        helpEsc("tt.TestJava","package tt; \n"
                +"public class TestJava { \n"
                +"  //@ accessible \\nothing;\n"
                +"  int m() { return i; }\n"
                +"  int i;\n"
                +"}"
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Accessible) in method m: i",20
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
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
                "package tt; \n" 
                        + "/*@ code_java_math spec_java_math*/ public class TestJava { \n" 
                        + "  static public int i;\n"
                        + "  //@ assigns i;\n" 
                        + "  //@ ensures i == \\old(i)+2;\n"
                        + "  public static void bok() { x: i = i + 1; /*@ assert i == i@x + 1 && i == (i+1)@x; */ i = i + 1;}\n" 
                        + "  //@ assigns i;\n"
                        + "  //@ ensures i == \\old(i+1);\n" 
                        + "  public static void bbad() { i = i - 1; /*@ assert i == i@x + 1; */ }\n" // ERROR
                        + "  //@ assigns i;\n" 
                        + "  public void bok2() { x: i = i + 1; /*@ assert i == this.i@x + 1; */ i = i + 1;}\n" 
                        + "  //@ requires a.length > 10 && a[0] >= 0;\n" 
                        + "  //@ assigns i;\n" 
                        + "  public static void bok3(int[] a) { x: i = i + 1; /*@ assert a[0]@x > -1; */ i = i + 1;}\n" 
                        + "}"
                        ,"/tt/TestJava.java:9: error: There is no label named x", 60
                );
    }

}
