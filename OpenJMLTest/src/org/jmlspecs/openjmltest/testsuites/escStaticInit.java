package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** ESC of static initialization through the synthetic method <clinit> (#1152): static fields start with their
 *  default values, the static initializers and static blocks run in textual order with full checking, and at the
 *  end the static invariants, non-null static fields and the static_initializer clause are checked. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escStaticInit extends EscBase {

    @Test
    public void testFieldInitializer() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static int good = 10 / (z == 0 ? 1 : z);
                  static int bad = 10 / z;
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method <clinit>",23
                );
    }

    @Test
    public void testBlock() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static int k;
                  static { k = 10 / (z == 0 ? 1 : z); }
                  static { k = 10 / z; }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method <clinit>",19
                );
    }

    @Test
    public void testGhost() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  //@ static ghost int good = 10 / (z == 0 ? 1 : z);
                  //@ static ghost int bad = 10 / z;
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method <clinit>",33
                );
    }

    @Test
    public void testPrecondition() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  static int good = pos(1);
                  static int bad = pos(0);
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Precondition: /tt/TestJava.java:4:) in method <clinit>",23
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:6:",26
                ,"/tt/TestJava.java:3: verify: Precondition conjunct is false: i > 0",18
                );
    }

    // An out-of-range cast in a compile-time constant (#861)
    @Test
    public void testConstantCast() {
        main.addOptions("--code-math=safe");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static final short GOOD = (short)30000;
                  static final short BAD = (short)40000;
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method <clinit>",28
                );
    }

    // Static fields start with their default values, so a non-null field must be set
    @Test
    public void testNonNullUnset() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static Object good = new Object();
                  static Object bad;
                  static void m() {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (NullField) in method <clinit>",17
                );
    }

    // A forward reference reads the default value
    @Test
    public void testForwardReference() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int a = TestJava.b + 1;
                  static int b = 7;
                  //@ static invariant a == 1 && b == 7;
                }
                """
                );
    }

    @Test
    public void testStaticInvariant() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static int k = 5;
                  //@ static invariant k == 5;
                  //@ static invariant z == 3;
                }
                """
                ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (InvariantExit: /tt/TestJava.java:6:) in method <clinit>",8
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:2:",14
                );
    }

    @Test
    public void testStaticInitializerHolds() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int k;
                  //@ ensures k == 10;
                  //@ static_initializer
                  static { k = 10; }
                }
                """
                );
    }

    @Test
    public void testStaticInitializerFalse() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int k = 5;
                  //@ ensures false;
                  //@ static_initializer
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Postcondition: /tt/TestJava.java:4:) in method <clinit>",7
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:5:",7
                );
    }

    // The requires clause of a static_initializer is assumed at the start of <clinit>
    @Test
    public void testStaticInitializerRequires() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class Other { public static int q; }
                public class TestJava {
                  public static int k = 10 / Other.q;
                  //@ requires Other.q != 0;
                  //@ ensures k == 10 / Other.q;
                  //@ static_initializer
                }
                """
                );
    }

    // The static_initializer clause describes the state at the end of static initialization; a method may run
    // after other code has changed k, so it may not assume k == 5
    @Test
    public void testStaticInitializerNotAssumedLater() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int k = 5;
                  //@ ensures k == 5;
                  //@ static_initializer

                  //@ assignable k;
                  public static void inc() { k++; }
                  public static void m() {
                    //@ assert k == 5;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method inc: overflow in int sum",31
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    // A static_initializer fact about final static fields, read through deterministic methods, cannot change after
    // static initialization, so it becomes an assumed static invariant (#1152)
    @Test
    public void testStaticInitializerInferredInvariant() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class P {
                  public final int v;
                  //@ ensures this.v == v;
                  //@ pure
                  public P(int v) { this.v = v; }
                  //@ ensures \\result == v;
                  //@ pure helper
                  public int get() { return v; }
                }
                public class TestJava {
                  public static final P P5 = new P(5);
                  public static int k = 5;
                  //@ public normal_behavior
                  //@   ensures P5 != null && P5.get() == 5;
                  //@   ensures k == 5;
                  //@ static_initializer

                  public static void m() {
                    //@ assert P5.get() == 5;
                    //@ assert k == 5;
                  }
                }
                """
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    // A fact that calls a method that is not a helper is not inferred (the method's axioms are guarded by its class's
    // invariants); a warning says so
    @Test
    public void testStaticInitializerNonHelperWarning() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class P {
                  public final int v;
                  //@ public normal_behavior
                  //@   ensures this.v == v;
                  //@ pure
                  public P(int v) { this.v = v; }
                  //@ public normal_behavior
                  //@   ensures \\result == v;
                  //@ pure
                  public int get() { return v; }
                }
                public class TestJava {
                  public static final P P5 = new P(5);
                  //@ public normal_behavior
                  //@   ensures P5 != null && P5.get() == 5;
                  //@ static_initializer

                  public static void m() {
                    //@ assert P5 != null;
                    //@ assert P5.get() == 5;
                  }
                }
                """
                ,"/tt/TestJava.java:16: warning: This static_initializer fact is not assumed as a static invariant, because get() is not a helper method",37
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    // A final instance field counts when read through final fields from a static final field; a non-final one does not
    @Test
    public void testStaticInitializerInferredInstanceField() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class Pt {
                  public final int x;
                  public int y;
                  public final /*@ nullable */ Pt next;
                  //@ public normal_behavior
                  //@   ensures this.x == x && this.y == 0 && this.next == next;
                  //@ pure
                  public Pt(int x, /*@ nullable */ Pt next) { this.x = x; this.next = next; }
                }
                public class TestJava {
                  public static final Pt ORIGIN = new Pt(0, new Pt(1, null));
                  //@ public normal_behavior
                  //@   ensures ORIGIN.x == 0 && ORIGIN.y == 0;
                  //@   ensures ORIGIN.next != null && ORIGIN.next.x == 1;
                  //@ static_initializer

                  public static void m() {
                    //@ assert ORIGIN.x == 0 && ORIGIN.next != null && ORIGIN.next.x == 1;
                    //@ assert ORIGIN.y == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    // A conditional case (with a requires) gives no invariant
    @Test
    public void testStaticInitializerConditionalNotInferred() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class Other { public static int q = 1; }
                public class TestJava {
                  public static final int K = 10 / Other.q;
                  //@ public normal_behavior
                  //@   requires Other.q == 1;
                  //@   ensures K == 10;
                  //@ static_initializer

                  public static void m() {
                    //@ assert K == 10;
                  }
                }
                """
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assert) in method m",9
                );
    }

    // A durable fact is a static invariant: <clinit> establishes it, methods assume it on entry and must restore it
    @Test
    public void testStaticInvariantAssumedLater() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static int k = 5;
                  //@ public static invariant k == 5;

                  //@ assignable k;
                  public static void inc() { k++; }
                  public static void m() {
                    //@ assert k == 5;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit: /tt/TestJava.java:4:) in method inc",22
                ,"/tt/TestJava.java:4: verify: Associated declaration: /tt/TestJava.java:7:",21
                );
    }

    // A static final field whose value is not a compile-time constant and that no static invariant mentions gets one
    // warning, however many methods use it; a constant, and a field mentioned in a static invariant, get none
    @org.junit.Ignore("the warning is disabled until the test suites are settled again")
    @Test
    public void testUndescribedStaticFinal() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public final static int C = 5;
                  public final static int D = C + 1;
                  public final static int[] A = new int[]{1, 2};
                  public final static Object B = new Object();
                  //@ public static invariant A.length == 2;
                  public static int m() { return A[0] + B.hashCode(); }
                  public static int n() { return A[1] + B.hashCode(); }
                }
                """
                ,"/tt/TestJava.java:6: warning: The static final field B is not mentioned in any static invariant, so methods can assume nothing about its value",30
                );
    }

    // The default frame of static initialization is C.*, the static fields of the class
    @Test
    public void testDefaultFrame() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class Other { public static int q; }
                public class TestJava {
                  static int k = 1;
                  static int j;
                  static { k = 2; j = 3; Other.q = 3; }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable: /tt/TestJava.java:3:) in method <clinit>: Other.q",34
                ,"/tt/TestJava.java:3: verify: Associated declaration: /tt/TestJava.java:6:",8
                );
    }

    // An assignable clause of the static_initializer is the frame of static initialization; a private heading lets
    // the clause name non-public fields
    @Test
    public void testExplicitFrame() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int k = 1;
                  private static int j;
                  //@ private normal_behavior
                  //@   assignable k;
                  //@ static_initializer
                  static { k = 2; j = 3; }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable: /tt/TestJava.java:6:) in method <clinit>: j",21
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:8:",9
                );
    }

    // <clinit> can be selected like a method
    @Test
    public void testSelect() {
        main.addOptions("--method=tt.TestJava.<clinit>");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static int bad = 10 / z;
                  public static void m() { int i = 10 / z; }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method <clinit>",23
                );
    }
}
