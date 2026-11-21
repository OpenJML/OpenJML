package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** ESC checks of instance field initializers (#774): each class has a passing initializer, then a failing one,
 *  so the passing one is checked before any failure adds assumptions. Static initializers are #1152. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escInitializers extends EscBase {

    @Test
    public void testFinalDiv() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  final int good = 10 / (z == 0 ? 1 : z);
                  final int bad = 10 / z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",22
                );
    }

    @Test
    public void testFinalPre() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  final int good = pos(1);
                  final int bad = pos(0);
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition: /tt/TestJava.java:6:) in method TestJava",22
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:8:",26
                ,"/tt/TestJava.java:5: verify: Precondition conjunct is false: i > 0",18
                );
    }

    @Test
    public void testFinalNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  final int good = nul == null ? 0 : nul.hashCode();
                  final int bad = nul.hashCode();
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method TestJava",22
                );
    }

    @Test
    public void testFinalOvf() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  final int good = z / 2 + 1;
                  final int bad = Integer.MAX_VALUE + z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method TestJava: overflow in int sum",37
                );
    }

    @Test
    public void testFinalNegSize() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  final int good = new int[z < 0 ? 0 : z].length;
                  final int bad = new int[z].length;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNegativeSize) in method TestJava",27
                );
    }

    @Test
    public void testFinalNonNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  final Object good = new Object();
                  final Object bad = nul;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullField) in method TestJava",16
                );
    }

    @Test
    public void testPlainDiv() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  int good = 10 / (z == 0 ? 1 : z);
                  int bad = 10 / z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",16
                );
    }

    @Test
    public void testPlainPre() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  int good = pos(1);
                  int bad = pos(0);
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition: /tt/TestJava.java:6:) in method TestJava",16
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:8:",26
                ,"/tt/TestJava.java:5: verify: Precondition conjunct is false: i > 0",18
                );
    }

    @Test
    public void testPlainNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  int good = nul == null ? 0 : nul.hashCode();
                  int bad = nul.hashCode();
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method TestJava",16
                );
    }

    @Test
    public void testPlainOvf() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  int good = z / 2 + 1;
                  int bad = Integer.MAX_VALUE + z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method TestJava: overflow in int sum",31
                );
    }

    @Test
    public void testPlainNegSize() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  int good = new int[z < 0 ? 0 : z].length;
                  int bad = new int[z].length;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNegativeSize) in method TestJava",21
                );
    }

    @Test
    public void testPlainNonNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  Object good = new Object();
                  Object bad = nul;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (NullField) in method TestJava",10
                );
    }

    @Test
    public void testGhostFinalDiv() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost final int good = 10 / (z == 0 ? 1 : z);
                  //@ ghost final int bad = 10 / z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",32
                );
    }

    @Test
    public void testGhostFinalPre() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost final int good = pos(1);
                  //@ ghost final int bad = pos(0);
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition: /tt/TestJava.java:6:) in method TestJava",32
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:8:",26
                ,"/tt/TestJava.java:5: verify: Precondition conjunct is false: i > 0",18
                );
    }

    @Test
    public void testGhostFinalNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost final int good = nul == null ? 0 : nul.hashCode();
                  //@ ghost final int bad = nul.hashCode();
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method TestJava",32
                );
    }

    @Test
    public void testGhostFinalOvf() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost final int good = z / 2 + 1;
                  //@ ghost final int bad = Integer.MAX_VALUE + z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method TestJava: overflow in int sum",47
                );
    }

    @Test
    public void testGhostDiv() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost int good = 10 / (z == 0 ? 1 : z);
                  //@ ghost int bad = 10 / z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",26
                );
    }

    @Test
    public void testGhostPre() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost int good = pos(1);
                  //@ ghost int bad = pos(0);
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Precondition: /tt/TestJava.java:6:) in method TestJava",26
                ,"/tt/TestJava.java:6: verify: Associated declaration: /tt/TestJava.java:8:",26
                ,"/tt/TestJava.java:5: verify: Precondition conjunct is false: i > 0",18
                );
    }

    @Test
    public void testGhostNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost int good = nul == null ? 0 : nul.hashCode();
                  //@ ghost int bad = nul.hashCode();
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method TestJava",26
                );
    }

    @Test
    public void testGhostOvf() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  static /*@ nullable */ Object nul;
                  //@ requires i > 0;
                  static /*@ pure */ int pos(int i) { return i; }
                  //@ ghost int good = z / 2 + 1;
                  //@ ghost int bad = Integer.MAX_VALUE + z;
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method TestJava: overflow in int sum",41
                );
    }

    // A failing initializer is reported for each constructor, but not for one that calls this(...)
    @Test
    public void testConstructors() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  int bad = 10 / z;
                  public TestJava() {}
                  public TestJava(int i) {}
                  public TestJava(boolean b) { this(); }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",16
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",16
                );
    }

    // Verifying one constructor reports the failure in that run
    @Test
    public void testOneConstructor() {
        main.addOptions("--method=TestJava(int)");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  int bad = 10 / z;
                  public TestJava() {}
                  public TestJava(int i) {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",16
                );
    }

    // An instance initializer block is checked like a field initializer
    @Test
    public void testBlock() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static int z;
                  int k;
                  { k = 10 / (z == 0 ? 1 : z); }
                  { k = 10 / z; }
                  public TestJava() {}
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method TestJava",12
                );
    }
}
