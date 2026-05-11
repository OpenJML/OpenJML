package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(org.openjml.runners.ParameterizedWithNames.class)
public class escrecord extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--check-feasibility=none");
        expectedExit = 0;
    }

    // =======================================================================
    //  Category 1: Basic record field assignment — the core Bug C fix
    // =======================================================================

    /** Compact constructor with non_null fields verified by requireNonNull.
     *  The ensures clauses require the fix: ESC must know this.first == first
     *  and this.last == last at the end of the compact constructor body. */
    @Test
    public void testRecordCompactNonNull() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Name(/*@ non_null */ String first, /*@ non_null */ String last) {
                        //@ ensures this.first() == first;
                        //@ ensures this.last() == last;
                        Name {
                            java.util.Objects.requireNonNull(first);
                            java.util.Objects.requireNonNull(last);
                        }
                    }
                }
                """);
    }

    /** Primitive record fields — should always verify cleanly. */
    @Test
    public void testRecordPrimitiveFields() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    record Point(int x, int y) {}
                }
                """);
    }

    /** Record with a single primitive field. */
    @Test
    public void testRecordSinglePrimitive() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    record Wrapper(int value) {}
                }
                """);
    }

    /** Generated (canonical) constructor with non_null reference field. */
    @Test
    public void testRecordGeneratedConstructorNonNull() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Box(/*@ non_null */ Object item) {}
                }
                """);
    }

    /** Compact constructor with empty body — fields should still be assigned.
     *  The ensures clauses require the fix: ESC must synthesize the implicit
     *  this.a == a and this.b == b assumptions after the (empty) body. */
    @Test
    public void testRecordCompactEmptyBody() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Pair(/*@ non_null */ Object a, /*@ non_null */ Object b) {
                        //@ ensures this.a() == a;
                        //@ ensures this.b() == b;
                        Pair {}
                    }
                }
                """);
    }

    /** Mixed primitive and reference fields. */
    @Test
    public void testRecordMixedFields() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Entry(/*@ non_null */ String key, int value) {
                        //@ ensures this.key() == key;
                        //@ ensures this.value() == value;
                        Entry {
                            java.util.Objects.requireNonNull(key);
                        }
                    }
                }
                """);
    }

    // =======================================================================
    //  Category 2: Compact body interactions
    // =======================================================================

    /** Compact constructor that validates with requireNonNull. */
    @Test
    public void testRecordCompactRequireNonNull() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Config(/*@ non_null */ String name, int timeout) {
                        //@ ensures this.name() == name;
                        //@ ensures this.timeout() == timeout;
                        Config {
                            java.util.Objects.requireNonNull(name, "name must not be null");
                            if (timeout < 0) throw new IllegalArgumentException("timeout < 0");
                        }
                    }
                }
                """);
    }

    /** Compact body that reassigns a parameter (normalizing). */
    @Test
    public void testRecordCompactParamTransform() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Label(/*@ non_null */ String text) {
                        Label {
                            java.util.Objects.requireNonNull(text);
                            text = text.trim();
                        }
                    }
                }
                """);
    }

    /** Compact constructor with range validation on primitives. */
    @Test
    public void testRecordCompactRangeValidation() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    record Range(int lo, int hi) {
                        //@ ensures this.lo() == lo;
                        //@ ensures this.hi() == hi;
                        Range {
                            if (lo > hi) throw new IllegalArgumentException();
                        }
                    }
                }
                """);
    }

    // =======================================================================
    //  Category 3: Record method field access
    // =======================================================================

    /** Record accessor methods can assume field invariants. */
    @Test
    public void testRecordMethodFieldAccess() {
        helpEsc("A", """
                import org.jmlspecs.annotation.*;
                class A {
                    record Name(/*@ non_null */ String first, /*@ non_null */ String last) {
                        Name {
                            java.util.Objects.requireNonNull(first);
                            java.util.Objects.requireNonNull(last);
                        }
                        //@ ensures \\result != null;
                        /*@ pure */ String fullName() {
                            return first + " " + last;
                        }
                    }
                }
                """);
    }

    // =======================================================================
    //  Category 4: Generic type parameters on records
    // =======================================================================

    /** Record with a generic type parameter — nullable reference. */
    @Test
    public void testRecordGenericNullable() {
        helpEsc("A", """
                class A {
                    record Container<T>(/*@ nullable */ T value) {}
                }
                """);
    }

    /** Record with bounded generic type parameter. */
    @Test
    public void testRecordGenericBounded() {
        helpEsc("A", """
                class A {
                    record NumBox<N extends Number>(/*@ non_null */ N num) {
                        NumBox {
                            java.util.Objects.requireNonNull(num);
                        }
                    }
                }
                """);
    }

    /** Record with multiple generic type parameters. */
    @Test
    public void testRecordMultipleGenerics() {
        helpEsc("A", """
                class A {
                    record Pair<A1, B1>(/*@ nullable */ A1 first, /*@ nullable */ B1 second) {}
                }
                """);
    }

    // =======================================================================
    //  Category 5: Records with JML annotations
    // =======================================================================

    /** Record with a JML invariant on a field. */
    @Test
    public void testRecordInvariant() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    record Positive(int value) {
                        //@ private invariant value > 0;
                        Positive {
                            if (value <= 0) throw new IllegalArgumentException();
                        }
                    }
                }
                """);
    }

    /** Record with ensures on the compact constructor. */
    @Test
    public void testRecordEnsures() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record NonEmpty(int kkk, int mmm) {
                        //@ normal_behavior
                        //@ ensures this.kkk == 10;
                        //@ ensures this.mmm == mmm;
                        //@ pure
                        NonEmpty {
                            kkk = 10;
                        }
                    }
                }
                """);
    }

    /** Record with ensures on the compact constructor. */
    @Test
    public void testRecordEnsuresError() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record NonEmpty(int kkk, int mmm) {
                        //@ normal_behavior
                        //@ ensures this.kkk == 10;
                        //@ ensures this.mmm == 100;
                        //@ pure
                        NonEmpty {
                            kkk = 10;
                        }
                    }
                }
                """
                ,"/tt/A.java:9: verify: The prover cannot establish an assertion (Postcondition) in method NonEmpty", 9
                ,"/tt/A.java:7: verify: Associated declaration", 13
                );
    }

    /** Pure record method. */
    @Test
    public void testRecordPureMethod() {
        helpEsc("A", """
                import org.jmlspecs.annotation.*;
                class A {
                    record IntPair(int x, int y) {
                        //@ requires Integer.MIN_VALUE <= x + y <= Integer.MAX_VALUE;
                        /*@ pure */ int sum() { return x + y; }
                    }
                }
                """);
    }

    @Test
    public void testRecordCustomGetter() {
        helpEsc("A", """
                import org.jmlspecs.annotation.*;
                class A {
                    record IntPair(int x, int y) {
                        //@ ensures \\result == 10;
                        /*@ pure */ public int x() { return 10; }
                    }
                }
                """);
    }

    @Test
    public void testRecordCustomGetterError() {
        helpEsc("A", """
                import org.jmlspecs.annotation.*;
                class A {
                    record IntPair(int x, int y) {
                        //@ ensures \\result == x; // ERROR
                        /*@ pure */ public int x() { return 10; }
                    }
                }
                """
                ,"/A.java:5: verify: The prover cannot establish an assertion (Postcondition) in method x", 38
                ,"/A.java:4: verify: Associated declaration", 13
                );
    }

    // =======================================================================
    //  Category 6: Sealed interfaces with records
    // =======================================================================

    /** Simple sealed interface with record implementations. */
    @Test
    public void testRecordSealedInterface() {
        helpEsc("A", """
                import org.jmlspecs.annotation.*;
                class A {
                    sealed interface Shape permits Circle, Rect {}
                    record Circle(double radius) implements Shape {
                        Circle {
                            if (radius < 0) throw new IllegalArgumentException();
                        }
                    }
                    record Rect(double w, double h) implements Shape {
                        Rect {
                            if (w < 0 || h < 0) throw new IllegalArgumentException();
                        }
                    }
                }
                """);
    }

    /** Record implementing multiple interfaces. */
    @Test
    public void testRecordMultipleInterfaces() {
        helpEsc("A", """
                class A {
                    interface Named { String name(); }
                    record Person(/*@ nullable */ String name, int age) implements Named {}
                }
                """);
    }

    // =======================================================================
    //  Category 7: Regression — regular classes should be unaffected
    // =======================================================================

    /** Regular class with constructor and non_null field — not a record. */
    @Test
    public void testRegularClassUnaffected() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    /*@ spec_public non_null */ String name;
                    //@ ensures this.name == n;
                    public A(/*@ non_null */ String n) {
                        this.name = n;
                    }
                }
                """);
    }

    /** Regular class with nullable field — unchanged semantics. */
    @Test
    public void testRegularClassNullableField() {
        helpEsc("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    /*@ nullable */ String label;
                    public A() {
                        this.label = null;
                    }
                }
                """);
    }

    /** Static fields in records — should NOT be affected by the fix. */
    @Test
    public void testRecordStaticFieldUnaffected() {
        helpEsc("A", """
                class A {
                    record Config(int value) {
                        static final int DEFAULT = 42;
                    }
                }
                """);
    }

    /** Record with no fields (empty record). */
    @Test
    public void testRecordNoFields() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    record Empty() {}
                }
                """);
    }

    /** Multiple records in same file. */
    @Test
    public void testMultipleRecordsInFile() {
        helpEsc("A", """
                import org.jmlspecs.annotation.*;
                class A {
                    record Ok<T>(/*@ non_null */ T value) {
                        Ok { java.util.Objects.requireNonNull(value); }
                    }
                    record Err<E>(/*@ non_null */ E error) {
                        Err { java.util.Objects.requireNonNull(error); }
                    }
                }
                """);
    }
}
