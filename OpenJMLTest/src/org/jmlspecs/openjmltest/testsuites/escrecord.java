package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.MockJavaFileObject;

import com.sun.tools.javac.util.List;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(org.openjml.runners.ParameterizedWithNames.class)
public class escrecord extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--check-feasibility=none");
        expectedExit = 0;
    }

    /**
     * Compiles the given source and asserts that no internal JML/OpenJML error
     * occurred.
     */
    private void assertNoInternalError(String filename, String source) throws Exception {
        JavaFileObject f = new MockJavaFileObject(filename, source);
        main.compile(new String[]{}, List.of(f));
        String diags = diagnosticsToString(collector.getDiagnostics());
        assertFalse("Did not expect a catastrophic internal error:\n" + diags,
                diags.contains("A catastrophic JML internal error occurred"));
        assertFalse("Did not expect an internal JML error:\n" + diags,
                diags.contains("An internal JML error occurred"));
    }

    /**
     * Compiles and asserts zero verification warnings (clean pass).
     */
    private void assertCleanVerification(String qualifiedName, String source) {
        helpEsc(qualifiedName, source);
    }

    // =======================================================================
    //  Category 1: Basic record field assignment — the core Bug C fix
    // =======================================================================

    /** Compact constructor with non_null fields verified by requireNonNull. */
    @Test
    public void testRecordCompactNonNull() {
        assertCleanVerification("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Name(/*@ non_null */ String first, /*@ non_null */ String last) {
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
        assertCleanVerification("tt.A", """
                package tt;
                public class A {
                    record Point(int x, int y) {}
                }
                """);
    }

    /** Record with a single primitive field. */
    @Test
    public void testRecordSinglePrimitive() {
        assertCleanVerification("tt.A", """
                package tt;
                public class A {
                    record Wrapper(int value) {}
                }
                """);
    }

    /** Generated (canonical) constructor with non_null reference field. */
    @Test
    public void testRecordGeneratedConstructorNonNull() {
        assertCleanVerification("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Box(/*@ non_null */ Object item) {}
                }
                """);
    }

    /** Compact constructor with empty body — fields should still be assigned. */
    @Test
    public void testRecordCompactEmptyBody() {
        assertCleanVerification("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Pair(/*@ non_null */ Object a, /*@ non_null */ Object b) {
                        Pair {}
                    }
                }
                """);
    }

    /** Mixed primitive and reference fields. */
    @Test
    public void testRecordMixedFields() {
        assertCleanVerification("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Entry(/*@ non_null */ String key, int value) {
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
        assertCleanVerification("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record Config(/*@ non_null */ String name, int timeout) {
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
        assertCleanVerification("tt.A", """
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
        assertCleanVerification("tt.A", """
                package tt;
                public class A {
                    record Range(int lo, int hi) {
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
    public void testRecordMethodFieldAccess() throws Exception {
        assertNoInternalError("A.java", """
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
    public void testRecordGenericNullable() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    record Container<T>(/*@ nullable */ T value) {}
                }
                """);
    }

    /** Record with bounded generic type parameter. */
    @Test
    public void testRecordGenericBounded() throws Exception {
        assertNoInternalError("A.java", """
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
    public void testRecordMultipleGenerics() throws Exception {
        assertNoInternalError("A.java", """
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
        assertCleanVerification("tt.A", """
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
        assertCleanVerification("tt.A", """
                package tt;
                import org.jmlspecs.annotation.*;
                public class A {
                    record NonEmpty(/*@ non_null */ String text) {
                        //@ ensures text != null;
                        NonEmpty {
                            java.util.Objects.requireNonNull(text);
                        }
                    }
                }
                """);
    }

    /** Pure record method. */
    @Test
    public void testRecordPureMethod() throws Exception {
        assertNoInternalError("A.java", """
                import org.jmlspecs.annotation.*;
                class A {
                    record IntPair(int x, int y) {
                        /*@ pure */ int sum() { return x + y; }
                    }
                }
                """);
    }

    // =======================================================================
    //  Category 6: Sealed interfaces with records
    // =======================================================================

    /** Simple sealed interface with record implementations. */
    @Test
    public void testRecordSealedInterface() throws Exception {
        assertNoInternalError("A.java", """
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
    public void testRecordMultipleInterfaces() throws Exception {
        assertNoInternalError("A.java", """
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
        assertCleanVerification("tt.A", """
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
        assertCleanVerification("tt.A", """
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
    public void testRecordStaticFieldUnaffected() throws Exception {
        assertNoInternalError("A.java", """
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
        assertCleanVerification("tt.A", """
                package tt;
                public class A {
                    record Empty() {}
                }
                """);
    }

    /** Multiple records in same file. */
    @Test
    public void testMultipleRecordsInFile() throws Exception {
        assertNoInternalError("A.java", """
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
