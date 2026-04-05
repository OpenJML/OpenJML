package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.MockJavaFileObject;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.List;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escswitch extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--source", "21");
        addOptions("--enable-preview", "--enable-preview");
        addOptions("--check-feasibility=none");
        expectedExit = 0;
    }

    /**
     * Compiles the given source and asserts that no internal JML/OpenJML error
     * occurred.  Accepts a clean exit (0) or the known missing-prover message
     * when z3 is unavailable in the test environment.
     */
    private void assertNoInternalError(String filename, String source) throws Exception {
        assertNoInternalError(filename, source, null);
    }

    private void assertNoInternalError(String filename, String source, String method) throws Exception {
        if (method != null) addOptions("--method=" + method);
        JavaFileObject f = new MockJavaFileObject(filename, source);
        int ex = main.compile(new String[]{}, List.of(f)).exitCode;
        String diags = diagnosticsToString(collector.getDiagnostics());
        assertFalse("Did not expect a catastrophic internal error:\n" + diags,
                diags.contains("A catastrophic JML internal error occurred"));
        assertFalse("Did not expect an internal JML error:\n" + diags,
                diags.contains("An internal JML error occurred"));
        assertFalse("Did not expect a null-expression crash in the SMT writer:\n" + diags,
                diags.contains("C_define_fun.expression()\" is null"));
        assertFalse("Did not expect the concat regression:\n" + diags,
                diags.contains("Could not find the concat method"));
        assertFalse("Did not expect a null-arg regression:\n" + diags,
                diags.contains("Cannot read field \"type\" because \"a\" is null"));
        assertTrue("Expected either a clean compile or only the known missing-prover failure, got:\n" + diags,
                ex == 0 || diags.contains("The executable for prover z3_4_3 is not specified"));
    }

    // -----------------------------------------------------------------------
    //  Bug-2 regression: switch expression with throw arm
    // -----------------------------------------------------------------------

    /** Minimal sealed Result type exercising record-pattern switch and binding-pattern switch. */
    static final String RESULT_SOURCE = """
            package com.example;

            public sealed interface Result<T, E> permits Result.Ok, Result.Err {

                record Ok<T, E>(T value) implements Result<T, E> {}
                record Err<T, E>(E error) implements Result<T, E> {}

                static <T, E extends Throwable> T getChecked(Result<T, E> result) throws E {
                    return switch (result) {
                        case Ok<T, E>(var value) -> value;
                        case Err<T, E>(var error) -> throw error;
                    };
                }

                static <T, E> T get(Result<T, E> result) {
                    return switch (result) {
                        case Ok<T, E> ok -> ok.value();
                        default -> null;
                    };
                }
            }
            """;

    /** The original crash: switch expression with a record-pattern yield arm and a throw arm. */
    @Test
    public void testResultGetChecked() throws Exception {
        assertNoInternalError("com/example/Result.java", RESULT_SOURCE, "getChecked");
    }

    /** The binding-pattern arm with a default fallback. */
    @Test
    public void testResultGet() throws Exception {
        assertNoInternalError("com/example/Result.java", RESULT_SOURCE, "get");
    }

    // -----------------------------------------------------------------------
    //  Pattern switch expression: binding patterns
    // -----------------------------------------------------------------------

    /** Switch expression with a simple binding pattern and a default. */
    @Test
    public void testBindingPatternSwitchExpr() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    int m(Object o) {
                        return switch (o) {
                            case String s -> s.length();
                            default -> 0;
                        };
                    }
                }
                """);
    }

    /** Exhaustive binding-pattern switch over a sealed interface. */
    @Test
    public void testSealedBindingPatternExhaustive() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    sealed interface Shape permits Circle, Rect {}
                    record Circle(double r) implements Shape {}
                    record Rect(double w, double h) implements Shape {}

                    double area(Shape s) {
                        return switch (s) {
                            case Circle c -> 3.14 * c.r() * c.r();
                            case Rect r   -> r.w() * r.h();
                        };
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Pattern switch expression: record patterns
    // -----------------------------------------------------------------------

    /** Switch expression with record patterns that destructure a record.
     *  Uses reference types (Integer) to avoid the pre-existing SMT sort-mismatch
     *  bug with primitive-typed record pattern components.
     *  Avoids int arithmetic to sidestep overflow verification warnings. */
    @Test
    public void testRecordPatternSwitchExpr() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    sealed interface Expr permits Lit, Neg {}
                    record Lit(String value) implements Expr {}
                    record Neg(Expr inner) implements Expr {}

                    String show(Expr e) {
                        return switch (e) {
                            case Lit(String v) -> v;
                            case Neg(Expr inner) -> "-" + show(inner);
                        };
                    }
                }
                """);
    }

    /** Record-pattern switch with a throw in one arm (the core Bug-2 scenario). */
    @Test
    public void testRecordPatternWithThrowArm() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    sealed interface Try<T> permits Ok, Fail {}
                    record Ok<T>(T value) implements Try<T> {}
                    record Fail<T>(RuntimeException ex) implements Try<T> {}

                    static <T> T unwrap(Try<T> t) {
                        return switch (t) {
                            case Ok<T>(var v)  -> v;
                            case Fail<T>(var e) -> throw e;
                        };
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Pattern switch expression: guarded patterns (when clause)
    // -----------------------------------------------------------------------

    /** Switch expression with guarded record patterns.
     *  Uses Integer (reference type) to avoid the pre-existing SMT sort-mismatch
     *  bug with primitive-typed record pattern components. */
    @Test
    public void testGuardedPatternSwitchExpr() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    record Box(Integer x) {}

                    int classify(Box b) {
                        return switch (b) {
                            case Box(Integer x) when x > 0  -> 1;
                            case Box(Integer x) when x == 0 -> 0;
                            case Box(Integer x)             -> -1;
                        };
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Pattern switch expression: mixed constant + pattern labels
    // -----------------------------------------------------------------------

    /** Switch expression mixing null, constant and pattern labels. */
    @Test
    public void testMixedConstantAndPatternLabels() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    String describe(Object o) {
                        return switch (o) {
                            case Integer i -> "int: " + i;
                            case String s  -> "str: " + s;
                            case null, default -> "other";
                        };
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Pattern switch *statement* (not expression)
    // -----------------------------------------------------------------------

    /** Pattern switch statement — verifies BasicBlocker handles pattern cases
     *  correctly even when the switch is not an expression. */
    @Test
    public void testPatternSwitchStatement() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    sealed interface Animal permits Dog, Cat {}
                    record Dog(String name) implements Animal {}
                    record Cat(String name) implements Animal {}

                    void greet(Animal a) {
                        switch (a) {
                            case Dog d -> System.out.println("Woof, " + d.name());
                            case Cat c -> System.out.println("Meow, " + c.name());
                        }
                    }
                }
                """);
    }

    /** Pattern switch statement with a throw in one arm. */
    @Test
    public void testPatternSwitchStatementWithThrow() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    sealed interface Validated<T> permits Valid, Invalid {}
                    record Valid<T>(T value) implements Validated<T> {}
                    record Invalid<T>(String msg) implements Validated<T> {}

                    static <T> void process(Validated<T> v) {
                        switch (v) {
                            case Valid<T>(var val)    -> System.out.println(val);
                            case Invalid<T>(var msg) -> throw new IllegalArgumentException(msg);
                        }
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Pattern switch expression: default with pattern arms
    // -----------------------------------------------------------------------

    /** Switch expression with pattern arms + explicit default. */
    @Test
    public void testPatternSwitchExprWithDefault() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    int measure(Object o) {
                        return switch (o) {
                            case String s  -> s.length();
                            case Integer i -> i;
                            default        -> -1;
                        };
                    }
                }
                """);
    }

    // -----------------------------------------------------------------------
    //  Multiple throw arms
    // -----------------------------------------------------------------------

    /** Switch expression where all-but-one arm throws — verifies that the
     *  throw-arm pattern handling in BasicBlocker doesn't crash.
     *  (A switch expression where literally *every* arm throws is rejected by
     *  javac with "switch expression does not have any result expressions".) */
    @Test
    public void testAllArmsThrow() throws Exception {
        assertNoInternalError("A.java", """
                class A {
                    sealed interface Status permits StatusA, StatusB, StatusC {}
                    record StatusA(String msg) implements Status {}
                    record StatusB(String msg) implements Status {}
                    record StatusC(String msg) implements Status {}

                    static int fail(Status s) {
                        return switch (s) {
                            case StatusA(var m) -> throw new UnsupportedOperationException(m);
                            case StatusB(var m) -> throw new UnsupportedOperationException(m);
                            case StatusC(var m) -> 0;
                        };
                    }
                }
                """);
    }
}
