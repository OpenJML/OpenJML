package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escswitch extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--source", "21");
        addOptions("--enable-preview"); // To allow unnamed vars in pattern matching
        addOptions("--check-feasibility=exit,switch,return");
        expectedExit = 0;
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
    public void testResultGetChecked() {
        addOptions("--method=getChecked");
        helpEsc("com.example.Result", RESULT_SOURCE);
    }

    /** The binding-pattern arm with a default fallback. */
    @Test
    public void testResultGet() {
        addOptions("--method=get");
        helpEsc("com.example.Result", RESULT_SOURCE);
    }

    // -----------------------------------------------------------------------
    //  Pattern switch expression: binding patterns
    // -----------------------------------------------------------------------

    /** Switch expression with a simple binding pattern and a default.
     *  Result is s.length() (>= 0) for a String, or 0 for everything else. */
    @Test
    public void testBindingPatternSwitchExpr() {
        helpEsc("A", """
                class A {
                    //@ ensures \\result >= 0;
                    int m(Object o) {
                        return switch (o) {
                            case String s -> s.length();
                            default -> 0;
                        };
                    }
                }
                """);
    }

    /** Verify that ESC detects an impossible bound on the binding-pattern result. */
    @Test
    public void testBindingPatternSwitchExprFail() {
        helpEsc("A", """
                class A {
                    //@ ensures \\result < 0;
                    int m(Object o) {
                        return switch (o) {
                            case String s -> s.length();
                            default -> 0;
                        };
                    }
                }
                """
                ,"/A.java:4: verify: The prover cannot establish an assertion (Postcondition) in method m", 9
                ,"/A.java:2: verify: Associated declaration", 9
                );
    }

    /** Exhaustive binding-pattern switch over a sealed interface. */
    @Test
    public void testSealedBindingPatternExhaustive() {
        helpEsc("A", """
                class A {
                    sealed interface Shape permits Circle, Rect {}
                    record Circle(double r) implements Shape {}
                    record Rect(double w, double h) implements Shape {}

                    //@ requires c.r() >= 0;
                    //@ ensures \\result >= 0;
                    double circleArea(Circle c) {
                        return 3.14 * c.r() * c.r();
                    }

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

    /** Switch expression with record patterns that destructure a record. */
    @Test
    public void testRecordPatternSwitchExpr() {
        helpEsc("A", """
                class A {
                    sealed interface Expr permits Lit, Neg {}
                    record Lit(String value) implements Expr {}
                    record Neg(Expr inner) implements Expr {}

                    //@ ensures \\result != null;
                    String show(Expr e) {
                        return switch (e) {
                            case Lit(String v) -> v;
                            case Neg(Expr inner) -> "-" + show(inner);
                        };
                    }
                }
                """);
    }

    /** ESC detects that show() cannot return null even though null-return is asserted. */
    @Test
    public void testRecordPatternSwitchExprFail() {
        helpEsc("A", """
                class A {
                    sealed interface Expr permits Lit, Neg {}
                    record Lit(String value) implements Expr {}
                    record Neg(Expr inner) implements Expr {}

                    //@ ensures \\result == null;
                    String show(Expr e) {
                        return switch (e) {
                            case Lit(String v) -> v;
                            case Neg(Expr inner) -> "-"; //  + show(inner);
                        };
                    }
                }
                """
                ,"/A.java:8: verify: The prover cannot establish an assertion (Postcondition) in method show", 9
                ,"/A.java:6: verify: Associated declaration", 9
                );
    }

    /** Record-pattern switch with a throw in one arm (the core Bug-2 scenario). */
    @Test
    public void testRecordPatternWithThrowArm() {
        helpEsc("A", """
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
     *  classify returns exactly 1, 0, or -1. */
    @Test
    public void testGuardedPatternSwitchExpr() {
        helpEsc("A", """
                class A {
                    record Box(Integer x) {}

                    //@ ensures \\result == 1 || \\result == 0 || \\result == -1;
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

    /** ESC detects that classify() cannot return 2. */
    @Test
    public void testGuardedPatternSwitchExprFail() {
        helpEsc("A", """
                class A {
                    record Box(Integer x) {}

                    //@ ensures \\result == 2;
                    int classify(Box b) {
                        return switch (b) {
                            case Box(Integer x) when x > 0  -> 1;
                            case Box(Integer x) when x == 0 -> 0;
                            case Box(Integer x)             -> -1;
                        };
                    }
                }
                """
                ,"/A.java:6: verify: The prover cannot establish an assertion (Postcondition) in method classify", 9
                ,"/A.java:4: verify: Associated declaration", 9
                );
    }

    // -----------------------------------------------------------------------
    //  Pattern switch expression: mixed constant + pattern labels
    // -----------------------------------------------------------------------

    /** Switch expression mixing null, constant and pattern labels. */
    @Test
    public void testMixedConstantAndPatternLabels() {
        helpEsc("A", """
                class A {
                    //@ ensures \\result != null;
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

    /** ESC detects that describe() cannot return null. */
    @Test
    public void testMixedConstantAndPatternLabelsFail() {
        helpEsc("A", """
                class A {
                    //@ ensures \\result == null;
                    /*@ nullable */ String describe(Object o) {
                        return switch (o) {
                            case Integer i -> "int: " + i;
                            case String s  -> "str: " + s;
                            case null, default -> "other";
                        };
                    }
                }
                """
                ,"/A.java:4: verify: The prover cannot establish an assertion (Postcondition) in method describe", 9
                ,"/A.java:2: verify: Associated declaration", 9
                );
    }

    // -----------------------------------------------------------------------
    //  Pattern switch *statement* (not expression)
    // -----------------------------------------------------------------------

    /** Pattern switch statement — verifies BasicBlocker handles pattern cases
     *  correctly even when the switch is not an expression. */
    @Test
    public void testPatternSwitchStatement() {
        helpEsc("A", """
                class A {
                    sealed interface Animal permits Dog, Cat {}
                    record Dog(String name) implements Animal {}
                    record Cat(String name) implements Animal {}

                    //@ requires a != null;
                    void greet(Animal a) {
                        switch (a) {
                            case Dog d -> System.out.println("Woof, " + d.name());
                            case Cat c -> System.out.println("Meow, " + c.name());
                        }
                    }
                }
                """);
    }

    @Test
    public void testSealed() {
        helpEsc("A", """
                class A {
                    sealed interface Animal permits Dog, Cat {}
                    record Dog(String name) implements Animal {}
                    record Cat(String name) implements Animal {}

                    //@ requires a != null;
                    void greet(Animal a) {
                        //@ assert a instanceof Dog || a instanceof Cat;
                    }
                }
                """);
    }

    /** Pattern switch statement with a throw in one arm. */
    @Test
    public void testPatternSwitchStatementWithThrow() {
        helpEsc("A", """
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

    /** Switch expression with pattern arms + explicit default. Result >= -1. */
    @Test
    public void testPatternSwitchExprWithDefault() {
        helpEsc("A", """
                class A {
                //@ requires o instanceof Integer k ==> k > 0;
                    //@ ensures \\result >= -1;
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

    /** ESC detects that measure() cannot return -2. */
    @Test
    public void testPatternSwitchExprWithDefaultFail() {
        helpEsc("A", """
                class A {
                    //@ ensures \\result < -1;
                    int measure(Object o) {
                        return switch (o) {
                            case String s  -> s.length();
                            case Integer i -> i;
                            default        -> -1;
                        };
                    }
                }
                """
                ,"/A.java:4: verify: The prover cannot establish an assertion (Postcondition) in method measure", 9
                ,"/A.java:2: verify: Associated declaration", 9
                );
    }

    // -----------------------------------------------------------------------
    //  Multiple throw arms
    // -----------------------------------------------------------------------

    /** Switch expression where all-but-one arm throws.
     *  On the normal path the only possible return is 0. */
    @Test
    public void testAllArmsThrow() {
        helpEsc("A", """
                class A {
                    sealed interface Status permits StatusA, StatusB, StatusC {}
                    record StatusA(String msg) implements Status {}
                    record StatusB(String msg) implements Status {}
                    record StatusC(String msg) implements Status {}

                    //@ ensures \\result == 0;
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

    @Test
    public void testAllArmsThrowB() {
        expectedExit = 1;
        helpEsc("A", """
                class A {
                    static int fail(int s) {
                        return switch (s) {
                            case 0 -> throw new UnsupportedOperationException();
                            case 1 -> throw new UnsupportedOperationException();
                            default -> throw new UnsupportedOperationException();
                        };
                    }
                }
                """
                ,"/A.java:3: error: switch expression does not have any result expressions", 16
                );
    }

    // -----------------------------------------------------------------------
    //  Switch expression throw arm — visitYield scenarios
    // -----------------------------------------------------------------------

    /** Switch expression with a throw arm — result is non-null on normal exit. */
    @Test
    public void testSwitchExprThrowArm() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    //@ ensures \\result != null;
                    public static /*@ pure */ String describe(int n) {
                        return switch (n) {
                            case 1 -> "one";
                            default -> throw new RuntimeException("unexpected: " + n);
                        };
                    }
                }
                """);
    }

    /** ESC detects that describe() cannot return null on the normal exit path. */
    @Test
    public void testSwitchExprThrowArmFail() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    //@ ensures \\result == null;
                    public static /*@ pure */ String describe(int n) {
                        return switch (n) {
                            case 1 -> "one";
                            default -> throw new RuntimeException("unexpected: " + n);
                        };
                    }
                }
                """
                ,"/tt/A.java:5: verify: The prover cannot establish an assertion (Postcondition) in method describe", 9
                ,"/tt/A.java:3: verify: Associated declaration", 9
                );
    }

    /** Switch expression where throw arm has concatenation. */
    @Test
    public void testSwitchExprThrowArmWithConcat() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    //@ ensures \\result != null;
                    public static /*@ pure */ String label(int n) {
                        return switch (n) {
                            case 0 -> "zero";
                            case 1 -> "one";
                            default -> throw new IllegalArgumentException("bad value: " + n);
                        };
                    }
                }
                """
                );
    }

    // -----------------------------------------------------------------------
    //  Nested record patterns
    // -----------------------------------------------------------------------

    /** Two-level nested pattern: case Neg(Lit(Integer v)) matches a Neg whose
     *  inner is a Lit.  Returns a small integer constant per branch so ESC can
     *  prove the result stays in {0, 1, 2} without any arithmetic reasoning.
     *  Uses Integer (boxed) to avoid the primitive-component SMT sort-mismatch bug. */
    @Test
    public void testNestedRecordPattern() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    sealed interface Expr permits Lit, Neg {}
                    record Lit(Integer v) implements Expr {}
                    record Neg(Expr inner) implements Expr {}

                    //@ ensures \\result >= 0 && \\result <= 2;
                    int depth(Expr e) {
                        return switch (e) {
                            case Neg(Lit(Integer v)) -> 2;
                            case Neg(Expr inner)     -> 1;
                            case Lit(Integer v)      -> 0;
                        };
                    }
                }
                """);
    }

    /** ESC detects that depth() cannot return 3. */
    @Test
    public void testNestedRecordPatternFail() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    sealed interface Expr permits Lit, Neg {}
                    record Lit(Integer v) implements Expr {}
                    record Neg(Expr inner) implements Expr {}

                    //@ ensures \\result == 3;
                    int depth(Expr e) {
                        return switch (e) {
                            case Neg(Lit(Integer v)) -> 2;
                            case Neg(Expr inner)     -> 1;
                            case Lit(Integer v)      -> 0;
                        };
                    }
                }
                """
                ,"/tt/A.java:9: verify: The prover cannot establish an assertion (Postcondition) in method depth", 9
                ,"/tt/A.java:7: verify: Associated declaration", 9
                );
    }

    /** Multi-type switch expression yield with throw arm. */
    @Test
    public void testSwitchExprObjectYieldThrowArm() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    public static Object coerce(int n) {
                        return switch (n) {
                            case 0 -> "zero";
                            case 1 -> 1;
                            default -> throw new IllegalArgumentException();
                        };
                    }
                }
                """);
    }
    
    public void testSwitchPrimitiveWhen() {
        helpEsc("tt.A", """
                package tt;
                public class A {
                    //@ ensures (n == 0 && b) ==> \\result == 1;
                    //@ ensures (n == 0 && !b) ==> \\result == -1;
                    //@ ensures n != 0 ==> \\result == 0;
                    public static int coerce(int n, boolean b) {
                        return switch (n) {
                            case 0 when b -> 1;
                            case 0 when !b -> -1;
                            default -> 0;
                        };
                    }
                }
                """);
    }
    
    public void testSwitchPrimitiveWhenFail() {
        helpEsc("tt.Z", """
                package tt;
                public class Z {
                    //@ ensures (n == 0 && b) ==> \\result == 1;
                    //@ ensures (n == 0 && !b) ==> \\result == -10;
                    //@ ensures n != 0==> \\result == 0;
                    public static int coerce(int n, boolean b) {
                        return switch (n) {
                            case 0 when b -> 1;
                            case 0 when !b -> -1;
                            default -> 0;
                        };
                    }
                }
                """);
    }
    
    @Test public void escEnum() {
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  enum E { A,B,C};
                  //@ requires arg != null;
                  //@ ensures arg == E.A ==> \\result == 1;
                  //@ ensures arg == E.C ==> \\result == 4;
                  public static int m(/*@ nullable */ E arg) {
                    int k = switch (arg) {
                      case A -> 1;
                      case B -> 2;
                      default -> 4;
                    };
                    return k;
                  }
                }
                """
                );
    }

    @Test public void escEnumNull() {
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  enum E { A,B,C};
                  //@ ensures arg == E.A ==> \\result == 1;
                  //@ ensures arg == E.C ==> \\result == 4;
                  public static int m(/*@ nullable */ E arg) {
                    int k = switch (arg) {
                      case A -> 1;
                      case B -> 2;
                      default -> 4;
                    };
                    return k;
                  }
                }
                """
                ,"/tt/Z.java:8: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m", 20
                );
    }

    @Test public void escEnumNullCase() {
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  enum E { A,B,C};
                  //@ ensures arg == E.A ==> \\result == 1;
                  //@ ensures arg == E.C ==> \\result == 4;
                  //@ ensures arg == null ==> \\result == 3;
                  public static int m(/*@ nullable */ E arg) {
                    int k = switch (arg) {
                      case A -> 1;
                      case B -> 2;
                      case null -> 3;
                      default -> 4;
                    };
                    return k;
                  }
                }
                """
                );
    }

    @Test public void escEnumNullDefaultCase() {
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  enum E { A,B,C};
                  //@ ensures arg == E.A ==> \\result == 1;
                  //@ ensures arg == E.C ==> \\result == 4;
                  //@ ensures arg == null ==> \\result == 4;
                  public static int m(/*@ nullable */ E arg) {
                    int k = switch (arg) {
                      case A -> 1;
                      case B -> 2;
                      case null, default -> 4;
                    };
                    return k;
                  }
                }
                """
                );
    }

    @Test public void escString() {
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  //@ requires arg != null;
                  //@ ensures arg == "abc" ==> \\result == 1;
                  //@ ensures arg == "def" ==> \\result == 4;
                  public static int m(/*@ nullable */ String arg) {
                    int k = switch (arg) {
                      case "abc" -> 1;
                      default -> 4;
                    };
                    return k;
                  }
                }
                """
                );
    }

    @Test public void escStringNull() {
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  //@ ensures arg == "abc" ==> \\result == 1;
                  //@ ensures arg == "def" ==> \\result == 4;
                  public static int m(/*@ nullable */ String arg) {
                    int k = switch (arg) {
                      case "abc" -> 1;
                      default -> 4;
                    };
                    return k;
                  }
                }
                """
                ,"/tt/Z.java:7: verify: The prover cannot establish an assertion (PossiblyNullValue) in method m", 20
                );
    }

    @Test public void escStringNullCase() {
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  //@ ensures arg == "abc" ==> \\result == 1;
                  //@ ensures arg == null ==> \\result == 3;
                  //@ ensures arg == "def" ==> \\result == 4;
                  public static int m(/*@ nullable */ String arg) {
                    int k = switch (arg) {
                      case "abc" -> 1;
                      case null -> 3;
                      default -> 4;
                    };
                    return k;
                  }
                }
                """
                );
    }

    @Test public void escStringNullDefaultCase() {
        addOptions("--show","--method=m");
        helpEsc("tt.Z",
                """
                package tt;
                /*@ nullable_by_default*/
                public class Z {
                  //@ ensures arg == "abc" ==> \\result == 1;
                  //@ ensures arg == null ==> \\result == 4;
                  //@ ensures arg == "def" ==> \\result == 4;
                  public static int m(/*@ nullable */ String arg) {
                    int k = switch (arg) {
                      case "abc" -> 1;
                      case null, default -> 4;
                    };
                    return k;
                  }
                }
                """
                );
    }

// Boolean and boolean are not allowed until Java 24; same for long float double and corresponding boxed types
//    @Test public void escBoolean() {
//        helpEsc("tt.Z",
//                """
//                package tt;
//                /*@ nullable_by_default*/
//                public class Z {
//                  //@ requires arg != null;
//                  //@ ensures arg == true ==> \\result == 1;
//                  //@ ensures arg == false ==> \\result == 4;
//                  public static int m(/*@ nullable */ Boolean arg) {
//                    int k = switch (arg) {
//                      case true -> 1;
//                      default -> 4;
//                    };
//                    return k;
//                  }
//                }
//                """
//                );
//    }
//
//    @Test public void escBoolean1() {
//        helpEsc("tt.Z",
//                """
//                package tt;
//                /*@ nullable_by_default*/
//                public class Z {
//                  //@ ensures arg == Boolean.TRUE ==> \\result == 1;
//                  //@ ensures arg == Boolean.FALSE ==> \\result == 4;
//                  public static int m(/*@ nullable */ Boolean arg) {
//                    int k = switch (arg) {
//                      case true -> 1;
//                      default -> 4;
//                    };
//                    return k;
//                  }
//                }
//                """
//                );
//    }
//
//    @Test public void escBoolean2() {
//        helpEsc("tt.Z",
//                """
//                package tt;
//                /*@ nullable_by_default*/
//                public class Z {
//                  //@ requires arg != null;
//                  //@ ensures arg == Boolean.TRUE ==> \\result == 1;
//                  //@ ensures arg == Boolean.FALSE ==> \\result == 4;
//                  public static int m(/*@ nullable */ Boolean arg) {
//                    int k = switch (arg) {
//                      case Boolean.TRUE -> 1;
//                      default -> 4;
//                    };
//                    return k;
//                  }
//                }
//                """
//                );
//    }
//
//    @Test public void escBooleanNull() {
//        helpEsc("tt.Z",
//                """
//                package tt;
//                /*@ nullable_by_default*/
//                public class Z {
//                  //@ requires arg != null;
//                  //@ ensures arg == Boolean.TRUE ==> \\result == 1;
//                  //@ ensures arg == Boolean.FALSE ==> \\result == 4;
//                  //@ ensures arg == null ==> \\result == 3;
//                  public static int m(/*@ nullable */ Boolean arg) {
//                    int k = switch (arg) {
//                      case Boolean.TRUE -> 1;
//                      case null -> 3;
//                      default -> 4;
//                    };
//                    return k;
//                  }
//                }
//                """
//                );
//    }


}
