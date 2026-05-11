package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class typecheckswitch extends TCBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--source", "21");
        addOptions("--enable-preview"); // To allow unnamed vars
        addOptions("--check");
        expectedExit = 0;
    }

    @Test
    public void testBindingPatternReference() {
        helpTCText("A.java",
                """
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

    @Test
    public void testBindingPatternSealedInterface() {
        helpTCText("A.java",
                """
                class A {
                    sealed interface R permits Ok, Err {}
                    record Ok(int value) implements R {}
                    record Err(int value) implements R {}
                    int m(R r) {
                        return switch (r) {
                            case Ok ok -> ok.value();
                            case Err err -> err.value();
                        };
                    }
                }
                """);
    }

    @Test
    public void testCaseNullAndDefault() {
        helpTCText("A.java",
                """
                class A {
                    int m(Object o) {
                        return switch (o) {
                            case null, default -> 0;
                        };
                    }
                }
                """);
    }

    @Test
    public void testGenericSelectorPatternSwitch() {
        helpTCText("A.java",
                """
                class A<E> {
                    int m(E e) {
                        return switch (e) {
                            case Exception ex -> 1;
                            default -> 0;
                        };
                    }
                }
                """);
    }

    @Test
    public void testGuardedRecordPatternSwitchExpression() {
        helpTCText("A.java",
                """
                class A {
                    record Box(int x) {}
                    int m(Box b) {
                        return switch (b) {
                            case Box(int x) when x > 0 -> x;
                            case Box(int x) -> -x;
                        };
                    }
                }
                """);
    }

    @Test
    public void testRecordPatternSimpleAndNested() {
        helpTCText("A.java",
                """
                class A {
                    record Bar(int x) {}
                    record Foo(Bar bar) {}
                    int m(Foo f) {
                        return switch (f) {
                            case Foo(Bar(int x)) -> x;
                        };
                    }
                }
                """);
    }

    @Test
    public void testUnnamedPatterns() {
        helpTCText("A.java",
                """
                class A {
                    record Foo(int x) {}
                    int m(Object o, Foo f) {
                        int a = switch (o) {
                            case String _, Integer _ -> 1;
                            default -> 0;
                        };
                        int b = switch (f) {
                            case Foo(_) -> 2;
                        };
                        return a + b;
                    }
                }
                """);
    }
}
