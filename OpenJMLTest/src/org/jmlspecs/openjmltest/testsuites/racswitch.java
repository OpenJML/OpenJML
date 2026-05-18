package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Test;

/** These tests exercise the RAC checking for switch statements and expressions.
 * They compile a test class using RAC and then execute the resulting program,
 * catching that program's output. All the tests here have valid JML — they are
 * testing whether the RAC translations work correctly.
 * Tests cover traditional switch statements (with int, short, byte, char, String,
 * and enum selectors) and modern pattern-matching switch expressions (Java 21+).
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racswitch extends RacBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--code-math=java","--spec-math=java");
        addOptions("--rac-show-source=line");
        // Tests presume --nonnull-by-default
    }

    // -----------------------------------------------------------------------
    // Traditional switch statement tests
    // -----------------------------------------------------------------------

    /** Tests switch statement */
    @Test public void testSwitch() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(0);
                    m(1);
                    m(2);
                    m(3);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    switch (i) {
                    case 0: //@ assert i == 0;
                      break;
                    case 1: //@ assert i == 0;
                      break;
                    case 2: //@ assert i == 2;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"/tt/TestJava.java:18: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement with declaration in a case*/
    @Test public void testSwitch2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(0);
                    m(1);
                    m(2);
                    m(3);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    switch (i) {
                    case 0: int k = 0; //@ assert i == k;
                    case 1: k=1;       //@ assert i == k;
                      break;
                    case 2: k=2;       //@ assert i == k;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:13: JML assertion is false" // case 0 falls through
                ,"/tt/TestJava.java:17: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement with block breaks */
    @Test public void testSwitch3() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(0);
                    m(1);
                    m(2);
                    m(3);
                    System.out.println("END");
                  }
                  static void m(int i) {
                    System.out.print(i);
                    out: { switch (i) {
                    case 0: break;
                    case 1: break out;
                    case 2: in: { break in; } System.out.print("X"); break;
                    default: in: { if (i == 3)  break; } System.out.print("Y"); break;
                    }
                    System.out.print("Z"); }
                  }
                }
                """
                ,"0Z12XZ3ZEND"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchShort() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m((short)0);
                    m((short)1);
                    m((short)2);
                    m((short)3);
                    System.out.println("END");
                  }
                  static void m(short i) {
                    switch (i) {
                    case 0: //@ assert i == 0;
                      break;
                    case 1: //@ assert i == 0;
                      break;
                    case 2: //@ assert i == 2;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"/tt/TestJava.java:18: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchShort2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m((short)0);
                    m((short)1);
                    m((short)2);
                    m((short)3);
                    System.out.println("END");
                  }
                  static void m(short s) {
                    Short i = Short.valueOf(s);
                    switch (i) {
                    case 0: //@ assert i == 0;
                      break;
                    case 1: //@ assert i == 0;
                      break;
                    case 2: //@ assert i == 2;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                ,"/tt/TestJava.java:19: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchByte() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m((byte)0);
                    m((byte)1);
                    m((byte)2);
                    m((byte)3);
                    System.out.println("END");
                  }
                  static void m(byte i) {
                    switch (i) {
                    case 0: //@ assert i == 0;
                      break;
                    case 1: //@ assert i == 0;
                      break;
                    case 2: //@ assert i == 2;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"/tt/TestJava.java:18: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchByte2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m((byte)0);
                    m((byte)1);
                    m((byte)2);
                    m((byte)3);
                    System.out.println("END");
                  }
                  static void m(byte s) {
                    Byte i = Byte.valueOf(s);
                    switch (i) {
                    case 0: //@ assert i == 0;
                      break;
                    case 1: //@ assert i == 0;
                      break;
                    case 2: //@ assert i == 2;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                ,"/tt/TestJava.java:19: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchInteger2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m(0);
                    m(1);
                    m(2);
                    m(3);
                    System.out.println("END");
                  }
                  static void m(int s) {
                    Integer i = Integer.valueOf(s);
                    switch (i) {
                    case 0: //@ assert i == 0;
                      break;
                    case 1: //@ assert i == 0;
                      break;
                    case 2: //@ assert i == 2;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                ,"/tt/TestJava.java:19: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchInteger2Null() {
        helpRacText("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default*/
                public class TestJava {
                  public static void main(String[] args) {
                    try { m(0); } catch (Exception e) { System.out.println("EXCEPTION THROWN"); }
                    System.out.println("END");
                  }
                  static void m(int s) {
                    Integer i = null;
                    switch (i) {
                    case 0: //@ assert i == 0;
                      break;
                    case 1: //@ assert i == 0;
                      break;
                    case 2: //@ assert i == 2;
                      break;
                    default: //@ assert i == 0;
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:10: JML Attempt to unbox a null object"
                ,"EXCEPTION THROWN"
                ,"END"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchChar() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m('a');
                    m('b');
                    m('c');
                    m('d');
                    System.out.println("END");
                  }
                  static void m(char i) {
                    switch (i) {
                    case 'a': //@ assert i == 'a';
                      break;
                    case 'b': //@ assert i == 'a';
                      break;
                    case 'c': //@ assert i == 'c';
                      break;
                    default: //@ assert i == 'a';
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:14: JML assertion is false"
                ,"/tt/TestJava.java:18: JML assertion is false"
                ,"END"
        );
    }

    /** Tests switch statement */
    @Test public void testSwitchChar2() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static void main(String[] args) {
                    m('a');
                    m('b');
                    m('c');
                    m('d');
                    System.out.println("END");
                  }
                  static void m(char s) {
                    Character i = Character.valueOf(s);
                    switch (i) {
                    case 'a': //@ assert i == 'a';
                      break;
                    case 'b': //@ assert i == 'a';
                      break;
                    case 'c': //@ assert i == 'c';
                      break;
                    default: //@ assert i == 'a';
                      break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                ,"/tt/TestJava.java:19: JML assertion is false"
                ,"END"
        );
    }

    @Test public void testStringSwitch() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  public static void main(String[] args) {
                    String s = "abc";
                    int k;
                    switch (s) {
                      case "asd": k = 1; break;
                      case "abc": k = 2; break;
                      case "def": k = 3; break;
                      default: k = 4; break;
                    }
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 2"
                );
    }

    @Test public void testStringSwitchNull() {
        expectedRACExit = 1;
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  public static void main(String[] args) {
                    String s = null;
                    int k = 0;
                    { switch (s) {
                      case "asd": k = 1; break;
                      case "abc": k = 2; break;
                      case "def": k = 3; break;
                      default: k = 4; break;
                    } }
                    System.out.println("END " + k);
                  }
                }
                """
                ,"/tt/A.java:7: verify: JML An object is unexpectedly null"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot invoke \"String.hashCode()\" because \"<local7>\" is null"
                ,"\tat tt.A.main(A.java:7)"
                );
    }

    @Test public void testStringSwitchNullCatch() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  public static void main(String[] args) {
                    String s = null;
                    int k = 0;
                    try { switch (s) {
                      case "asd": k = 1; break;
                      case "abc": k = 2; break;
                      case "def": k = 3; break;
                      default: k = 4; break;
                    } } catch (Exception e) { System.out.println("CAUGHT"); }
                    System.out.println("END " + k);
                  }
                }
                """
                ,"CAUGHT"
                ,"END 0"
                );
    }

    @Test public void testEnumSwitch() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  enum E { A,B,C};
                  public static void main(String[] args) {
                    E e = E.B;
                    int k = 0;
                    switch (e) {
                      case A: k = 1; break;
                      case B: k = 2; break;
                      case C: k = 3; break;
                      default: k = 4; break;
                    }
                    System.out.println("END " + k);
                  }
                }
                """
                ,"END 2"
                );
    }

    @Test public void testEnumSwitchNull() {
        expectedRACExit = 1;
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  enum E { A,B,C};
                  public static void main(String[] args) {
                    E e = null;
                    int k = 0;
                    { switch (e) {
                      case A: k = 1; break;
                      case B: k = 2; break;
                      case C: k = 3; break;
                      default: k = 4; break;
                      }
                    }
                    System.out.println("END " + k);
                  }
                }
                """
                ,"/tt/A.java:8: verify: JML An object is unexpectedly null"
                ,"Exception in thread \"main\" java.lang.NullPointerException: Cannot invoke \"tt.A$E.ordinal()\" because \"<local4>\" is null"
                ,"\tat tt.A.main(A.java:8)"
                );
    }

    @Test public void testEnumSwitchNullCatch() {
        helpRacText("tt.A",
                """
                package tt;
                /*@ nullable_by_default*/
                public class A {
                  enum E { A,B,C};
                  public static void main(String[] args) {
                    E e = null;
                    int k = 0;
                    try { switch (e) {
                      case A: k = 1; break;
                      case B: k = 2; break;
                      case C: k = 3; break;
                      default: k = 4; break;
                      }
                    } catch (Exception ee) { System.out.println("CAUGHT");}
                    System.out.println("END " + k);
                  }
                }
                """
                ,"CAUGHT"
                ,"END 0"
                );
    }

    // -----------------------------------------------------------------------
    // Pattern-matching switch tests
    // -----------------------------------------------------------------------

    /** Binding pattern: case String s matches a String and binds it. */
    @Test
    public void testPatternSwitchBindingPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ spec_pure
                    public static int classify(Object o) {
                        return switch (o) {
                            case String s -> s.length();
                            case Integer i -> i;
                            default -> -1;
                        };
                    }
                    public static void main(String... args) {
                        //@ assert classify("hello") == 5;
                        //@ assert classify(42) == 42;
                        //@ assert classify(3.14) == -1;
                        //@ assert classify("hello") == 99;  // ERROR - line 15
                    }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                );
    }

    /** Guarded pattern: when clause further constrains the match. */
    @Test
    public void testPatternSwitchGuardedPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ spec_pure
                    public static String size(Object o) {
                        return switch (o) {
                            case Integer i when i > 100 -> "large";
                            case Integer i when i > 10  -> "medium";
                            case Integer i              -> "small";
                            default                     -> "other";
                        };
                    }
                    public static void main(String... args) {
                        //@ assert size(200).equals("large");
                        //@ assert size(50).equals("medium");
                        //@ assert size(5).equals("small");
                        //@ assert size("x").equals("other");
                        //@ assert size(50).equals("large");  // ERROR - line 17
                    }
                }
                """
                ,"/tt/TestJava.java:17: JML assertion is false"
                );
    }

    /** Null case label: explicit null matching in switch. */
    @Test
    public void testPatternSwitchNullCase() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    //@ spec_pure
                    public static String describe(/*@ nullable */Object o) {
                        return switch (o) {
                            case null    -> "nothing";
                            case String s -> s;
                            default      -> "other";
                        };
                    }
                    public static void main(String... args) {
                        //@ assert describe(null).equals("nothing");
                        //@ assert describe("hi").equals("hi");
                        //@ assert describe(42).equals("other");
                        //@ assert describe(null).equals("something");  // ERROR - line 15
                    }
                }
                """
                ,"/tt/TestJava.java:15: JML assertion is false"
                );
    }

    /** Sealed interface with binding patterns — exhaustive switch. */
    @Test
    public void testPatternSwitchSealedInterface() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    sealed interface Shape permits Circle, Rect {}
                    record Circle(double r) implements Shape {}
                    record Rect(double w, double h) implements Shape {}
                    //@ spec_pure
                    public static String name(Shape s) {
                        return switch (s) {
                            case Circle c -> "circle";
                            case Rect r   -> "rect";
                        };
                    }
                    public static void main(String... args) {
                        var s = new Circle(1.0);
                        //@ assert name(s).equals("circle");
                        var r = new Rect(2.0, 3.0);
                        //@ assert name(r).equals("rect");
                        var c = new Circle(1.0);
                        //@ assert name(c).equals("rect");  // ERROR - line 19
                    }
                }
                """
                ,"/tt/TestJava.java:19: JML assertion is false"
                );
    }

    /** Nested record patterns: matching Add(Lit(a), Lit(b)) requires two levels
     *  of destructuring — the outer Add and the inner Lit components. */
    @Test
    public void testPatternSwitchNestedRecordPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    sealed interface Expr permits Lit, Add {}
                    record Lit(int v) implements Expr {}
                    record Add(Expr left, Expr right) implements Expr {}
                    //@ spec_pure
                    public static int eval(Expr e) {
                        return switch (e) {
                            case Add(Lit(int a), Lit(int b)) -> a + b;
                            case Add(Lit(int a), Add(Lit(int b), Lit(int c))) -> a + b + c;
                            case Lit(int v) -> v;
                            default -> -1;
                        };
                    }
                    public static void main(String... args) {
                        var v = eval(new Lit(7));
                        //@ assert v == 7;
                        var a = eval(new Add(new Lit(3), new Lit(4)));
                        //@ assert a == 7;
                        var b = eval(new Add(new Lit(1), new Add(new Lit(2), new Lit(3))));
                        //@ assert b == 6;
                        var c = eval(new Add(new Lit(3), new Lit(4)));
                        //@ assert c == 10;  // ERROR - line 23
                    }
                }
                """
                ,"/tt/TestJava.java:23: JML assertion is false"
                );
    }

    /** Record pattern destructuring in switch expression. */
    @Test
    public void testPatternSwitchRecordPattern() {
        helpRacText("tt.TestJava",
                """
                package tt;
                public class TestJava {
                    record Point(int x, int y) {}
                    //@ pure
                    public static int sum(Object o) {
                        return switch (o) {
                            case Point(int x, int y) -> x + y;
                            default -> -1;
                        };
                    }
                    public static void main(String... args) {
                        int k = sum(new Point(3, 4));
                        //@ assert k == 7;
                        k = sum(new Point(0, 0));
                        //@ assert k == 0;
                        k = sum("not a point");
                        //@ assert k == -1;
                        k = sum(new Point(3, 4));
                        //@ assert k == 10;  // ERROR - line 19
                    }
                }
                """
                ,"/tt/TestJava.java:19: JML assertion is false"
                );
    }

    public void testSwitchPrimitiveWhen() {
        helpRacText("tt.A", """
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
        helpRacText("tt.A", """
                package tt;
                public class A {
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
}
