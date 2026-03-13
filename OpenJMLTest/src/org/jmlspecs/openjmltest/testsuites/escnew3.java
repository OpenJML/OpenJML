package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnew3 extends EscBase {

    // Test well-definedness within the implicit old
    @Test @Ignore // Times out
    public void testNonNullElements3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;
                  public void m5b(Object[] a) {
                    //@ assume a != null && a.length == 3;
                    //@ assume \\nonnullelements(a);
                    a[0] = null;
                    //@ assert \\nonnullelements(a);
                  }
                  //@ modifies \\everything;
                  public void m5c(Object[] a) {
                    //@ assume a != null && a.length == 0;
                    //@ assert \\nonnullelements(a);
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m4a",9
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assert) in method m5a",9
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Assert) in method m5b",9
                );
    }

    // Test well-definedness within the implicit old
    @Test @Ignore // Times out
    public void testNonNullElements() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m1x(/*@ non_null */ Object[] a) {
                    //@ assume \\nonnullelements(a);
                    //@ assume a.length > 1;
                    //@ assert a[0] != null;
                  }
                  //@ modifies \\everything;
                  public void m11(Object[] a) {
                    //@ assume \\nonnullelements(a);
                    //@ assert a != null;
                  }
                  //@ modifies \\everything;
                  public void m11a(Object[] a) {
                    //@ assume \\nonnullelements(a);
                    //@ assert a == null;
                  }
                  //@ modifies \\everything;
                  public void m1a(Object[] a) {
                    //@ assume a != null && a.length > 1;
                    //@ assert a[0] != null;
                  }
                  //@ modifies \\everything;
                  public void m2(Object[] a) {
                    //@ assume a != null && a.length == 0;
                    //@ assert \\nonnullelements(a);
                  }
                }
                """
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (Assert) in method m11a",9
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Assert) in method m1a",9
                );
    }

    // Test well-definedness within the implicit old
    @Test @Ignore // Times out
    public void testNonNullElements2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m22(Object[] a) {
                    //@ assume a != null && a.length == 0;
                    //@ assert (\\forall int i; 0<=i && i<a.length; a[i] != null);
                  }
                  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;
                  public void m3(Object[] a) {
                    //@ assume a != null && a.length == 1;
                    a[0] = new Object();    //@ assert a[0] != null;
                    //@ assert \\nonnullelements(a);
                  }
                  //@ modifies \\everything;
                  public void m33(Object[] a) {
                    //@ assume a != null && a.length == 1;
                    //@ assume a[0] != null;
                    //@ assert \\nonnullelements(a);
                  }
                  //@ requires \\elemtype(\\typeof(a)) == \\type(Object); modifies \\everything;
                  public void m4(Object[] a) {
                    //@ assume a != null && a.length == 2;
                    a[0] = new Object();
                    a[1] = new Object();
                    //@ assert \\nonnullelements(a);
                  }
                  //@ modifies \\everything;
                  public void m44(Object[] a) {
                    //@ assume a != null && a.length == 2;
                    //@ assume a[0] != null;
                    //@ assume a[1] != null;
                    //@ assert \\nonnullelements(a);
                  }
                }
                """
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
                    //@ assert \\not_modified(i);
                  }
                  //@ modifies \\everything;
                  public void m1a(int i) {
                    i = 5;
                    //@ assert \\not_modified(i);
                  }
                  public int i;
                  public static int si;
                  //@ ghost public int gi;
                  //@ requires i == 5;
                  //@ modifies \\everything;
                  public void m2() {
                    i = 5;
                    //@ assert \\not_modified(i);
                  }
                  //@ modifies \\everything;
                  public void m2a() {
                    i = 5;
                    //@ assert \\not_modified(i);
                  }
                  //@ requires si == 5;
                  //@ modifies \\everything;
                  public void m3() {
                    si = 5;
                    //@ assert \\not_modified(si);
                  }
                  //@ modifies \\everything;
                  public void m3a() {
                    si = 5;
                    //@ assert \\not_modified(si);
                  }
                  //@ requires gi == 5;
                  //@ modifies \\everything;
                  public void m4() {
                    //@ set gi = 5;
                    //@ assert \\not_modified(gi);
                  }
                  //@ modifies \\everything;
                  public void m4a() {
                    //@ set gi = 5;
                    //@ assert \\not_modified(gi);
                  }
                }
                """
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (Assert) in method m1a",9
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Assert) in method m2a",9
                ,"/tt/TestJava.java:37: verify: The prover cannot establish an assertion (Assert) in method m3a",9
                ,"/tt/TestJava.java:48: verify: The prover cannot establish an assertion (Assert) in method m4a",9
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
                    //@ assert \\not_modified(t.i);
                  }
                  //@ requires t != null;
                  //@ modifies \\everything;
                  public void m1a() {
                    t = null;
                    //@ assert \\not_modified(t.i) ? true: true;
                  }
                  //@ requires t == null;
                  //@ modifies \\everything;
                  public void m1b() {
                    t = new TestJava();
                    //@ assert \\not_modified(t.i) ? true: true;
                  }
                  //@ modifies \\everything;
                  public void m1c() {
                    //@ assert \\not_modified(t.i) ? true: true;
                  }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1a",31
                ,"/tt/TestJava.java:20: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1b",31
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method m1c",31
                );
    }

    @Test
    public void testCast() {
        main.addOptions("-code-math=safe","-spec-math=safe");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static long l;
                  public static int i;
                  public static short s;
                  public static char c;
                  public static byte b;
                  //@ requires i == 6;
                  //@ modifies \\everything;
                  public void m0() {
                    s = (short)i;
                    //@ assert s == i;
                    b = (byte)i;
                    //@ assert b == i;
                    c = (char)i;
                    //@ assert c == i;
                    l = (long)i;
                    //@ assert l == i;
                    int ii = (int)i;
                    //@ assert ii == i;
                    //@ assert i == (short)i;
                    //@ assert i == (long)i;
                    //@ assert i == (char)i;
                    //@ assert i == (byte)i;
                    //@ assert i == (int)i;
                  }
                  //@ requires i == 100000;
                  //@ modifies \\everything;
                  public static void m0bad() {
                    s = (short)i;
                    //@ assert s == i;
                  }
                  //@ requires i == 100000;
                  //@ modifies \\everything;
                  public static void m0badx() {
                    //@ assert i == (short)i;
                  }
                  //@ requires i == 100000;
                  //@ modifies \\everything;
                  public static void m1badx() {
                    //@ assert i == (byte)i;
                  }
                  //@ requires i == 100000;
                  //@ modifies \\everything;
                  public static void m2badx() {
                    //@ assert i == (char)i;
                  }
                  //@ requires i == 100000;
                  //@ modifies \\everything;
                  public static void m1bad() {
                    b = (byte)i;
                    //@ assert b == i;
                  }
                  //@ requires i == 100000;
                  //@ modifies \\everything;
                  public static void m2bad() {
                    c = (char)i;
                    //@ assert c == i;
                  }
                }
                """
                // NOTE: The range checks are soft asserts -- they do not change the result. Hence the subsequent assert (e.g. Line 31)
                // will fail.
                // The order of the two errors in each method may be reversed
                ,anyorder(
                  seq("/tt/TestJava.java:31: verify: The prover cannot establish an assertion (Assert) in method m0bad",9)
                 ,seq("/tt/TestJava.java:30: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m0bad",9))
                ,anyorder(
                  seq("/tt/TestJava.java:36: verify: The prover cannot establish an assertion (Assert) in method m0badx",9)
                 ,seq("/tt/TestJava.java:36: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m0badx",21))
                ,anyorder(
                  seq("/tt/TestJava.java:41: verify: The prover cannot establish an assertion (Assert) in method m1badx",9)
                 ,seq("/tt/TestJava.java:41: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m1badx",21))
                ,anyorder(
                  seq("/tt/TestJava.java:46: verify: The prover cannot establish an assertion (Assert) in method m2badx",9)
                 ,seq("/tt/TestJava.java:46: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m2badx",21))
                ,anyorder(
                  seq("/tt/TestJava.java:52: verify: The prover cannot establish an assertion (Assert) in method m1bad",9)
                 ,seq("/tt/TestJava.java:51: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m1bad",9))
                ,anyorder(
                  seq("/tt/TestJava.java:58: verify: The prover cannot establish an assertion (Assert) in method m2bad",9)
                 ,seq("/tt/TestJava.java:57: verify: The prover cannot establish an assertion (ArithmeticCastRange) in method m2bad",9))
                );
    }

    @Test
    public void testCast1() {
        addOptions("--esc-max-warnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m0() {
                    {/*@ nullable */ Short s = null;
                    short ss = (short)s;
                    //@ assert 0 == (short)s;}
                  }
                  //@ modifies \\everything;
                  public void m1() {
                    {/*@ nullable */ Integer s = null;
                    int ss = (int)s;
                    //@ assert 0 == (int)s;}
                  }
                  //@ modifies \\everything;
                  public void m2() {
                    {/*@ nullable */ Long s = null;
                    long ss = (long)s;
                    //@ assert 0L == (long)s;}
                  }
                  //@ modifies \\everything;
                  public void m3() {
                    {/*@ nullable */ Byte s = null;
                    byte ss = (byte)s;
                    //@ assert 0 == (byte)s;}
                  }
                  //@ modifies \\everything;
                  public void m4() {
                    {/*@ nullable */ Character s = null;
                    char ss = (char)s;
                    //@ assert 0 == (char)s;}
                  }
                  //@ modifies \\everything;
                  public void m7() {
                    {/*@ nullable */ Boolean s = null;
                    boolean ss = (boolean)s;
                    //@ assert (boolean)s;}
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m0",23
                ,"/tt/TestJava.java:12: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m1",19
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m2",21
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m3",21
                ,"/tt/TestJava.java:30: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m4",21
                ,"/tt/TestJava.java:36: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m7",27
                );
    }

    @Test
    public void testCast1real() {
        Assume.assumeTrue(runLongTests || !"z3_4_3".equals(solver));
        addOptions("--check"); // -esc times out FIXME
        addOptions("--esc-max-warnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m5() {
                    {/*@ nullable */ Double s = null;
                    double ss = (double)s;
                    //@ assert 0 == (double)s;}
                  }
                }
                """
                // FIXME Reinstate when running -esc
        //        ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m5",17
                );
    }

    @Test
    public void testCast1realb() {
        Assume.assumeTrue(runLongTests || !"z3_4_3".equals(solver));
        main.addOptions("--check"); // FIXME -esc times out
        addOptions("--esc-max-warnings=1");  // FIXME - issues very many warnings - lots of nearly identical paths?
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ modifies \\everything;
                  public void m6() {
                    {/*@ nullable */ Float s = null;
                    float ss = (float)s;
                    //@ assert 0.0 == (float)s;}
                  }
                }
                """
                // FIXME Reinstate when running -esc
         //       ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method m6",16
                );
    }

    // TODO - test not_modified and old nested in each other; remember to test definedness

    @Test
    public void testAssignableConstructor0() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private int i;
                  //@ assignable \\everything;
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor1() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private int i;
                  //@ assignable i;
                  public void mm() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                ,"/tt/TestJava.java:4: error: An identifier with private visibility may not be used in a assignable clause with public visibility",18
                );
    }

    @Test
    public void testAssignableConstructor2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private int i;
                  //@ assignable \\nothing;
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private int i;
                
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor3a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private int i;
                  //@ requires true;\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor3ae() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private int i;
                  //@ requires true; pure\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor3e() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  private int i;
                  //@ pure\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { //@ public model nullable Object state;
                  private int i; //@ in state;
                  \s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor4e() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { //@ public model nullable Object state;
                  private int i; //@ in state;
                  //@ pure\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor4a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { //@ public model nullable Object state;
                  private int i; //@ in state;
                  //@ requires true;
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor4ae() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { //@ public model nullable Object state;
                  private int i; //@ in state;
                  //@ requires true; pure\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { //@ public model nullable Object state;
                  private int i; //@ in state;
                  //@ pure
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor5s() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava { //@ public model nullable Object state;
                  private int i; //@ in state;
                  //@ pure
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor6() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ spec_public */ private int i;
                  \s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor6a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ spec_public */ private int i;
                  //@ requires true;\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor6e() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ spec_public */ private int i;
                  //@ pure\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor6ae() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ spec_public */ private int i;
                  //@ requires true; pure\s
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor7() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ spec_public */ private int i;
                  //@ pure
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testAssignableConstructor7s() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ spec_public */ private int i;
                  //@ pure
                  public TestJava() { i = 0; }
                  //@ assignable \\everything;
                  public static void m() { new TestJava(); }
                }
                """
                );
    }

    @Test
    public void testVarargs() {
        helpEsc("tt.TestJava",
                """
                package tt;
                /*@ nullable_by_default */ public class TestJava {
                  //@ ensures \\result == ints.length;
                  //@ pure
                  public static int m(Integer ... ints) {
                    //@ assert ints != null;
                    return ints.length; }
                  public static void n(/*@ non_null*/Integer[] args) {
                    int i = m(args);
                    //@ assert i == args.length;
                    }
                  public static void n0() {
                    int i = m();
                    //@ assert i == 0;
                    }
                  public static void n1() {
                    int i = m(1);
                    //@ assert i == 1;
                    }
                  public static void n2() {
                    int i = m(1,1);
                    //@ assert i == 2;
                    }
                }
                """
                );
    }

    @Test
    public void testVarargs2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures \\result == (ints.length > 0 ? ints[0] : (int)ints.length);
                  //@ pure
                  public static int m(int ... ints) {
                    //@ assert ints != null;
                    if (ints.length > 0) return ints[0]; else return ints.length; }
                  public static void n0() {
                    int i = m();
                    //@ assert i == 0;
                    }
                  public static void n1() {
                    int i = m(2);
                    //@ assert i == 2;
                    }
                  public static void n2() {
                    int i = m(5,6);
                    //@ assert i == 5;
                    }
                }
                """
                );
    }

    @Test @Ignore // times out
    public void testVarargs3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires ints.length == 0 || ints[0] != null;
                  //@ ensures \\result == (ints.length > 0 ? ints[0] : (int)ints.length);
                  //@ pure
                  public static int m(Integer ... ints) {
                    //@ assert ints != null;
                    if (ints.length > 0) return ints[0]; else return ints.length; }
                  public static void n0() {
                    int i = m();
                    //@ assert i == 0;
                    }
                  public static void n1() {
                    int i = m(2);
                    //@ assert i == 2;
                    }
                  public static void n2() {
                    int i = m(5,6);
                    //@ assert i == 5;
                    }
                }
                """
                );
    }


    @Test
    public void testBits() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                     boolean b = true;
                     boolean bb = false;
                     //@ assert !(b & bb);
                     //@ assert (b | bb);
                     //@ assert (b ^ bb);
                     //@ assert (b & bb);
                    }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m",10
                );

    }

    @Test
    public void testLabels() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires iii == 10;
                  public void m(int iii) {
                     a:;
                     iii = 12;
                     b:{};
                     iii = 14;
                     //@ check \\old(iii) == 10;
                     //@ check \\old(iii,a) == 10;
                     //@ check \\old(iii,b) == 12;
                     //@ check iii == 14;
                    }
                }
                """
                );
    }

    @Test
    public void testGhostLabels() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires iii == 10;
                  public void m(int iii) {
                     //@ a:;
                     iii = 12;
                     //@ b:{};
                     iii = 14;
                     //@ check \\old(iii) == 10;
                     //@ check \\old(iii,a) == 10;
                     //@ check \\old(iii,b) == 12;
                     //@ check iii == 14;
                    }
                }
                """
                );
    }

     @Test
    public void testLabels2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k;
                  /*@ ensures \\result == k; pure */ public int mm() { return k; }
                  //@ requires k == 10;
                  public void m() {
                     a:{}
                     k = 12;
                     b:{}
                     k = 14;
                     //@ check \\old(mm()) == 10;
                     //@ check \\old(mm(),a) == 10;
                     //@ check \\old(mm(),b) == 12;
                     //@ check mm() == 14;
                    }
                }
                """
                );

    }

    @Test
    public void testOldClause() {
    	main.addOptions("-escMaxWarnings=1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int k = 5;
                  //@ old int kk = k; requires k == 5 && i > kk && i < 100 && i > -100; assignable k; ensures k == i+1; ensures kk == 5;
                  //@ also
                  //@ old int kk = k+1; requires k == 5 && i < kk && i < 100 && i > -100; assignable k; ensures k == i-1; ensures kk == 6;
                  static public void m(int i) {
                     if (i>k) k = i+1; else k = i-1;
                  }
                }
                """
                );

    }

    @Test // Can reuse labels but not nest them
    public void testLabelScopeBad() {
        expectedExit = 1;
        main.addOptions("-show","-method=m");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k;
                  public void m() {
                     //@ assert \\old(k,a) == 10;
                     a:{}
                     k = 12;
                     while(k > 10) {  a:{} k--; }
                     while(k > 6) {  b:{ b:{} } k--; }
                     while(k > 5) {  b:{} b:{} k--; }
                     while(k > 0) {  c:{} k--;}
                     k = 14;
                     //@ assert \\old(k,c) == 12;
                    }
                }
                """
                ,"/tt/TestJava.java:5: error: Unknown label: a", 24
                ,"/tt/TestJava.java:9: error: label b already in use", 26
                );


    }

    @Test // Can reuse labels but not nest them
    public void testLabelScope() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int k;
                  public void m() {
                     int x = 100;
                     d:{}
                     x = 101;
                     //@ assert 100 == \\old(x,d);
                     d:{}
                     x = 102;
                     //@ assert 101 == \\old(x,d);
                     d:{}
                     x = 103;
                     //@ assert 102 == \\old(x,d);
                    }
                }
                """
                );


    }

    @Test
    public void testPreconditionOnly() {
        addOptions("--check-feasibility=preconditionOnly");
        // preconditionOnly just checks that the preconditions+invariants are feasible; it does not check
        // the body of a method
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i > -10 && i < 10;
                  public void m(int i) {
                     //@ assert i != i;
                    }

                  //@ requires i > 0;
                  //@ requires i < 0;
                  public void mm(int i) {
                     //@ assert i != i;
                    }
                  //@ requires i > 0;
                  //@ ensures \\result > 0;
                  public int mmm(int i) {
                     return -i;
                    }
                }
                """
                ,"/tt/TestJava.java:10: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.mm(int)",15
                );


    }

    @Test
    public void testIfNoBrace() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i > -10 && i < 10;
                  public void m(int i) {
                     if (i < 0)\s
                        //@ assert i < 0;
                        i = -i;\s
                     //@ assert i >= 0;
                    }
                }
                """
                );


    }

    @Test
    public void testIfNoBrace2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i > -10 && i < 10;
                  public void m(int i) {
                     if (i < 0)\s
                        i = -i;\s
                        //@ assert i < 0;
                     //@ assert i >= 0;
                    }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m", 13
                );


    }

    @Test
    public void testIfNoBrace3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires i > -10 && i < 10;
                  public void m(int i) {
                     if (i < 0)\s
                        i = -i;\s
                        //@ assert i > 0;
                     //@ assert i >= 0;
                    }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assert) in method m", 13
                );


    }

    @Test
    public void testOldClause2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int k = 5;
                  //@ old int kk = k;
                  //@ {| requires i < 10 && i > kk; assignable k; ensures k == i+1;\s
                  //@ also
                  //@    requires i > -10 && i < kk; assignable k; ensures k == i-1;\s
                  //@ |}
                  static public void m(int i) {
                     if (i>k) k = i+1; else k = i-1;
                  }
                }
                """
                );

    }

    // Problem from Michael Coblenz - git issue #504
    @Test
    public void testSimpleClone() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public String y = "";
                 \s
                  public int[] foo() {
                     int[] result1 = new int[]{1};
                     int[] result2 = result1.clone();
                     return result2;
                  }
                }
                """
                );

    }

    @Test
    public void testTriggers() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures \\result == i>=0;\s
                  //@ pure
                  public boolean bb(int i) { return i >= 0; }
                  public void foo() { int j;
                     //@ assert (\\forall int i; 0<=i ; bb(i) : bb(i));
                     //@ assert (\\forall int i; 0<=i ; i>=-1 : i>=0, i<=0);
                  }
                }
                """
                );
    }

    @Test
    public void testTriggersBad() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ pure
                  public boolean bb(int i) { return i >= 0; }
                  public void foo() { int j;
                     //@ assert (\\forall int i; 0<=i ; bb(i) : );
                     //@ assert (\\forall boolean i;  ; i : bb(i));
                     //@ assert 0 == (\\sum int i; 0<=i ; i : i);
                  }
                }
                """
                ,"/tt/TestJava.java:7: error: incompatible types: boolean cannot be converted to int",47
                ,"/tt/TestJava.java:8: warning: Triggers only recognized in \\forall or \\exists quantified expressions",46
                );
    }

    @Test
    public void testExceptionNegativeIndex() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     int j = a[i];
                  }
                  //@ public normal_behavior
                  public void fooA(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     try { int j = a[i]; } catch (ArrayIndexOutOfBoundsException e) {}
                  }
                  //@ public normal_behavior
                  public void fooB(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume 1 < a.length;
                     //@ assume i < a.length;
                     try { int j = a[0]; } catch (ArrayIndexOutOfBoundsException e) {}
                     int j = a[i];
                  }
                  //@ public normal_behavior
                  public void fooC(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     try { int j = a[i]; } catch (IndexOutOfBoundsException e) {}
                  }
                  //@ public normal_behavior
                  public void fooD(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume 1 < a.length;
                     //@ assume i < a.length;
                     try { int j = a[0]; } catch (NullPointerException e) {}
                     int j = a[i]; // Old error
                  }
                  //@ public normal_behavior requires i >= -1;
                  //@ also public exceptional_behavior requires i < -1; signals_only RuntimeException;
                  public void fooE(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     int j = a[i];  } // New error
                  //@ public normal_behavior requires i >= 0;
                  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;
                  public void fooF(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     int j = a[i];  } // No error
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method foo",15
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooB",15
                ,"/tt/TestJava.java:35: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooD",15
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooE",15
                ,"/tt/TestJava.java:37: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionNegativeIndexAssign() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     a[i] = 0;
                  }
                  //@ public normal_behavior
                  public void fooA(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     try { a[i] = 0; } catch (ArrayIndexOutOfBoundsException e) {}
                  }
                  //@ public normal_behavior
                  public void fooB(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume 1 < a.length;
                     //@ assume i < a.length;
                     try { a[i] = 0; } catch (ArrayIndexOutOfBoundsException e) {}
                     a[i] = 0;
                  }
                  //@ public normal_behavior
                  public void fooC(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     try { a[i] = 0; } catch (IndexOutOfBoundsException e) {}
                  }
                  //@ public normal_behavior
                  public void fooD(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume 1 < a.length;
                     //@ assume i < a.length;
                     try { a[i] = 0; } catch (NullPointerException e) {}
                     a[i] = 0; // Old error
                  }
                  //@ public normal_behavior requires i >= -1;
                  //@ also public exceptional_behavior requires i < -1; signals_only RuntimeException;
                  public void fooE(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     a[i] = 0;  } // New error
                  //@ public normal_behavior requires i >= 0;
                  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;
                  public void fooF(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     a[i] = 0;  } // No error
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method foo",7
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooB",7
                ,"/tt/TestJava.java:34: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooD",13
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooE",7
                ,"/tt/TestJava.java:37: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionNegativeIndexAssignOp() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     a[i] += 0;
                  }
                  //@ public normal_behavior
                  public void fooA(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     try { a[i] += 0; } catch (ArrayIndexOutOfBoundsException e) {}
                  }
                  //@ public normal_behavior
                  public void fooB(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume 1 < a.length;
                     //@ assume i < a.length;
                     try { a[i] += 0; } catch (ArrayIndexOutOfBoundsException e) {}
                     a[i] += 0;
                  }
                  //@ public normal_behavior
                  public void fooC(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     try { a[i] += 0; } catch (IndexOutOfBoundsException e) {}
                  }
                  //@ public normal_behavior
                  public void fooD(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume 1 < a.length;
                     //@ assume i < a.length;
                     try { a[i] += 0; } catch (NullPointerException e) {}
                     a[i] += 0; // Old error
                  }
                  //@ public normal_behavior requires i >= -1;
                  //@ also public exceptional_behavior requires i < -1; signals_only RuntimeException;
                  public void fooE(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     a[i] += 0;  } // New error
                  //@ public normal_behavior requires i >= 0;
                  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;
                  public void fooF(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i < a.length;
                     a[i] += 0;  } // No error
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method foo",7
                ,"/tt/TestJava.java:21: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooB",7
                ,"/tt/TestJava.java:34: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method fooD",13
                ,"/tt/TestJava.java:42: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooE",7
                ,"/tt/TestJava.java:37: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionTooLargeIndex() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i >= 0;
                     int j = a[i];
                  }
                  //@ public normal_behavior
                  public void fooA(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i >= 0;
                     try { int j = a[i]; } catch (ArrayIndexOutOfBoundsException e) {}  }
                  //@ public normal_behavior requires 0 <= i && i <= a.length;
                  //@ also public exceptional_behavior requires i > a.length+1; signals_only RuntimeException;
                  public void fooB(int[] a, int i) {
                     int j = a[i];
                  }
                  //@ public normal_behavior requires 0 <= i && i < a.length;
                  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;
                  public void fooC(int[] a, int i) {
                     int j = a[i];
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method foo",15
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:14: verify: Associated declaration",14
                );
    }
    @Test
    public void testExceptionTooLargeIndexAssign() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i >= 0;
                     a[i] = 0;
                  }
                  //@ public normal_behavior
                  public void fooA(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i >= 0;
                     try { a[i] = 0; } catch (ArrayIndexOutOfBoundsException e) {}  }
                  //@ public normal_behavior requires 0 <= i && i <= a.length;
                  //@ also public exceptional_behavior requires i > a.length+1; signals_only RuntimeException;
                  public void fooB(int[] a, int i) {
                     a[i] = 0;
                  }
                  //@ public normal_behavior requires 0 <= i && i < a.length;
                  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;
                  public void fooC(int[] a, int i) {
                     a[i] = 0;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method foo",7
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:14: verify: Associated declaration",14
                );
    }
    @Test
    public void testExceptionTooLargeIndexAssignOp() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i >= 0;
                     a[i]+= 0;
                  }
                  //@ public normal_behavior
                  public void fooA(int[] a, int i) {
                     //@ assume a != null;
                     //@ assume i >= 0;
                     try { a[i]+= 0; } catch (ArrayIndexOutOfBoundsException e) {}  }
                  //@ public normal_behavior requires 0 <= i && i <= a.length;
                  //@ also public exceptional_behavior requires i > a.length+1; signals_only RuntimeException;
                  public void fooB(int[] a, int i) {
                     a[i]+= 0;
                  }
                  //@ public normal_behavior requires 0 <= i && i < a.length;
                  //@ also public exceptional_behavior requires i < 0; signals_only RuntimeException;
                  public void fooC(int[] a, int i) {
                     a[i]+= 0;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method foo",7
                ,"/tt/TestJava.java:17: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:14: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionDivZero() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int a) {
                     int j = 1/a;
                  }
                  //@ public normal_behavior
                  public void fooA(int a) {
                     try { int j = 1/a; } catch (ArithmeticException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only ArithmeticException;
                  public void fooB(int a) {
                     int j = 1/a;
                  }
                  //@ public normal_behavior requires a != 0;
                  //@ also public exceptional_behavior requires a == 0; signals_only ArithmeticException;
                  public void fooC(int a) {
                     int j = 1/a;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyDivideByZero) in method foo",15
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:11: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionArrayStore() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  Object[] oo = new String[10];  //@ invariant oo.length > 1;\s
                  //@ public normal_behavior
                  public void foo(int a) {
                     oo[0] = 1;
                  }
                  //@ public normal_behavior
                  public void fooA(int a) {
                     try { oo[0] = 1; } catch (ArrayStoreException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only ArrayStoreException;
                  public void fooB(int a) {
                     oo[0] = 1;
                  }
                  //@ public normal_behavior requires \\type(Integer) <:= \\elemtype(\\typeof(ooo)) ;
                  //@ also public exceptional_behavior requires !(\\type(Integer) <:= \\elemtype(\\typeof(ooo))); signals_only ArrayStoreException;
                  public void fooC(Object[] ooo, int a) {
                     //@ assume ooo.length > 1 ;
                     ooo[0] = 1;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyBadArrayAssignment) in method foo",12
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",12
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionCallNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  /*@ public normal_behavior */ public int m() { return 0; }
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ TestJava a) {
                     int j = a.m();
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ TestJava a) {
                     try { int j = a.m(); } catch (NullPointerException e) {}  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ TestJava a) {
                     int j = a.m();
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ TestJava a) {
                     int j = a.m();
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",15
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:11: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionNewNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  class A {}
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ TestJava a) {
                     A j = a.new A();
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ TestJava a) {
                     try { A j = a.new A(); } catch (NullPointerException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ TestJava a) {
                     A j = a.new A();
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ TestJava a) {
                     A j = a.new A();
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",12
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",12
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionUnboxNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  class A {}
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ Integer a) {
                     int j = (int)a;
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ Integer a) {
                     try { int j = (int)a; } catch (NullPointerException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ Integer a) {
                     int j = (int)a;
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ Integer a) {
                     int j = (int)a;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method foo",19
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",19
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionUnboxImplicitNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  class A {}
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ Integer a) {
                     int j = a;
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ Integer a) {
                     try { int j = a; } catch (NullPointerException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ Integer a) {
                     int j = a;
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ Integer a) {
                     int j = a;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullUnbox) in method foo",14
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",14
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionAssignNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  class A { int x; }
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ A a) {
                     a.x = 1;
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ A a) {
                     try { a.x = 1; } catch (NullPointerException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ A a) {
                     a.x = 1;
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ A a) {
                     a.x = 1;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionAssignOpNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  class A { int x; }
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ A a) {
                     a.x += 0;
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ A a) {
                     try { a.x += 0; } catch (NullPointerException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ A a) {
                     a.x += 0;
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ A a) {
                     a.x += 0;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionSwitchNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  enum A { X,Y; };
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ A a) {
                     switch (a) {};
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ A a) {
                     try { switch (a) {}; } catch (NullPointerException e) {} // OK - possibly null is caught
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ A a) {
                     switch (a) {}; // ERROR - possibly null is not expected because of null precondition
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ A a) {
                     switch(a) {}; // OK - possibly null is expected
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullValue) in method foo",13
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",13
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionSynchNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  class A { }
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ A a) {
                     synchronized (a) {};
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ A a) {
                     try { synchronized (a) {}; } catch (NullPointerException e) {}
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ A a) {
                     synchronized (a) {};
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ A a) {
                     synchronized(a) {};
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullValue) in method foo",19
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",19
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionThrowNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  class A extends RuntimeException {}
                  //@ public behavior signals_only A;
                  public void foo(/*@ nullable */ A a) {
                     throw a;
                  }
                  //@ public behavior signals_only A;
                  public void fooA(/*@ nullable */ A a) {
                     try { throw a; } catch (NullPointerException e) {}
                  }
                  //@ public behavior signals_only A;
                  //@ also public exceptional_behavior requires false; signals_only A, NullPointerException;
                  public void fooB(/*@ nullable */ A a) {
                     throw a ;
                  }
                  //@ public behavior requires a != null; signals_only A;
                  //@ also public exceptional_behavior requires a == null; signals_only A, NullPointerException;
                  public void fooC(/*@ nullable */ A a) {
                     throw a;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullValue) in method foo",12
                ,"/tt/TestJava.java:15: verify: The prover cannot establish an assertion (ExceptionList) in method fooB",12
                ,"/tt/TestJava.java:12: verify: Associated declaration",23
                );
    }

    @Test
    public void testExceptionArrayNull() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo( int/*@ nullable */[] a) {
                     //@ assume a != null ==> a.length > 1;
                     int j = a[0];
                  }
                  //@ public normal_behavior
                  public void fooA( int/*@ nullable */[] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     try { int j = a[0]; } catch (NullPointerException e) {}  }
                  //@ public normal_behavior requires i>0;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(int/*@ nullable */[] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     int j = a[0];
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(int/*@ nullable */ [] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     int j = a[0];
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",15
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionArrayNullAssign() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int /*@ nullable */ [] a) {
                     //@ assume a != null ==> a.length > 1;
                     a[0] = 0;
                  }
                  //@ public normal_behavior
                  public void fooA(int /*@ nullable */ [] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     try { a[0] = 0; } catch (NullPointerException e) {}  }
                  //@ public normal_behavior requires i>0;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(int /*@ nullable */ [] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     a[0] = 0;
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(int /*@ nullable */ [] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     a[0] = 0;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionArrayNullAssignOp() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int /*@ nullable */ [] a) {
                     //@ assume a != null ==> a.length > 1;
                     a[0] += 0;
                  }
                  //@ public normal_behavior
                  public void fooA(int /*@ nullable */ [] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     try { a[0] = 0; } catch (NullPointerException e) {}  }
                  //@ public normal_behavior requires i>0;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(int /*@ nullable */ [] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     a[0] = 0;
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(int /*@ nullable */ [] a, int i) {
                     //@ assume a != null ==> a.length > 1;
                     a[0] = 0;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",7
                ,"/tt/TestJava.java:16: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",7
                ,"/tt/TestJava.java:12: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionDeref() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public static class A { public int x; }
                  //@ public normal_behavior
                  public void foo(/*@ nullable */ A a) {
                     int j = a.x;
                  }
                  //@ public normal_behavior
                  public void fooA(/*@ nullable */ A a) {
                     try { int j = a.x; } catch (NullPointerException e) {}
                  }
                  public void fooAA(/*@ nullable */ A a, NullPointerException en) {//@ assume a == null & en != null;\s
                     try { int j = a.x; } catch (NullPointerException e) {/*@ assert a == null; */ }
                     int k = a.x;
                  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NullPointerException;
                  public void fooB(/*@ nullable */ A a) {
                     int j = a.x;
                  }
                  //@ public normal_behavior requires a != null;
                  //@ also public exceptional_behavior requires a == null; signals_only NullPointerException;
                  public void fooC(/*@ nullable */ A a) {
                     int j = a.x;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method foo",15
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method fooAA",15
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",15
                ,"/tt/TestJava.java:16: verify: Associated declaration",14
                );
    }

    @Test
    public void testExceptionNegArraySize() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ public normal_behavior
                  public void foo(int n) {
                     int[] j = new int[n];
                  }
                  //@ public normal_behavior
                  public void fooA(int n) {
                     try { int[] j = new int[n]; } catch (NegativeArraySizeException e) {}  }
                  //@ public normal_behavior requires true;
                  //@ also public exceptional_behavior requires false; signals_only NegativeArraySizeException;
                  public void fooB(int n) {
                     int[] j = new int[n];
                  }
                  //@ public normal_behavior requires n >= 0;
                  //@ also public exceptional_behavior requires n < 0; signals_only NegativeArraySizeException;
                  public void fooC(int n) {
                     int[] j = new int[n];
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNegativeSize) in method foo",24
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method fooB",24
                ,"/tt/TestJava.java:10: verify: Associated declaration",14
                );
    }

    @Test
    public void testInvariants() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ ensures \\result == (\\lbl BYTES Integer.BYTES);
                  public int foo() {
                     return 4;
                  }
                }
                """
                );
    }

    @Test
    public void testInstanceOfA() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  //@ requires a instanceof TestJava && ((TestJava)a).k == 42;
                  public void m(A a) {
                    if (a instanceof TestJava t) {
                       //@ check t.k == 42;
                       //@ check t.k == 43; // ERROR
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m", 12
                );
    }

    @Test
    public void testInstanceOfB() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  //@ requires a instanceof TestJava tt && tt.k == 42;
                  public void m(A a) {
                    if (a instanceof TestJava t) {
                       //@ check t.k == 42;
                       //@ check t.k == 43; // ERROR
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Assert) in method m", 12
                );
    }

    @Test
    public void testInstanceOfC() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  //@ requires a instanceof TestJava tt && tt.k == 42;
                  public void m(A a) {
                    if (a instanceof TestJava t && t.k == 42) {
                        //@ unreachable; // ERROR is reachable
                    } else {
                        //@ unreachable; // OK
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Unreachable) in method m", 13
                );
    }

    @Test
    public void testInstanceOfD() {
        helpEsc("tt.TestJava",
                """
                package tt;
                class A {}
                public class TestJava extends A {
                  public int k;
                  public void m() {
                    //@ check \\forall A a; a != null; (a instanceof TestJava t && t.k == 42);
                  }
                }
                """
                ,"/tt/TestJava.java:6: warning: Not implemented for static checking: binding pattern in this location", 53
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assert) in method m", 9
                );
    }
}
