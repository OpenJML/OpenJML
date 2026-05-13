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
public class escnewassignable extends EscBase {

    // Forms to test: x, this.x, , this.*
    // xx, T.xx, tt.T.x, T.* tt.T.*
    // o.x o.oo.x, m(o).x o.*, o.oo.*, m(o).* 
    // a[i].x a[i].* a[*].x a[*].* a[i .. j].x a[i ..*].x a[*..j].x a[*..*].x a[i .. j].* a[i ..*].* a[*..j].* a[*..*].*
    // a[i] a[i..j] a[*] a[i..*] a[*..j] a[*..*]
    // \everything \nothing 
    
    @Test
    public void testAssignable1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int x,y;
                  //@ assignable x;
                  public void m1bad(int i) {
                    y = 0 ;
                  }
                  //@ assignable x;
                  public void m1good(int i) {
                    x = 0 ;
                    i = 0; ;
                    int k = 0; ;
                    k = 0; ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable) in method m1bad: y",7
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testAssignable2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int x;
                  //@ requires i > 0;
                  //@ assignable x;
                  public void mgood(int i) {
                    x = 0 ;
                  }
                  //@ requires i > 0;
                  //@ assignable x;
                  public void m1good(int i) {
                    if (i > 0) x = 0 ;
                  }
                }
                """);
    }

    @Test
    public void testAssignable3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int x,y;
                  //@ requires i > 0;
                  //@ assignable x;
                  //@ also
                  //@ requires i == 0;
                  //@ assignable y;
                  public void m1bad(int i) {
                    x = 0 ;
                  }
                  //@ requires i > 0;
                  //@ assignable x;
                  //@ also
                  //@ requires i == 0;
                  //@ assignable y;
                  public void m1good(int i) {
                    if (i > 0) x = 0 ;
                    if (i == 0) y = 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assignable) in method m1bad: x",7
                ,"/tt/TestJava.java:8: verify: Associated declaration",7
                );
    }

    @Test
    public void testAssignable4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int x,y;
                  //@ requires i > 0;
                  //@ assignable x;
                  //@ also
                  //@ requires i == 0;
                  //@ assignable y;
                  public void m1bad(int i) {
                    i = 0 ;
                    y = 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:11: verify: The prover cannot establish an assertion (Assignable) in method m1bad: y",7
                ,"/tt/TestJava.java:5: verify: Associated declaration",7
                );
    }

    @Test
    public void testAssignable5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int x,xx; public static int y,yy;
                  //@ assignable this.x;
                  public void m1bad(int i) {
                    y = 0 ;
                  }
                  //@ assignable this.x;
                  public void m2bad(int i) {
                    xx = 0 ;
                  }
                  //@ assignable TestJava.y;
                  public void m3bad(int i) {
                    yy = 0 ;
                  }
                  //@ assignable TestJava.y;
                  public void m4bad(int i) {
                    x = 0 ;
                  }
                  //@ assignable tt.TestJava.y;
                  public void m5bad(int i) {
                    yy = 0 ;
                  }
                  //@ assignable tt.TestJava.y;
                  public void m6bad(int i) {
                    x = 0 ;
                  }
                  //@ assignable this.x;
                  public void m1good(int i) {
                    x = 0 ;
                  }
                  //@ assignable TestJava.y;
                  public void m2good(int i) {
                    y = 0 ;
                  }
                  //@ assignable tt.TestJava.y;
                  public void m3good(int i) {
                    y = 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable) in method m1bad: y",7
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assignable) in method m2bad: xx",8
                ,"/tt/TestJava.java:8: verify: Associated declaration",7
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assignable) in method m3bad: yy",8
                ,"/tt/TestJava.java:12: verify: Associated declaration",7
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assignable) in method m4bad: x",7
                ,"/tt/TestJava.java:16: verify: Associated declaration",7
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Assignable) in method m5bad: yy",8
                ,"/tt/TestJava.java:20: verify: Associated declaration",7
                ,"/tt/TestJava.java:26: verify: The prover cannot establish an assertion (Assignable) in method m6bad: x",7
                ,"/tt/TestJava.java:24: verify: Associated declaration",7
                );
    }

    @Test
    public void testAssignable6() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int x,xx; static public int y,yy;
                  //@ assignable this.*;
                  public void m1bad(int i) {
                    y = 0 ;
                  }
                  //@ assignable TestJava.*;
                  public void m2bad(int i) {
                    x = 0 ;
                  }
                  //@ assignable tt.TestJava.*;
                  public void m3bad(int i) {
                    x = 0 ;
                  }
                  //@ assignable this.*;
                  public void m1good(int i) {
                    x = 0 ;
                  }
                  //@ assignable TestJava.*;
                  public void m2good(int i) {
                    y = 0 ;
                  }
                  //@ assignable tt.TestJava.*;
                  public void m3good(int i) {
                    y = 0 ;
                  }
                  //@ requires true;
                  //@ assignable y;
                  //@ also requires true;
                  //@ assignable this.*;
                  public void m0bad(int i) {
                    x = 0 ;
                  }
                  //@ requires true;
                  //@ assignable y;
                  //@ assignable this.*;
                  public void m00bad(int i) {
                    x = 0 ;
                  }
                  //@ requires true;
                  //@ assignable y, this.*;
                  public void m00good(int i) {
                    x = 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (Assignable) in method m1bad: y",7
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Assignable) in method m2bad: x",7
                ,"/tt/TestJava.java:8: verify: Associated declaration",7
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assignable) in method m3bad: x",7
                ,"/tt/TestJava.java:12: verify: Associated declaration",7
                ,"/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Assignable) in method m0bad: x",7
                ,"/tt/TestJava.java:29: verify: Associated declaration",7
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (Assignable) in method m00bad: x",7
                ,"/tt/TestJava.java:36: verify: Associated declaration",7
                );
    }

    @Test
    public void testAssignable7() {
        //addOptions("--show","--method=m4bad");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  int x,xx; static int y,yy; /*@ spec_public */ int[] z;
                  //@ assignable \\everything;
                  public void m1good(int i, TestJava a) {
                    y = 0 ;
                    x = 0 ;
                    i = 0 ;
                    this.x = 0 ;
                    this.y = 0 ;
                    a.x = 0 ;
                    a.y = 0 ;
                    TestJava.y = 0 ;
                    //@ assume z != null && z.length > 1;
                    z[0] = 0 ;
                  }
                  //@ assignable \\nothing;
                  public void m1bad(int i, TestJava a) {
                    y = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m2bad(int i, TestJava a) {
                    x = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m3good(int i, TestJava a) {
                    i = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m4bad(int i, TestJava a) {
                    this.x = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m5bad(int i, TestJava a) {
                    this.y = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m6bad(int i, TestJava a) {
                    a.x = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m7bad(int i, TestJava a) {
                    a.y = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m8bad(int i, TestJava a) {
                    TestJava.y = 0 ;
                  }

                  //@ assignable \\nothing;
                  public void m9bad(int i, TestJava a) {
                    //@ assume z != null && z.length > 1;
                    z[0] = 0 ;
                  }
                  public TestJava() { z = new int[10];}
                }
                """
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assignable) in method m1bad: y",7
                ,"/tt/TestJava.java:17: verify: Associated declaration",7
                ,"/tt/TestJava.java:24: verify: The prover cannot establish an assertion (Assignable) in method m2bad: x",7
                ,"/tt/TestJava.java:22: verify: Associated declaration",7
                ,"/tt/TestJava.java:34: verify: The prover cannot establish an assertion (Assignable) in method m4bad: this.x",12
                ,"/tt/TestJava.java:32: verify: Associated declaration",7
                ,"/tt/TestJava.java:39: verify: The prover cannot establish an assertion (Assignable) in method m5bad: this.y",12
                ,"/tt/TestJava.java:37: verify: Associated declaration",7
                ,"/tt/TestJava.java:44: verify: The prover cannot establish an assertion (Assignable) in method m6bad: a.x",9
                ,"/tt/TestJava.java:42: verify: Associated declaration",7
                ,"/tt/TestJava.java:49: verify: The prover cannot establish an assertion (Assignable) in method m7bad: a.y",9
                ,"/tt/TestJava.java:47: verify: Associated declaration",7
                ,"/tt/TestJava.java:54: verify: The prover cannot establish an assertion (Assignable) in method m8bad: TestJava.y",16
                ,"/tt/TestJava.java:52: verify: Associated declaration",7
                ,"/tt/TestJava.java:60: verify: The prover cannot establish an assertion (Assignable) in method m9bad: z[0]",10
                ,"/tt/TestJava.java:57: verify: Associated declaration",7
                );
    }

    @Test
    public void testAssignable8() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int /*@ nullable */ [] z;
                  //@ public invariant z != null && z.length > 10;
                  //@ requires a != null && a.length > 10;
                  //@ assignable a[1];
                  public void m1good(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable z[1];
                  public void m1bad(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable a[*];
                  public void m2good(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable z[*];
                  public void m2bad(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable a[0..3];
                  public void m3good(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable z[0..3];
                  public void m3bad(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable a[2..3];
                  public void m3bad1(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable a[0..0];
                  public void m3bad2(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable a[0..*];
                  public void m4good(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable z[0..*];
                  public void m4bad(int i, int[] a) {
                    a[1] = 0 ;
                  }
                  //@ requires a != null && a.length > 10;
                  //@ assignable a[2..*];
                  public void m4bad1(int i, int[] a) {
                    a[1] = 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:2: verify: The prover cannot establish an assertion (InvariantExit) in method TestJava",8
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assignable) in method m1bad: a[1]",10
                ,"/tt/TestJava.java:11: verify: Associated declaration",7
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assignable) in method m2bad: a[1]",10
                ,"/tt/TestJava.java:21: verify: Associated declaration",7
                ,"/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Assignable) in method m3bad: a[1]",10
                ,"/tt/TestJava.java:31: verify: Associated declaration",7
                ,"/tt/TestJava.java:38: verify: The prover cannot establish an assertion (Assignable) in method m3bad1: a[1]",10
                ,"/tt/TestJava.java:36: verify: Associated declaration",7
                ,"/tt/TestJava.java:43: verify: The prover cannot establish an assertion (Assignable) in method m3bad2: a[1]",10
                ,"/tt/TestJava.java:41: verify: Associated declaration",7
                ,"/tt/TestJava.java:53: verify: The prover cannot establish an assertion (Assignable) in method m4bad: a[1]",10
                ,"/tt/TestJava.java:51: verify: Associated declaration",7
                ,"/tt/TestJava.java:58: verify: The prover cannot establish an assertion (Assignable) in method m4bad1: a[1]",10
                ,"/tt/TestJava.java:56: verify: Associated declaration",7
                );
    }

    @Test
    public void testAssignable9() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int i; static public int si; @org.jmlspecs.annotation.NonNull public TestJava b;
                  //@ assignable a.i;
                  public void m1good(TestJava a) {
                    a.i = 0 ;
                  }
                  //@ assignable a.*;
                  public void m2good(TestJava a) {
                    a.i = 0 ;
                  }
                  //@ assignable b.i;
                  public void m1bad(TestJava a) {
                    a.i = 0 ;
                  }
                  //@ assignable b.*;
                  public void m2bad(TestJava a) {
                    a.i = 0 ;
                  }
                  //@ assignable a.si;
                  public void m3bad(TestJava a) {
                    a.i = 0 ;
                  }
                  //@ requires a == b;
                  //@ assignable b.i;
                  public void m4good(TestJava a) {
                    a.i = 0 ;
                  }
                  //@ requires a == this;
                  //@ assignable i;
                  public void m5good(TestJava a) {
                    a.i = 0 ;
                  }
                  public TestJava() { b = new TestJava(); }
                }
                """
                ,"/tt/TestJava.java:14: verify: The prover cannot establish an assertion (Assignable) in method m1bad: a.i",9
                ,"/tt/TestJava.java:12: verify: Associated declaration",7
                ,"/tt/TestJava.java:18: verify: The prover cannot establish an assertion (Assignable) in method m2bad: a.i",9
                ,"/tt/TestJava.java:16: verify: Associated declaration",7
                ,"/tt/TestJava.java:22: verify: The prover cannot establish an assertion (Assignable) in method m3bad: a.i",9
                ,"/tt/TestJava.java:20: verify: Associated declaration",7
                );
    }

    @Test 
    public void testAssignableM1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public class A { public int x,y; public static int xx,yy; }
                  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a;
                  //@ assignable y, A.xx, a.x, this.y, TestJava.yy, tt.TestJava.yy;
                  public void m1bad(int i) {
                    m();
                  }
                  //@ assignable x;
                  public void m1good(int i) {
                    m();
                  }
                  //@ assignable this.x;
                  public void m2good(int i) {
                    m();
                  }
                  //@ assignable y, A.xx, a.xx, a.x, this.y, TestJava.yy, tt.TestJava.yy; //@ requires a != null;
                  public void m3bad(int i) {
                    ms();
                  }
                  //@ assignable x;
                  public void m() {
                  }
                  //@ assignable xx;
                  public void ms() {
                  }
                 public TestJava() { a = new A(); }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Assignable) in method m1bad: x",6
                ,"/tt/TestJava.java:5: verify: Associated declaration",7
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assignable) in method m3bad: xx",7
                ,"/tt/TestJava.java:17: verify: Associated declaration",7

                );
    }

    @Test 
    public void testAssignableM2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public class A { public int x,y; public static int xx,yy; }
                  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a;

                  //@ assignable xx;
                  public void m3good(int i) {
                    ms();
                  }

                  //@ assignable TestJava.xx;
                  public void m3agood(int i) {
                    ms();
                  }

                  //@ assignable tt.TestJava.xx;
                  public void m3bgood(int i) {
                    ms();
                  }

                  //@ assignable this.xx;
                  public void m3cgood(int i) {
                    ms();
                  }

                  //@ assignable x;
                  public void m() {
                  }

                  //@ assignable xx;
                  public void ms() {
                  }

                 public TestJava() { a = new A(); }
                }
                """

                );
    }

    @Test 
    public void testAssignableM3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public class A { public int x,y; public static int xx,yy; }
                  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a;

                  //@ assignable x;
                  public void m() {
                  }

                  //@ assignable xx;
                  public void ms() {
                  }

                  //@ assignable this.x;
                  public void mt() {
                  }

                  //@ assignable TestJava.xx;
                  public void mts() {
                  }

                 public TestJava() { a = new A(); }
                }
                """

                );
    }

    @Test 
    public void testAssignableM4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public class A { public int x,y; public static int xx,yy; }
                  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a;
                  //@ assignable tt.TestJava.xx;
                  public void mtts() {
                  }
                  //@ assignable A.xx;
                  public void mas() {
                  }
                  //@ requires b == this;
                  //@ assignable x;
                  public void m1z1(TestJava b) {
                    b.m();
                  }
                  //@ requires b != null;
                  //@ assignable x;
                  public void m1z1bad(TestJava b) {
                    b.m();
                  }
                  //@ assignable x;
                  public void m() {
                  }
                 public TestJava() { a = new A(); }
                }
                """
                ,"/tt/TestJava.java:19: verify: The prover cannot establish an assertion (Assignable) in method m1z1bad: x",8
                ,"/tt/TestJava.java:17: verify: Associated declaration",7
                );
    }

    @Test 
    public void testAssignableM5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public class A { public int x,y; public static int xx,yy; }
                  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a;
                  //@ requires b != null;
                  //@ assignable b.x;
                  public void m1z2(TestJava b) {
                    b.m();
                  }
                  //@ requires b == this;
                  //@ assignable b.x;
                  public void m1z3(TestJava b) {
                    m();
                  }
                  //@ requires b == this;
                  //@ assignable b.x;
                  public void m1z4(TestJava b) {
                    this.m();
                  }
                  //@ requires b != null;
                  //@ assignable b.x;
                  public void m1z4bad(TestJava b) {
                    this.m();
                  }
                  //@ assignable x;
                  public void m() {
                  }
                 public TestJava() { a = new A(); }
                }
                """
                ,"/tt/TestJava.java:23: verify: The prover cannot establish an assertion (Assignable) in method m1z4bad: x",11
                ,"/tt/TestJava.java:21: verify: Associated declaration",7

                );
    }

    @Test 
    public void testAssignableM1bug() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public class A { int x,y; static int xx,yy; }
                  public int x,y; static public int xx,yy; @org.jmlspecs.annotation.NonNull public A a;
                  //@ requires a == this;
                  //@ assignable x;
                  public void m1z1(TestJava a) {
                    a.m();
                  }
                  //@ requires a != null;
                  //@ assignable x;
                  public void m1z1bad(TestJava a) {
                    a.m();
                  }
                  //@ requires a != null;
                  //@ assignable a.x;
                  public void m1z2(TestJava a) {
                    a.m();
                  }
                  //@ requires a == this;
                  //@ assignable a.x;
                  public void m1z3(TestJava a) {
                    m();
                  }
                  //@ requires a == this;
                  //@ assignable a.x;
                  public void m1z4(TestJava a) {
                    this.m();
                  }
                  //@ requires a != null;
                  //@ assignable a.x;
                  public void m1z4bad(TestJava a) {
                    this.m();
                  }
                  //@ assignable x;
                  public void m() {
                  }
                 public TestJava() { a = new A(); }
                }
                """
                ,"/tt/TestJava.java:13: verify: The prover cannot establish an assertion (Assignable) in method m1z1bad: x",8
                ,"/tt/TestJava.java:11: verify: Associated declaration",7
                ,"/tt/TestJava.java:33: verify: The prover cannot establish an assertion (Assignable) in method m1z4bad: x",11
                ,"/tt/TestJava.java:31: verify: Associated declaration",7

                );
    }
}
