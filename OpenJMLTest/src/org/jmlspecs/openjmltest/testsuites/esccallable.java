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
public class esccallable extends EscBase {

    @Test
    public void testBasicCallable() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable \\nothing;
                  public void m() {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n;
                  void m() { n(); }
                  //@ callable \\nothing;
                  void n() {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable \\nothing;
                  public void m() { n(); }
                  void n() {}
                }
                """
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n() is not callable",22
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",22
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                                 )
                );
    }

    @Test
    public void testBasicCallable4() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n;
                  void m() { p(); }
                  void n() {}
                  void p() {}
                }
                """
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.p() is not callable",15
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                                ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",15
                                        ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                          )
                );
    }

    @Test
    public void testBasicCallable5() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n;
                  void m() { B.n(); }
                  void n() {}
                  void p() {}
                }
                class B { public static void n() {} };
                """
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.B.n() is not callable",17
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",17
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         )
                );
    }

    @Test
    public void testBasicCallable6() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable TestJava.n;
                  void m() { B.n(); }
                  static void n() {}
                  void p() {}
                }
                class B { public static void n() {} };
                """
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.B.n() is not callable",17
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",17
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable7() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable B.n;
                  void m() { B.n(); }
                  void n() {}
                  void p() {}
                }
                class B {
                  //@ callable \\nothing;
                  public static void n() {} };
                """
                );
    }

    @Test
    public void testBasicCallable8() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(int);
                  void m() { n(1); }
                  //@ callable \\nothing;
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable9() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(Object);
                  void m() { n(1); }
                  //@ callable \\nothing;
                  void n(int i) {}
                  //@ callable \\nothing;
                  void n(Object o) {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(int) is not callable",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable10() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(int);
                  void m() { n(1); }
                  //@ callable n(Object);
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(Object) is not callable",16
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(int),n(Object);
                  void m() { n(1); }
                  //@ callable n(Object);
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable11a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(int),n(Object);
                  void m() { n(1); }
                  //@ callable \\everything;
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",16
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11b() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable \\everything;
                  void m() { n(1); }
                  //@ callable \\everything;
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable11c() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable \\nothing;
                  void m() { n(1); }
                  //@ callable \\everything;
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(int) is not callable",15
                                ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                         ,seq("/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",16
                                 ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable11d() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable \\nothing;
                  void m() { n(1); }
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                ,anyorder(seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n(int) is not callable",15
                            ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                          ,seq("/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",15
                                    ,"/tt/TestJava.java:3: verify: Associated declaration",7)
                           )
                );
    }

    @Test
    public void testBasicCallable11e() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(int);
                  void m() { n(1); }
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable11f() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable \\everything;
                  void m() { n(1); }
                  void n(int i) {}
                  void n(Object o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable12() {  // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n();
                  void m(Object o) { n(o); }
                  //@ callable \\nothing;
                  void n(Object ... o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable12a() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(Object,Object);
                  void m(Object o) { n(o); }
                  //@ callable \\nothing;
                  void n(Object ... o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable13() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(Object[]);
                  void m() { n(); }
                  //@ callable \\nothing;
                  void n(Object ... o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable14() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(Object[]);
                  void m(Object o) { n(o); }
                  //@ callable \\nothing;
                  void n(Object ... o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable15() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(Object[]);
                  void m(Object[] o) { n(o); }
                  //@ callable \\nothing;
                  void n(Object ... o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable16() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ callable n(Object[]);
                  void m(Object o) { n(o,o); }
                  //@ callable \\nothing;
                  void n(Object ... o) {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable20() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ callable n();
                  //@ also requires !b;
                  //@ callable \\nothing;
                  void m(boolean b) { if (b) n(); }
                  //@ callable \\nothing;
                  void n() {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable21() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ callable n();
                  //@ also requires !b;
                  //@ callable \\nothing;
                  void m(boolean b) { if (!b) n(); }
                  //@ callable \\nothing;
                  void n() {}
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n() is not callable",32
                ,"/tt/TestJava.java:6: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable21a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ callable n();
                  //@ also requires !b;
                  //@ callable \\nothing;
                  void m(boolean b) { if (!b) n(); }
                  void n() {}
                }
                """
                ,anyorder(seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: tt.TestJava.n() is not callable",32
                                ,"/tt/TestJava.java:6: verify: Associated declaration",7)
                            ,seq("/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",32
                                    ,"/tt/TestJava.java:6: verify: Associated declaration",7)
                        )
                );
    }

    @Test
    public void testBasicCallable21c() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ callable n();
                  //@ also requires !b;
                  //@ callable \\nothing;
                  void m(boolean b) { if (b) n(); }
                  void n() {}
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (Callable) in method m: \\everything is not callable",31
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    @Test
    public void testBasicCallable21b() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ callable n();
                  //@ also requires !b;
                  //@ callable \\everything;
                  void m(boolean b) { if (!b) n(); }
                  void n() {}
                }
                """
                );
    }

    @Test
    public void testBasicCallable22() { // OK
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ requires b;
                  //@ callable n(boolean);
                  //@ also requires !b;
                  //@ callable \\nothing;
                  void m(boolean b) { if (b) n(!b); }
                  //@ requires q;
                  //@ callable p();
                  //@ also requires !q;
                  //@ callable \\nothing;
                  void n(boolean q) {}
                  void p() {}
                }
                """
                );
    }
}
