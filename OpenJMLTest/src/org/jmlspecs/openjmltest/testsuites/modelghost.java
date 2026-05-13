package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;

import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check various improper declarations of model and ghost
 * methods and fields.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class modelghost extends TCBase {

    @Test
    public void testClassSimple() {
        helpTCText("A.java",
                """
                public class A { /*@ model int m() { return B.n; } */ C mm() { return C.nn; }}
                /*@ model class B { public static int n; } */
                class C { public static C nn; }
                """
                );
    }

    @Test
    public void testClassSimple2() {
        helpTCText("A.java",
                """
                public class A { /*@ model int m() { return B.n; } */ B mm() { return B.nn; }}
                /*@ model class B { public static int n; } */
                """
                ,"/A.java:1: error: cannot find symbol\n  symbol:   class B\n  location: class A",55
                ,"/A.java:1: error: cannot find symbol\n  symbol:   variable B\n  location: class A",71
                );
    }

    @Test
    public void testClassSimple3() {
        helpTCText("A.java",
                """
                public class A { /*@ model B m() { return B.n; }  */ }
                /*@ model class B { public static B n; } */
                """
                );
    }

    @Test
    public void testMethod() {
        helpTCText("A.java",
                """
                public class A {
                  void m() {} // OK
                  //@ model int m1() { return 0; } // OK
                  /*@ model */ int m2() { return 9; } // BAD
                  void p() {}
                  //@ model int p1(); // OK
                  /*@ model */ int p2() {} // BAD
                  //@ int q(){} // BAD
                  static public class II { // Line 9
                  void m() {} // OK
                  //@ model int m1() { return 0; } // OK
                  /*@ model */ int m2() { return 9; } // BAD
                  void p() {} // BAD
                  //@ model int p1(); // OK
                  /*@ model */ int p2(){} // BAD
                  //@ int q(); // BAD
                  }
                  /*@ static model public class III { // Line 18
                  void m() {} // OK
                  model int m1() { return 0; } // NO NESTING
                  void p(); // OK - FIXME - resolve the rules about model methods and embedded model declarations
                  model int p1(); // NO NESTING
                  }*/
                }
                /*@ model class B { // Line 25
                  void m() {} // OK
                   model int m1() { return 0; } // NO NESTING
                  void p(); // OK -- FIXME - as above
                   model int p1(); // NO NESTING
                }
                */ class C { // Line 31
                  void m() {} // OK
                  //@ model int m1() { return 0; } // OK
                  /*@ model */ int m2() { return 9; } // BAD
                  void p() {}
                  //@ model int p1(); // OK
                  /*@ model */ int p2() {} // BAD
                  //@ int q(); // BAD
                }
                """
                ,"/A.java:4: error: A Java method declaration must not be marked model: A.m2()",7
                ,"/A.java:7: error: A Java method declaration must not be marked model: A.p2()",7
                ,"/A.java:8: error: A JML method declaration must be marked model: A.q()",11
                ,"/A.java:12: error: A Java method declaration must not be marked model: A.II.m2()",7
                ,"/A.java:15: error: A Java method declaration must not be marked model: A.II.p2()",7
                ,"/A.java:16: error: A JML method declaration must be marked model: A.II.q()",11
                ,"/A.java:20: error: A model type may not contain model declarations: A.III.m1()",13
                ,"/A.java:22: error: A model type may not contain model declarations: A.III.p1()",13
                ,"/A.java:27: error: A model type may not contain model declarations: B.m1()",14
                ,"/A.java:29: error: A model type may not contain model declarations: B.p1()",14
                ,"/A.java:34: error: A Java method declaration must not be marked model: C.m2()",7
                ,"/A.java:37: error: A Java method declaration must not be marked model: C.p2()",7
                ,"/A.java:38: error: A JML method declaration must be marked model: C.q()",11
                );
    }

    @Test
    public void testMethodBody() {
        helpTCText("A.java",
                """
                public class A {
                  void m() {} // OK
                  //@ model int m1() { return 0; } // OK
                  void p(); // BAD
                  //@ model int p1(); // OK
                }
                """
                ,"/A.java:4: error: missing method body, or declare abstract",8
                );
    }

    @Test
    public void testMethodBody2() {
        addMockFile("$A/A.jml","public class A { void m();\n void mm(){} /*@ model void mmm(); */ }");
        helpTCText("A.java",
                """
                public class A {
                  void m() {} // OK
                  void mm() {} // OK
                }
                """
                ,"/$A/A.jml:2: error: The specification of the method A.mm() must not have a body",11
                );
    }

    @Test
    public void testUseMethod() {
        helpTCText("A.java",
                """
                public class A {
                  /*@ pure */ boolean m() {} // OK
                  //@ model pure boolean m1() { return true; } // OK
                  //@ invariant m() && m1();
                  //@ requires m() && m1();
                  void p() {} ;
                  //@ requires m() && m1(); // BAD - VISIBILITY PROBLEMS
                  public void pp() {} ;
                }
                """
                ,"/A.java:7: error: An identifier with package visibility may not be used in a requires clause with public visibility",16
                ,"/A.java:7: error: An identifier with package visibility may not be used in a requires clause with public visibility",23
                );

    }

    @Test
    public void testUseMethod2() {
        helpTCText("A.java",
                """
                public class A {
                  //@ requires B.m() && B.m1();
                  static void p() {};
                  //@ requires B.m() && B.m1(); // BAD - VISIBILITY PROBLEMS
                  public static void pp() {} ;
                }
                class B {
                  static /*@ pure */ boolean m() {} // OK
                  //@ model pure static boolean m1() { return true; } // OK
                  //@ static invariant m() && m1();
                }
                """
                ,"/A.java:4: error: An identifier with package visibility may not be used in a requires clause with public visibility",17
                ,"/A.java:4: error: An identifier with package visibility may not be used in a requires clause with public visibility",26
                );

    }

    @Test
    public void testUseJML() {
        helpTCText("A.java",
                """
                import org.jmlspecs.lang.JML; public class A {
                  //@ requires JML.erasure(\\typeof(this)) == JML.erasure(\\type(A));
                  void p() {};
                }
                """
                );

    }

    @Test
    public void testClass() {
        helpTCText("A.java",
                """
                public class A {
                  //@ model static public class B{}
                  /*@ model */ static public class C{} // NOT MODEL
                  //@ static public class D{} // SHOULD BE MODEL
                  public class AA {
                    //@ model  public class B{}
                    /*@ model */  public class C{} // NOT MODEL
                    //@  public class D{} // SHOULD BE MODEL
                  }
                  /*@ model public class M { // Line 10
                    model  public class B{} // NO POINT
                     public class C{}
                  }*/
                }
                /*@ model */ class Y { // BAD
                }
                /*@ model class Q {
                  model  public class C{} // NO POINT
                   public class D{}
                }*/
                class Z {
                  //@ model  public class B{}
                  /*@ model */  public class C{} // BAD
                  //@  public class D{} // BAD
                }
                """
                // Java 21
                ,"/A.java:3: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.C",7
                ,"/A.java:4: error: A method or type declaration within a JML annotation must be model: A.D", 21
                ,"/A.java:7: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.AA.C",9
                ,"/A.java:8: error: A method or type declaration within a JML annotation must be model: A.AA.D", 17
                ,"/A.java:11: error: A model type may not contain model declarations: B in A.M",19
                ,"/A.java:15: error: A Java declaration (not within a JML annotation) may not be either ghost or model: Y",5
                ,"/A.java:18: error: A model type may not contain model declarations: C in Q",17
                ,"/A.java:23: error: A Java declaration (not within a JML annotation) may not be either ghost or model: Z.C",7
                ,"/A.java:24: error: A method or type declaration within a JML annotation must be model: Z.D", 15
        );

    }

    @Test
    public void testField() {
        helpTCText("A.java",
                """
                public class A {
                  int m; // OK
                  //@ model int m1; // OK
                  //@ ghost int m1a; // OK
                  /*@ model */ int m2; // BAD
                  /*@ ghost */ int m2a; // BAD
                  //@ int q; // BAD
                  static public class II { // Line 8
                  int m; // OK
                  //@ model int m1; // OK
                  //@ ghost int m1a; // OK
                  /*@ model */ int m2; // BAD
                  /*@ ghost */ int m2a; // BAD
                  //@ int q; // BAD
                  }
                  /*@ static model public class III { // Line 16
                    int m; // OK
                    model int m1; // NO NESTING
                    ghost int m1a; // NO NESTING
                \s
                  }*/
                }
                /*@ model class B { // Line 23
                  int m; // OK
                   model int m1; ghost int m2; // NO NESTING
                }
                */ class C {
                  int m; // OK
                  //@ model int m1; // OK
                  //@ ghost int m1a; // OK
                  /*@ model */ int m2; // BAD
                  /*@ ghost */ int m2a; // BAD
                  //@ int q; // BAD
                }
                """
                // Order changed for Java8
                ,"/A.java:5: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.m2",7
                ,"/A.java:6: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.m2a",7
                ,"/A.java:7: error: A declaration within a JML annotation must be either ghost or model: A.q",11
                ,"/A.java:12: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.II.m2",7
                ,"/A.java:13: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.II.m2a",7
                ,"/A.java:14: error: A declaration within a JML annotation must be either ghost or model: A.II.q",11
                ,"/A.java:18: error: A model type may not contain model declarations: m1 in A.III",15
                ,"/A.java:19: error: A model type may not contain ghost declarations: m1a in A.III",15
                ,"/A.java:25: error: A model type may not contain model declarations: m1 in B",14
                ,"/A.java:25: error: A model type may not contain ghost declarations: m2 in B",28
                ,"/A.java:31: error: A Java declaration (not within a JML annotation) may not be either ghost or model: C.m2",7
                ,"/A.java:32: error: A Java declaration (not within a JML annotation) may not be either ghost or model: C.m2a",7
                ,"/A.java:33: error: A declaration within a JML annotation must be either ghost or model: C.q",11
                );
    }

    @Test
    public void testInitializer() {
        addMockFile("$A/A.jml","public class A { { i = 2; } }");
        helpTCText("A.java","public class A { int i; { i = 1; } } "
                ,"/$A/A.jml:1: error: Initializer blocks are not allowed in specifications",18
        );
    }

    @Test
    public void testInitializer2() {
        addMockFile("$A/A.jml","public class A { } /*@ model  class B { int i;   } */ ");
        helpTCText("A.java","public class A { int i; { i = 1; } } "
        );
    }

    @Test
    public void testInitializer2a() {
        addMockFile("$A/A.jml","public class A { } /*@ model public class B { int i;   } */ ");
        helpTCText("A.java","public class A { int i; { i = 1; } } "
                ,"/$A/A.jml:1: error: class B is public, should be declared in a file named B.java",37
        );
    }

    @Test
    public void testInitializer3() {
        addMockFile("$A/A.jml","public class A { } \n/*@ model class B { int ijk;  \n{ ijk = 2; } } */ ");
        helpTCText("A.java","public class A { int i; { i = 1; } } "
        );
    }

    @Test
    public void testPackage() {
        addMockFile("$A/A.jml","package p; public class A { /*@ model public class B { int i;  { i = 2; } } */ }");
        helpTCText("A.java","package p; public class A { int i; { i = 1; } } "
        );
    }

    @Test
    public void testPackage2() {
        addMockFile("$A/A.jml","package pp; public class A { /*@ model public class B { int i;  { i = 2; } } */ }");
        helpTCText("A.java","package p; public class A { int i; { i = 1; } } "
        );
    }

    @Test public void testInterface() {
        helpTCText("TestJava.java",
                """
                package tt;
                public interface TestJava {
                  //@ public model instance int z;
                  //@ static model int z2;
                  public static int zz = 0;
                }
                """
                );
    }
}
