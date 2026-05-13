package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

// Tests the rules about which visibility of identifiers can be used in specification constructs

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escvisibility1 extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        String z = java.io.File.pathSeparator;
        String testspecpath = "$A"+z+"$B";
        addOptions("-classpath",   testspecpath);
        addOptions("-sourcepath",   testspecpath);
        addOptions("-specspath",   testspecpath);
        addOptions("--normal");
    }

    @Test
    public void testInvariant() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  public int pb;
                  protected int pt;
                   int pa;
                  private int pv;
                  //@ invariant 0 == pb; // Line 7
                  //@ invariant 0 == pt;
                  //@ invariant 0 == pa;
                  //@ invariant 0 == pv;
                  //@ public invariant 0 == pb;
                  //@ public invariant 0 == pt;
                  //@ public invariant 0 == pa;
                  //@ public invariant 0 == pv;
                  //@ protected invariant 0 == pb; // Line 15
                  //@ protected invariant 0 == pt;
                  //@ protected invariant 0 == pa;
                  //@ protected invariant 0 == pv;
                  //@ private invariant 0 == pb;
                  //@ private invariant 0 == pt;
                  //@ private invariant 0 == pa;
                  //@ private invariant 0 == pv;
                }
                """
                ,"/tt/TestJava.java:7: error: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:8: error: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:10: error: An identifier with private visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: error: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:13: error: An identifier with package visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:15: error: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:17: error: An identifier with package visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:18: error: An identifier with private visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:19: error: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:21: error: An identifier with package visibility may not be used in a invariant clause with private visibility",30
                );
    }

    @Test
    public void testInvariantM() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  /*@ pure */public int pb(){return 0; };
                  /*@ pure */protected int pt(){return 0; };
                  /*@ pure */ int pa(){return 0; };
                  /*@ pure */private int pv(){return 0; };
                  //@ invariant 0 == pb(); // Line 7
                  //@ invariant 0 == pt();
                  //@ invariant 0 == pa();
                  //@ invariant 0 == pv();
                  //@ public invariant 0 == pb();
                  //@ public invariant 0 == pt();
                  //@ public invariant 0 == pa();
                  //@ public invariant 0 == pv();
                  //@ protected invariant 0 == pb(); // Line 15
                  //@ protected invariant 0 == pt();
                  //@ protected invariant 0 == pa();
                  //@ protected invariant 0 == pv();
                  //@ private invariant 0 == pb();
                  //@ private invariant 0 == pt();
                  //@ private invariant 0 == pa();
                  //@ private invariant 0 == pv();
                }
                """
                ,"/tt/TestJava.java:10: error: An identifier with private visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: error: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:13: error: An identifier with package visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:17: error: An identifier with package visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:18: error: An identifier with private visibility may not be used in a invariant clause with protected visibility",32
                );
    }

    @Test
    public void testInvariant2() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  /*@ spec_public */ protected int pt;
                  /*@ spec_public */  int pa;
                  /*@ spec_public */ private int pv;
                  //@ invariant 0 == pt; // Line 6
                  //@ invariant 0 == pa;
                  //@ invariant 0 == pv;
                  //@ public invariant 0 == pt;
                  //@ public invariant 0 == pa;
                  //@ public invariant 0 == pv;
                  //@ protected invariant 0 == pt;
                  //@ protected invariant 0 == pa;
                  //@ protected invariant 0 == pv;
                  //@ private invariant 0 == pt;
                  //@ private invariant 0 == pa;
                  //@ private invariant 0 == pv;
                  /*@ spec_protected */  int pat;
                  /*@ spec_protected */ private int pvt;
                  //@ invariant 0 == pat;
                  //@ invariant 0 == pvt;
                  //@ public invariant 0 == pat;
                  //@ public invariant 0 == pvt;
                  //@ protected invariant 0 == pat;
                  //@ protected invariant 0 == pvt;
                  //@ private invariant 0 == pat;
                  //@ private invariant 0 == pvt;
                }
                """
                ,"/tt/TestJava.java:6: error: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:7: error: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:8: error: An identifier with public visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:12: error: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:13: error: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:14: error: An identifier with public visibility may not be used in a invariant clause with protected visibility",32
                ,"/tt/TestJava.java:15: error: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:16: error: An identifier with public visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:17: error: An identifier with public visibility may not be used in a invariant clause with private visibility",30

                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:21: error: An identifier with protected visibility may not be used in a invariant clause with package visibility",22
                ,"/tt/TestJava.java:22: error: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:23: error: An identifier with protected visibility may not be used in a invariant clause with public visibility",29
                ,"/tt/TestJava.java:26: error: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                ,"/tt/TestJava.java:27: error: An identifier with protected visibility may not be used in a invariant clause with private visibility",30
                );
    }

    @Test
    public void testInClause() {
        expectedExit = 1;
        addOptions("-check");
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  //@ model public int pb;
                  //@ model protected int pt;
                  //@ model  int pa;
                  //@ model private int pv;
                  public int x1; //@ in pb; // Line 7
                  public int x2; //@ in pt;
                  public int x3; //@ in pa;
                  public int x4; //@ in pv;
                  protected int y1; //@ in pb;
                  protected int y2; //@ in pt;
                  protected int y3; //@ in pa;
                  protected int y4; //@ in pv;
                   int z1; //@ in pb;
                   int z2; //@ in pt;
                   int z3; //@ in pa;
                   int z4; //@ in pv;
                  private int t1; //@ in pb;
                  private int t2; //@ in pt;
                  private int t3; //@ in pa;
                  private int t4; //@ in pv;
                }
                """
                ,"/tt/TestJava.java:8: error: An identifier with protected visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:9: error: An identifier with package visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:10: error: An identifier with private visibility may not be used in a in clause with public visibility",25
                ,"/tt/TestJava.java:13: error: An identifier with package visibility may not be used in a in clause with protected visibility",28
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a in clause with protected visibility",28
                ,"/tt/TestJava.java:18: error: An identifier with private visibility may not be used in a in clause with package visibility",19
                );
    }

    @Test
    public void testRequires1() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  public boolean pb;
                  protected boolean pt;
                   boolean pa;
                  private boolean pv;
                  /*@ spec_public */ protected boolean ptb;
                  /*@ spec_public */  boolean pab;
                  /*@ spec_public */ private boolean pvb;
                  /*@ spec_protected */  boolean pat;
                  /*@ spec_protected */ private boolean pvt;
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also private normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also protected normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also public normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  public void m(){}
                }
                """
                ,"/tt/TestJava.java:12: error: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:12: error: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:12: error: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:12: error: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:12: error: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:18: error: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: error: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: error: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: error: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }

    @Test
    public void testRequires2() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  public boolean pb;
                  protected boolean pt;
                   boolean pa;
                  private boolean pv;
                  /*@ spec_public */ protected boolean ptb;
                  /*@ spec_public */  boolean pab;
                  /*@ spec_public */ private boolean pvb;
                  /*@ spec_protected */  boolean pat;
                  /*@ spec_protected */ private boolean pvt;
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also private normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also protected normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also public normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  protected void m(){}
                }
                """
                ,"/tt/TestJava.java:12: error: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:12: error: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:18: error: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: error: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: [jml-lint] There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: error: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: error: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }

    @Test
    public void testRequires3() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  public boolean pb;
                  protected boolean pt;
                   boolean pa;
                  private boolean pv;
                  /*@ spec_public */ protected boolean ptb;
                  /*@ spec_public */  boolean pab;
                  /*@ spec_public */ private boolean pvb;
                  /*@ spec_protected */  boolean pat;
                  /*@ spec_protected */ private boolean pvt;
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also private normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also protected normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also public normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                   void m(){}
                }
                """
                ,"/tt/TestJava.java:12: error: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:17: warning: [jml-lint] There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:18: error: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: error: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: [jml-lint] There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: error: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: error: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }

    @Test
    public void testRequires4() {
        expectedExit = 1;
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  public boolean pb;
                  protected boolean pt;
                   boolean pa;
                  private boolean pv;
                  /*@ spec_public */ protected boolean ptb;
                  /*@ spec_public */  boolean pab;
                  /*@ spec_public */ private boolean pvb;
                  /*@ spec_protected */  boolean pat;
                  /*@ spec_protected */ private boolean pvt;
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also private normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also protected normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  //@ also public normal_behavior
                  //@ requires pb && pt && pa && pv && ptb && pab && pvb && pat && pvt;
                  private void m(){}
                }
                """
                ,"/tt/TestJava.java:12: warning: [jml-lint] There is no point to a specification case having more visibility than its method",7
                ,"/tt/TestJava.java:14: error: An identifier with private visibility may not be used in a requires clause with package visibility",34
                ,"/tt/TestJava.java:17: warning: [jml-lint] There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:18: error: An identifier with package visibility may not be used in a requires clause with protected visibility",28
                ,"/tt/TestJava.java:18: error: An identifier with private visibility may not be used in a requires clause with protected visibility",34
                ,"/tt/TestJava.java:19: warning: [jml-lint] There is no point to a specification case having more visibility than its method",12
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",22
                ,"/tt/TestJava.java:20: error: An identifier with package visibility may not be used in a requires clause with public visibility",28
                ,"/tt/TestJava.java:20: error: An identifier with private visibility may not be used in a requires clause with public visibility",34
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",61
                ,"/tt/TestJava.java:20: error: An identifier with protected visibility may not be used in a requires clause with public visibility",68
                );
    }


    @Test
    public void testThisStarDefault() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                int i;
                public A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStarDefault1() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                int i;
                //@ requires true;
                public A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar0() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                int i;
                //@ pure
                public A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar1() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                 public int i;
                //@ pure
                public A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar2() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                 private int i;
                //@ pure
                public A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar3() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                 protected int i;
                //@ pure
                public A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar4() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                 public int i;
                //@ pure
                private A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar5() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                 private int i;
                //@ pure
                private A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar6() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                 protected int i;
                //@ pure
                private A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar7() {
        helpEsc("tt.A",
                """
                package tt; public class A {
                  int i;
                //@ pure
                private A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar8() {
        helpEsc("tx.B","package tx; public class B {\n protected int i;\n}",
                "tt.A",
                """
                package tt; public class A extends tx.B {
                \s
                //@ pure
                 A() { i = 0; }
                }
                """
                );
    }

    @Test
    public void testThisStar9() {
        helpEsc("tx.B","package tx; public class B {\n protected int i;\n}",
                "tt.A",
                """
                package tt; public class A extends tx.B {
                \s
                //@ pure
                protected A() { i = 0; }
                }
                """
                );
    }

    // Testing nested classes

    // FIXME - why the duplicate errors
    @Test
    public void testNestedPrivate() {
        expectedExit = 1;
        helpEsc("tt.B","package tt; public class B {\n static tt.A.P pp = A.Q.q; }\n", // No tt.A.P, No A.Q.q
                "tt.A",
                """
                package tt; public class A  {
                \s
                static private class P { static private int p; }
                static private class Q { static public int q = A.P.p ; }} // OK
                class AA { static int x = A.P.p + A.Q.q; } //No tt.A.P, tt.A.Q
                """
                ,"/tt/B.java:2: error: tt.A.P has private access in tt.A",13
                ,"/tt/B.java:2: error: tt.A.P has private access in tt.A",13
                ,"/tt/B.java:2: error: tt.A.Q has private access in tt.A",22
                ,"/tt/B.java:2: error: tt.A.Q has private access in tt.A",22
                ,"/tt/A.java:5: error: tt.A.P has private access in tt.A",28
                ,"/tt/A.java:5: error: tt.A.P has private access in tt.A",28
                ,"/tt/A.java:5: error: tt.A.Q has private access in tt.A",36
                ,"/tt/A.java:5: error: tt.A.Q has private access in tt.A",36
                );
    }

    @Test
    public void testNestedProtected() {
        expectedExit = 1;
        helpEsc("tt.B","package tx; public class B {\n static tt.A.P pp = tt.A.Q.q; }\n", // No tt.A.P, No A.Q.q
                "tt.A",
                """
                package tt; public class A  {
                \s
                static protected class P { static private int p; }
                static protected class Q { static public int q = A.P.p ; }} // OK
                class AA { static int x = A.P.p + A.Q.q; } // q OK - same package
                """
                ,"/tt/B.java:2: error: tt.A.P has protected access in tt.A",13
                ,"/tt/B.java:2: error: tt.A.P has protected access in tt.A",13
                ,"/tt/B.java:2: error: tt.A.Q has protected access in tt.A",25
                ,"/tt/B.java:2: error: tt.A.Q has protected access in tt.A",25
                ,"/tt/A.java:5: error: p has private access in tt.A.P",30
                );
    }
}
