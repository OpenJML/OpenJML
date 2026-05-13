package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.Options;

// Tests the rules about which specification cases are enforced by a method's implementation

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escvisibility extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        String z = java.io.File.pathSeparator;
        String testspecpath = "$A"+z+"$B";
        Options.instance(context).put("--class-path",   testspecpath);
        Options.instance(context).put("--source-path",   testspecpath);
        addOptions("--specspath",   testspecpath);
        addOptions("--normal");
    }

    // Invariant inherited from same package

    @Test
    public void testPrivate() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  private boolean b = false; public boolean bb = true;
                  //@ private invariant b;
                  //@ ensures bb;
                  public void change() { b = false; }
                }
                public class TestJava extends Parent {
                  public void m1() throws Exception {
                      change();
                  }
                }
                """
                );
    }

    @Test
    public void testPublic() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  public boolean b = true;
                  //@ public invariant b;
                }
                public class TestJava extends Parent {
                  public void m1() throws Exception {
                      b = false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",14
                );
    }

    @Test
    public void testProtected() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  protected boolean b = true;
                  //@ protected invariant b;
                }
                public class TestJava extends Parent {
                  public void m1() throws Exception {
                      b = false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",17
                );
    }

    @Test
    public void testPackage() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  boolean b = true;
                  //@ invariant b;
                }
                public class TestJava extends Parent {
                  public void m1() throws Exception {
                      b = false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",7
                );
    }

    // Invariant in same class

    @Test
    public void testPrivate2() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                }
                public class TestJava extends Parent {
                  private boolean b = true;
                  //@ private invariant b;
                  public void m1() {
                      b = false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: verify: Associated declaration",15
                );
    }

    @Test
    public void testPublic2() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  public boolean b = true;
                }
                public class TestJava extends Parent {
                  //@ public invariant b;
                  public void m1() {
                      b = false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: verify: Associated declaration",14
                );
    }

    @Test
    public void testProtected2() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  protected boolean b = true;
                }
                public class TestJava extends Parent {
                  //@ protected invariant b;
                  public void m1() {
                      b = false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: verify: Associated declaration",17
                );
    }

    @Test
    public void testPackage2() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  boolean b = true;
                }
                public class TestJava extends Parent {
                  //@ invariant b;
                  public void m1() {
                      b = false;
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: The prover cannot establish an assertion (InvariantExit) in method m1",15
                ,"/tt/TestJava.java:6: verify: Associated declaration",7
                );
    }

    // Inherited method spec in same package

    @Test
    public void testPrivate3() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@ private normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                );
    }

    @Test
    public void testPublic3() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@ public normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",9
                );
    }

    @Test
    public void testProtected3() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@ protected normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",9
                );
    }

    @Test
    public void testPackage3() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@ normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:4: verify: Associated declaration",9
                );
    }

    // Inherited lightweight method spec in same package

    @Test
    public void testPrivate3a() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@   ensures false;
                  private void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                );
    }

    @Test
    public void testPublic3a() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@  ensures false;
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",8
                );
    }

    @Test
    public void testProtected3a() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@  ensures false;
                  protected void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",8
                );
    }

    @Test
    public void testPackage3a() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  //@  ensures false;
                  void m1() {
                  }
                }
                public class TestJava extends Parent {
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:3: verify: Associated declaration",8
                );
    }

    // Inherited method spec in same class

    @Test
    public void testPrivate4() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  //@ also private normal_behavior ensures false;
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: verify: Associated declaration",36
                );
    }

    @Test
    public void testPublic4() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  //@ also public normal_behavior ensures false;
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: verify: Associated declaration",35
                );
    }

    @Test
    public void testProtected4() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  //@ also protected normal_behavior ensures false;
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:7: verify: Associated declaration",38
                );
    }

    @Test
    public void testPackage4() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class Parent {
                  public void m1() {
                  }
                }
                public class TestJava extends Parent {
                  //@ also normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:9: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tt/TestJava.java:8: verify: Associated declaration",9
                );
    }

    // Inherited method specs from a different package

    @Test
    public void testPrivate5() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@ private normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                """
                );
    }

    @Test
    public void testPublic5() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@ public normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:3: verify: Associated declaration",9
                );
    }

    @Test
    public void testProtected5() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@ protected normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:3: verify: Associated declaration",9
                );
    }

    @Test
    public void testPackage5() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@ normal_behavior
                  //@   ensures false;
                  public void m1() {
                  }
                }
                """
                );
    }


    // Inherited lightweight method specs from a different package

    @Test
    public void testPrivate6() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@  ensures false;
                  private void m1() {
                  }
                }
                """
                );
    }

    @Test
    public void testPublic6() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@  ensures false;
                  public void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:2: verify: Associated declaration",8
                );
    }

    @Test
    public void testProtected6() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@  ensures false;
                  protected void m1() {
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Postcondition) in method m1",15
                ,"/tx/Parent.java:2: verify: Associated declaration",8
                );
    }

    @Test
    public void testPackage6() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava extends tx.Parent {
                  public void m1() {
                  }
                }
                """,

                "tx.Parent",
                """
                package tx; public class Parent {
                  //@  ensures false;
                  void m1() {
                  }
                }
                """
                );
    }

    // Not-inherited method spec

    @Test
    public void testPublic7() {
        addOptions("--method", "tt.TestJava.m1");
        String s2 =
                """
                package tx; public class B {
                  //@  requires false;
                  static public void m1() {
                  }
                }
                """;

        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                     tx.B.m1();  }
                }
                """
                , "tx.B", s2


                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method m1",13
                ,"/tx/B.java:3: verify: Associated declaration",22
                ,"/tx/B.java:2: verify: Precondition conjunct is false: false",17
                );
    }

    @Test
    public void testPrivate8() {
    	expectedExit = 0;
        addOptions("--method", "tt.TestJava.m1");
        String s2 =
                """
                package tx; public class B {
                  //@ private normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                """;

        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                     tx.B.m1();  }
                }
                """
                ,"tx.B",s2
                ,"/tt/TestJava.java:4: warning: No visible specifications for this call site: tx.B.m1() called from tt.TestJava.m1()",13
                );
    }

    @Test
    public void testPublic8() {
        addOptions("--method", "tt.TestJava.m1");
        String s2 =
                """
                package tx; public class B {
                  //@ public normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                """;

        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                     tx.B.m1();  }
                }
                """
                ,"tx.B",s2

                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method m1",13
                ,"/tx/B.java:4: verify: Associated declaration",22
                ,"/tx/B.java:3: verify: Precondition conjunct is false: false",17
                );
    }


    @Test
    public void testProtected8() {
    	expectedExit = 0;
        addOptions("--method", "tt.TestJava.m1");
        String s2 =
                """
                package tx; public class B {
                  //@ protected normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                """;

        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                     tx.B.m1();  }
                }
                """
                ,"tx.B",s2
                ,"/tt/TestJava.java:4: warning: No visible specifications for this call site: tx.B.m1() called from tt.TestJava.m1()",13
                );
    }

    @Test
    public void testPackage8() {
    	expectedExit = 0;
        addOptions("--method", "tt.TestJava.m1");
        String s2 =
                """
                package tx; public class B {
                  //@ normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                """;

        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1() {
                     tx.B.m1();  }
                }
                """
                ,"tx.B", s2
                ,"/tt/TestJava.java:4: warning: No visible specifications for this call site: tx.B.m1() called from tt.TestJava.m1()",13
                );
    }

    @Test
    public void testPrivate9() {
    	expectedExit = 0;
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  //@ private normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                public class TestJava {
                  public void m1() {
                      B.m1();  }
                }
                """
                ,"/tt/TestJava.java:10: warning: No visible specifications for this call site: tt.B.m1() called from tt.TestJava.m1()",11
                );
    }

    @Test
    public void testPublic9() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  //@ public normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                public class TestJava {
                  public void m1() {
                      B.m1();  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Precondition) in method m1",11
                ,"/tt/TestJava.java:5: verify: Associated declaration",22
                ,"/tt/TestJava.java:4: verify: Precondition conjunct is false: false",17
                );
    }

    @Test
    public void testProtected9() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  //@ protected normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                public class TestJava {
                  public void m1() {
                      B.m1();  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Precondition) in method m1",11
                ,"/tt/TestJava.java:5: verify: Associated declaration",22
                ,"/tt/TestJava.java:4: verify: Precondition conjunct is false: false",17
                );
    }

    @Test
    public void testPackage9() {
        addOptions("--method", "tt.TestJava.m1");
        helpEsc("tt.TestJava",
                """
                package tt;
                class B {
                  //@ normal_behavior
                  //@  requires false;
                  static public void m1() {
                  }
                }
                public class TestJava {
                  public void m1() {
                      B.m1();  }
                }
                """
                ,"/tt/TestJava.java:10: verify: The prover cannot establish an assertion (Precondition) in method m1",11
                ,"/tt/TestJava.java:5: verify: Associated declaration",22
                ,"/tt/TestJava.java:4: verify: Precondition conjunct is false: false",17
                );
    }
}
