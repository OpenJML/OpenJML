package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class feasibility extends EscBase {
    
    String split = null;

    @Before @Override
    public void setUp() throws Exception {
        super.setUp();
        captureOutput = false;
    }
    
    protected void helpFeas(String feasoption, String program, Object... expectedResults) {
        if (split != null) addOptions("--split=" + split);
        addOptions("--check-feasibility=none");
        addOptions("--no-show-skipped");
        addOptions("--method=m,q,r");
        super.helpEsc("tt.TestJava", program);
        reset();
        if (split != null) addOptions("--split=" + split);
        addOptions("--no-show-skipped");
        addOptions("--method=m,q,r");
        addOptions("--check-feasibility=" + feasoption);
        super.helpEsc("tt.TestJava", program, expectedResults);
    }
    
    // FIXME - preconditions of spec; methodaxioms?

    @Test
    public void fassert() {
        helpFeas("assert",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ assume false;
                    //@ assert true;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point before explicit assert statement in method tt.TestJava.m()", 9
                );
    }

    @Test
    public void fassume() {
        helpFeas("assume",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    int i = 0;
                    //@ assume i != 0; // No feasibility checking if the assume is explicitly false
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point after explicit assume statement in method tt.TestJava.m()", 9
                );
    }

    @Test
    public void fcall() {
        helpFeas("call",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ assume false;
                    m();
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point before call in method tt.TestJava.m()", 6
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point after call in method tt.TestJava.m()", 6
                );
    }

    @Test
    public void fcall2() {
        helpFeas("call",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    t();
                  }
                  //@ public behavior
                  //@ ensures false;
                  //@ signals (Exception e) false;
                  public void t() { }
                }
                """
                ,"/tt/TestJava.java:4: verify: There is no feasible path to program point after call in method tt.TestJava.m()", 6
                );
    }

    @Test
    public void fcatch() {
        helpFeas("catch",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    try {}
                    catch (Exception e) {}
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at beginning of catch block in method tt.TestJava.m()", 5
                );
    }

    @Test
    public void fexit() {
        helpFeas("exit",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    if (i == 0) return;
                  }
                  //@ requires i != 0;
                  public void q(int i) {
                    if (i == 0) throw new RuntimeException();
                  }
                  //@ requires i != 0;
                  public void r(int i) {
                    if (i == 0) return;
                    //@ assume false;
                  }
                }
                """
                ,"/tt/TestJava.java:15: verify: There is no feasible path to program point at program exit in method tt.TestJava.r(int)", 3
                );
    }

    @Test
    public void ffinally() {
        helpFeas("finally",
                """
                package tt;
                public class TestJava {
                  //@ diverges true;
                  public void m() {
                    try { //@ assume false;
                    }
                    finally {}
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: There is no feasible path to program point at beginning of finally block in method tt.TestJava.m()", 13
                );
    }

    @Test
    public void fhalt() {
        helpFeas("halt",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ assume false;
                    //@ halt
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at halt statement in method tt.TestJava.m()", 9
                );
    }

    @Test
    public void fif() {
        helpFeas("if",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    if (i != 0) {
                      m(0);
                    }
                  }
                  //@ requires i == 0;
                  public void q(int i) {
                    if (i == 0) {
                    } else {
                      q(0);
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at then branch in method tt.TestJava.m(int)", 17
                ,"/tt/TestJava.java:12: verify: There is no feasible path to program point at else branch in method tt.TestJava.q(int)", 12
                );
    }

    @Test
    public void fblockbreak() {
        helpFeas("break",
                """
                package tt;
                public class TestJava {
                  //@ requires i > 0;
                  public void m(int i) {
                    x: {
                      if (i == 0) break x;
                      i = 1;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at break statement in method tt.TestJava.m(int)", 19
                );
    }

    @Test
    public void floopbreak() {
        helpFeas("break",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ loop_invariant 0 <= i <= 10;
                    for (int i = 0; i < 10; i++) {
                      if (i == -1) break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at break statement in method tt.TestJava.m()", 20
                );
    }

    @Test
    public void floopcontinue() {
        helpFeas("loopcontinue",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ loop_invariant 0 <= i <= 10;
                    for (int i = 0; i < 10; i++) {
                      if (i == -1) continue;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at loop continue statement in method tt.TestJava.m()", 20
                );
    }

    @Test
    public void floopcondition() {
        helpFeas("loopcondition",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ loop_invariant 0 <= i <= 10;
                    for (int i = 0; i > 10; i++) {
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at beginning of loop body in method tt.TestJava.m()", 34
                );
    }

    @Test
    public void floopbody() {
        helpFeas("loopbody",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    //@ loop_invariant 0 <= i <= 10;
                    for (int i = 0; i > 10; i++) {
                      int k = 0;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: There is no feasible path to program point at end of loop body in method tt.TestJava.m()", 5
                );
    }

    @Test
    public void floopexit() {
        helpFeas("loopexit",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    int i = 0;
                    //@ loop_invariant 0 <= i <= 10;
                    while (true) {
                      i = 1;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: There is no feasible path to program point at loop exit branch (false condition) in method tt.TestJava.m()", 5
                );
    }

    @Test
    public void fprecondition() {
        helpFeas("precondition",
                """
                package tt;
                public class TestJava {
                  //@ requires false;
                  public void m() {
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m()", 15
                );
    }

    @Test
    public void fprecondition2() {
        helpFeas("precondition",
                """
                package tt;
                public class TestJava {
                  public int i;
                  //@ public invariant i != 0;
                  //@ requires i == 0;
                  public void m() {
                    i = 1;
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m()", 15
                );
    }

    @Test
    public void fpreconditionOnly() {
        helpFeas("preconditionOnly",
                """
                package tt;
                public class TestJava {
                  //@ requires false;
                  public void m() {
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m()", 15
                );
    }

    @Test
    public void freachable() {
        helpFeas("reachable",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    if (i != 0) {
                      //@ reachable;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at reachable statement in method tt.TestJava.m(int)", 11
                );
    }

    @Test
    public void freturn() {
        helpFeas("return",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void q(int i) {
                    if (i != 0) {
                      return;
                    }
                  }
                  //@ requires i == 0;
                  public void m(int i) {
                    if (i == 0) {
                      return;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at return statement in method tt.TestJava.q(int)", 7
                ,"/tt/TestJava.java:14: verify: There is no feasible path to program point at implicit return in method tt.TestJava.m(int)",3
                );
    }

    @Test
    public void fswitch() {
        helpFeas("switch",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    switch (i) {
                      case 0: break;
                      default: break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: There is no feasible path to program point after case condition in method tt.TestJava.m(int)", 7
                );
    }

    @Test
    public void fswitch2() {
        helpFeas("switch",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 1;
                  public void m(int i) {
                    switch (i) {
                      case 0: break;
                      default: break;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point after case condition in method tt.TestJava.m(int)", 7
                );
    }

    @Test
    public void fspecA() {
        split = "A";
        helpFeas("spec",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    //@ refining ensures false;
                    {}
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at statement spec (after using summary) in method tt.TestJava.m(int)", 9
                );
    }

    @Test
    public void fspecB() {
        split = "B";
        helpFeas("spec",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    //@ refining ensures true;
                    {
                    //@ assume false;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: There is no feasible path to program point at end of refining statement block in method tt.TestJava.m(int)", 5
                );
    }

    @Test
    public void fthrow() {
        helpFeas("throw",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    if (i != 0) {
                      throw new RuntimeException();
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at throw statement in method tt.TestJava.m(int)", 7
                );
    }
}