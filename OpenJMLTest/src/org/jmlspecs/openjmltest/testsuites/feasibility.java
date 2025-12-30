package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class feasibility extends EscBase {

    @Before @Override
    public void setUp() throws Exception {
        super.setUp();
        captureOutput = false;
    }
    
    final String[] none = new String[] {};
 
    protected void helpFeas(String option, String program, Object... expectedResults) {
        helpFeas(none, option, program, expectedResults);
    }
    
    protected void helpFeas(String[] options, String option, String program, Object... expectedResults) {
        addOptions(options);
        addOptions("--check-feasibility=none");
        super.helpEsc("tt.TestJava", program);
        reset();
        addOptions(options);
        addOptions("--check-feasibility=" + option);
        super.helpEsc("tt.TestJava", program, expectedResults);
    }
    
    // FIXME - also break statement not in loop; preconditions of spec; methodaxioms?

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
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point after call in method tt.TestJava.m()", 6
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
                  public void m() {
                    //@ assume false;
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: There is no feasible path to program point at program exit in method tt.TestJava.m()", 15
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
                    try { System.exit(0); }
                    finally {}
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at beginning of finally block in method tt.TestJava.m()", 5
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
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at then branch in method tt.TestJava.m(int)", 5
                ,"/tt/TestJava.java:11: verify: There is no feasible path to program point at else branch in method tt.TestJava.q(int)", 5
                );
    }

    @Test
    public void floopbreak() {
        helpFeas("loopbreak",
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
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at break statement in method tt.TestJava.m()", 5
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
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at continue statement in method tt.TestJava.m()", 5
                );
    }

    @Test @Ignore // FIXME - not implemented
    public void floopcondition() {
        helpFeas("loopcondition",
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
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at then branch in method tt.TestJava.m()", 5
                );
    }

    @Test @Ignore // FIXME - not implemented
    public void floopexit() {
        helpFeas("loopexit",
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
                ,"/tt/TestJava.java:5: verify: There is no feasible path to program point at then branch in method tt.TestJava.m()", 5
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
    public void fprecondition2() { // FIXME
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
                ,"/tt/TestJava.java:4: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.m()", 15
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
                  public void m(int i) {
                    if (i != 0) {
                      return;
                    }
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: There is no feasible path to program point at return statement in method tt.TestJava.m(int)", 7
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
    public void fspecA() {  // FIXME
        helpFeas(new String[]{"--split=A","--no-show-skipped"}, "spec",
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
    public void fspecB() {  // FIXME
        helpFeas(new String[]{"--split=B","--no-show-skipped"}, "spec",
                """
                package tt;
                public class TestJava {
                  //@ requires i == 0;
                  public void m(int i) {
                    //@ refining requires false;
                    {}
                  }
                }
                """
                ,"/tt/TestJava.java:7: verify: There is no feasible path to program point after case condition in method tt.TestJava.m(int)", 7
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