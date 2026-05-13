package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;


/** This class of JUnit tests checks that assertion violations for assertions
 * declared in other files are printed with source code from the other file.
 * @author David R. Cok
 *
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class esclocation extends EscBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--nullable-by-default"); // Because the tests were written this way
        addOptions("--check-feasibility=all");
    }

    @Test
    public void testLocationRequires() {
        addMockFile("$A/tt/TestJava.jml",
                """
                package tt; public class TestJava {
                  //@   requires false;
                  public void mm();
                }
                """
                );
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    mm();
                  }
                  public void mm() {}
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Precondition) in method m",7
                ,"/$A/tt/TestJava.jml:3: verify: Associated declaration",15
                ,"/$A/tt/TestJava.jml:2: verify: Precondition conjunct is false: false",18
                ,"/tt/TestJava.java:6: verify: Invariants+Preconditions appear to be contradictory in method tt.TestJava.mm()",15
                );
    }

    @Test
    public void testLocationEnsures() {
        addMockFile("$A/tt/TestJava.jml",
                """
                package tt; public class TestJava {
                  //@   ensures false;
                  public void m();
                }
                """
                );
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                  }
                }
                """
                ,"/tt/TestJava.java:3: verify: The prover cannot establish an assertion (Postcondition) in method m",15
                ,"/$A/tt/TestJava.jml:2: verify: Associated declaration",9
                );
    }

    @Test
    public void testLocationEnsures2() {
        addMockFile("$A/tt/TestJava.jml",
                """
                package tt; public class TestJava {
                  //@   ensures false;
                  public void m();
                }
                """
                );
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    return;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Postcondition) in method m",5
                ,"/$A/tt/TestJava.jml:2: verify: Associated declaration",9
                );
    }

    @Test
    public void testLocationSignals() {
        addMockFile("$A/tt/TestJava.jml",
                """
                package tt; public class TestJava {
                  //@   signals (Exception) false;
                  public void m();
                }
                """
                );
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m() {
                    throw new RuntimeException();
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (ExceptionalPostcondition) in method m",5
                ,"/$A/tt/TestJava.jml:2: verify: Associated declaration",9
                );
    }

    @Test
    public void testLocationInvariant() {
        addMockFile("$A/tt/TestJava.jml",
                """
                package tt; public class TestJava {
                  //@ public static invariant i>=0;
                  //@ assignable i;
                  public void m() ;
                }
                """
                );
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  public void m() {
                    i = -1; return;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (InvariantExit) in method m",13
                ,"/$A/tt/TestJava.jml:2: verify: Associated declaration",21
                );
    }

    @Test
    public void testLocationInitially() {
        addMockFile("$A/tt/TestJava.jml",
                """
                package tt; public class TestJava {
                  //@ public initially i>=0;
                  //@ assignable i;
                  public TestJava();
                }
                """
                );
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  public TestJava() {
                    i = -1; return;
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Initially) in method TestJava",13
                ,"/$A/tt/TestJava.jml:2: verify: Associated declaration",14
                );
    }


    @Test
    public void testLocationConstraint() {
        addMockFile("$A/tt/TestJava.jml",
                """
                package tt; public class TestJava {
                  //@ public constraint i>=\\old(i);
                  //@ assignable i;
                  public void m();
                }
                """
                );
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  static public int i;
                  public void m() {
                    i = -1; return;
                  }
                }
                """
                // FIXME - normalize column
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (Constraint) in method m",13
                ,"/$A/tt/TestJava.jml:2: verify: Associated declaration",14
                );
    }

    // TODO: represents, non_null field, non_null parameter, non_null method
    // TODO: non_null local, any local
    // TODO: signals_only, diverges, assignable
    // TODO: called preconditions
    // TODO: called undefined: div by 0, array index neg, array index too big
    // TODO: code undefined
}


