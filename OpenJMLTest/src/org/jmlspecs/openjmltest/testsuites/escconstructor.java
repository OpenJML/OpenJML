package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.Options;

// FIXME - these were old tests - are they duplicates? should we use them?

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escconstructor extends EscBase {

    @org.junit.Before
    @Override
    public void setUp() throws Exception {
        // noCollectDiagnostics = true;
        super.setUp();
        // main.addOptions("-trace");
        // JmlEsc.escdebug = true;
        // org.jmlspecs.openjml.provers.YicesProver.showCommunication = 3;
        // print = true;
    }

    @Test
    public void testAssignable() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public int a;
                  static public int b;
                  //@ assignable \\nothing;
                  public TestJava() {
                    a = 10;
                    b = 10;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable) in method TestJava: b", 7
                ,"/tt/TestJava.java:5: verify: Associated declaration", 7
                );
    }

    @Test
    public void testAssignableDefault() {
        main.addOptions("-defaults=constructor:pure");
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                   int a;
                  static  int b;

                  public TestJava() {
                    a = 10;
                    b = 10;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable) in method TestJava: b", 7
                ,"/tt/TestJava.java:6: verify: Associated declaration", 10
                );
    }

    @Test
    public void testAssignableDefault2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                   int a;
                  static  int b;
                  //@ assignable \\nothing;
                  public TestJava() {
                    a = 10;
                    b = 10;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable) in method TestJava: b", 7
                ,"/tt/TestJava.java:5: verify: Associated declaration", 7
                );
    }

    @Test
    public void testCheckFields() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                   public int a;
                   public int b = 0;
                   public int c = 10;
                   public int cc; { cc = 15; }
                   //@ ghost public int d = 20;
                   //@ initially a == 0 && b == 0 && c == 10 && cc == 15 && d == 20;  //@ assignable \\nothing;
                  //@ ensures a == 0 && b == 0 && c == 10 && cc == 15;
                  public TestJava() {
                    //@ assert a == 0;
                    //@ assert b == 0;
                    //@ assert c == 10;
                  }
                }
                """
                );
    }

    @Test
    public void testInvariants() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                   public int b = 10;
                   //@ public invariant b == 10;
                  //@ assignable \\nothing;
                  public TestJava(TestJava arg) {
                    //@ assert arg != this;
                    //@ assert b == 10;
                    //@ assert arg.b == 10;
                  }
                }
                """
                );
    }
}
