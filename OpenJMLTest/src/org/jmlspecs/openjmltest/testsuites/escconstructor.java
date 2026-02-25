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
                          "package tt; \n"
                        + "public class TestJava { \n"
                        + "  public int a;\n"
                        + "  static public int b;\n"
                        + "  //@ assignable \\nothing; \n"
                        + "  public TestJava() {\n"
                        + "    a = 10; \n"
                        + "    b = 10; \n" // Not allowed
                        + "  }\n" 
                        + "}\n"
                        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable) in method TestJava: b", 7
                        ,"/tt/TestJava.java:5: verify: Associated declaration", 7
                );
    }

    @Test
    public void testAssignableDefault() {
        main.addOptions("-defaults=constructor:pure");
        helpEsc("tt.TestJava",
                          "package tt; \n"
                        + "public class TestJava { \n"
                        + "   int a;\n"
                        + "  static  int b;\n"
                        + "   \n"
                        + "  public TestJava() {\n"
                        + "    a = 10; \n"
                        + "    b = 10; \n" // Not allowed
                        + "  }\n" 
                        + "}\n"
                        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable) in method TestJava: b", 7
                        ,"/tt/TestJava.java:6: verify: Associated declaration", 10
                );
    }

    @Test
    public void testAssignableDefault2() {
        helpEsc("tt.TestJava",
                          "package tt; \n"
                        + "public class TestJava { \n"
                        + "   int a;\n"
                        + "  static  int b;\n"
                        + "  //@ assignable \\nothing; \n"
                        + "  public TestJava() {\n"
                        + "    a = 10; \n"
                        + "    b = 10; \n" // Not allowed
                        + "  }\n" 
                        + "}\n"
                        ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable) in method TestJava: b", 7
                        ,"/tt/TestJava.java:5: verify: Associated declaration", 7
                );
    }

    @Test
    public void testCheckFields() {
        helpEsc("tt.TestJava",
                          "package tt; \n"
                        + "public class TestJava { \n"
                        + "   public int a;\n"
                        + "   public int b = 0;\n"
                        + "   public int c = 10;\n"
                        + "   public int cc; { cc = 15; }\n"
                        + "   //@ ghost public int d = 20;\n"
                        + "   //@ initially a == 0 && b == 0 && c == 10 && cc == 15 && d == 20;"
                        + "  //@ assignable \\nothing; \n"
                        + "  //@ ensures a == 0 && b == 0 && c == 10 && cc == 15; \n"
                        + "  public TestJava() {\n"
                        + "    //@ assert a == 0; \n"
                        + "    //@ assert b == 0; \n"
                        + "    //@ assert c == 10; \n"
                        + "  }\n" 
                        + "}\n"
                );
    }

    @Test
    public void testInvariants() {
        helpEsc("tt.TestJava",
                          "package tt; \n"
                        + "public class TestJava { \n"
                        + "   public int b = 10;\n"
                        + "   //@ public invariant b == 10;\n"
                        + "  //@ assignable \\nothing; \n"
                        + "  public TestJava(TestJava arg) {\n"
                        + "    //@ assert arg != this; \n"
                        + "    //@ assert b == 10; \n"
                        + "    //@ assert arg.b == 10; \n"
                        + "  }\n" 
                        + "}\n"
                );
    }
}
