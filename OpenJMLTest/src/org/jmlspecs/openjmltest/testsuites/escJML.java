package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escJML extends EscBase {

    @Override
    public void setUp() throws Exception {
        testspecpath1 = "$A"+z+"$B"+ z + "$SY";
        super.setUp();
    }
    
    @Override
    public void tearDown() throws Exception {
        testspecpath1 = "$A"+z+"$B";
        super.tearDown();
    }
    
    // FIXME - the JML.lbl functions should report output just like the \lbl version do
    
    @Test
    public void testLBLObject() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(String i) {
                     //@ assert JML.lbl("AL",i) == null;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBL2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(Integer i) {
                     //@ assert JML.lbl("AL",i) == null;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLint() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(int i) {
                     //@ assert \\lbl(AL,i) != 0;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: Label AL has value 0", 22
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLshort() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(short i) {
                     //@ assert JML.lbl("AL",i) == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLboolean() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(boolean i) {
                     //@ assert JML.lbl("AL",i);
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLdouble() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(double i) {
                     //@ assert JML.lbl("AL",i) == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }

    @Test
    public void testLBLfloat() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m(float i) {
                     //@ assert JML.lbl("AL",i) == 0;
                  }
                }
                """
                ,"/tt/TestJava.java:4: verify: The prover cannot establish an assertion (Assert) in method m",10
                );
    }
}
