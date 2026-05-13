package org.jmlspecs.openjmltest.testsuites;

//import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class javaarray extends EscBase {

    @Test
    public void testJavaArray() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i, boolean[] a) {
                    //@ assume a.length > 10 && i > 0 && i < a.length;
                    boolean bb = a[i];
                    int len = a.length;
                    a[0] = false;
                    boolean[] b = a;
                    a[i] = true;
                    //@ assert !b[0] && b[i];
                  }
                }
                """
                );
    }

    @Test
    public void testJavaArray1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i, boolean[] a) {
                    //@ ghost \\bigint ii = i; set ii = ii*2;
                    //@ assume 0 <= ii && ii < a.length;
                    //@ ghost boolean b = a[ii];
                  }
                }
                """
                );
    }

    @Test
    public void testJavaArray1a() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i, boolean[] a) {
                    //@ ghost \\bigint ii = i; set ii = ii*2;
                    //@ assume 0 <= ii < 1000;
                    //@ ghost boolean b = a[ii];
                  }
                }
                """
                ,"/tt/TestJava.java:6: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method m1",28
                );
    }

    @Test
    public void testJavaArray2() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i, boolean[] a) {
                    //@ assume i < a.length;
                    boolean bb = a[i];
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyNegativeIndex) in method m1",19
                );
    }

    @Test
    public void testJavaArray3() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  public void m1(int i, boolean[] a) {
                    //@ assume i >= 0;
                    boolean bb = a[i];
                  }
                }
                """
                ,"/tt/TestJava.java:5: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method m1",19
                );
    }
}
