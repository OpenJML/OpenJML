package org.jmlspecs.openjmltest.testsuites;

import java.util.Collection;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escinclause extends EscBase {

    @Test
    public void testInClause1() {
        helpEsc("tt.TestJava",
                """
                package tt;
                public class TestJava {
                  //@ model public int mx;
                  int x; //@ in mx;
                  int y;
                  //@ assignable mx;
                  public void m1bad(int i) {
                    y = 0 ;
                  }
                  //@ assignable mx;
                  public void m1good(int i) {
                    x = 0 ;
                  }
                }
                """
                ,"/tt/TestJava.java:8: verify: The prover cannot establish an assertion (Assignable) in method m1bad: y",7
                ,"/tt/TestJava.java:6: verify: Associated declaration",7
                );
    }
}
