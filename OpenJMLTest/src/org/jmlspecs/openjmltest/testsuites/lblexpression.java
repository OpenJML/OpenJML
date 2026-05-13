package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class lblexpression extends TCBase {

    @Test
    public void testlbl() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ invariant (\\lblneg A false);
                   //@ invariant (\\lblpos A k);
                   void m(double k) {}
                }
                """
        ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",29
        );
    }

    @Test
    public void testlbl2() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ invariant \\lblneg A false; // This is not strict JML, but it is difficult to preclude
                   //@ invariant 0==(\\lblpos A -k);
                   void m(double k) {}
                }
                """
                ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",32
        );
    }

    @Test
    public void testlbl3() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ invariant \\lblneg ghost false; // This is not strict JML, but it is difficult to preclude
                   //@ invariant 0==(\\lblpos pure -k);
                   void m(double k) {}
                }
                """
                ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",35
        );
    }

    @Test
    public void testlblany() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ invariant \\lbl ghost false; // This is not strict JML, but it is difficult to preclude
                   //@ invariant 0==(\\lbl pure -k);
                   void m(double k) {}
                }
                """
        );
    }

    @Test
    public void testlblany2() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ invariant \\lbl ghost false; // This is not strict JML, but it is difficult to preclude
                   //@ invariant (\\lbl pure -k);
                   void m(double k) {}
                }
                """
                ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",19
        );
    }

    @Test
    public void testlblany3() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ invariant \\lbl(ghost,false);
                   void m(double k) {}
                }
                """
        );
    }

}
