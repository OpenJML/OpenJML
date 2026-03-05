package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class lblexpression extends TCBase {

    @Test
    public void testlbl() {
        helpTCText("A.java",
                " class A { int k;  \n" +
                "   //@ invariant (\\lblneg A false);\n" +
                "   //@ invariant (\\lblpos A k);\n" +
                "   void m(double k) {}\n" +
                "}",
        "/A.java:3: error: incompatible types: int cannot be converted to boolean",29
        );
    }

    @Test
    public void testlbl2() {
        helpTCText("A.java",
                " class A { int k;  \n" +
                "   //@ invariant \\lblneg A false;\n" +  // This is not strict JML, but it is difficult to preclude
                "   //@ invariant 0==(\\lblpos A -k);\n" +
                "   void m(double k) {}\n" +
                "}"
                ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",32
        );
    }

    @Test
    public void testlbl3() {
        helpTCText("A.java",
                " class A { int k;  \n" +
                "   //@ invariant \\lblneg ghost false;\n" +  // This is not strict JML, but it is difficult to preclude
                "   //@ invariant 0==(\\lblpos pure -k);\n" +
                "   void m(double k) {}\n" +
                "}"
                ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",35
        );
    }

    @Test
    public void testlblany() {
        helpTCText("A.java",
                " class A { int k;  \n" +
                "   //@ invariant \\lbl ghost false;\n" +  // This is not strict JML, but it is difficult to preclude
                "   //@ invariant 0==(\\lbl pure -k);\n" +
                "   void m(double k) {}\n" +
                "}"
        );
    }

    @Test
    public void testlblany2() {
        helpTCText("A.java",
                " class A { int k;  \n" +
                "   //@ invariant \\lbl ghost false;\n" +  // This is not strict JML, but it is difficult to preclude
                "   //@ invariant (\\lbl pure -k);\n" +
                "   void m(double k) {}\n" +
                "}"
                ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",19
        );
    }

    @Test
    public void testlblany3() {
        helpTCText("A.java",
                " class A { int k;  \n" +
                "   //@ invariant \\lbl(ghost,false);\n" + 
                "   void m(double k) {}\n" +
                "}"
        );
    }

}
