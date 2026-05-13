package org.jmlspecs.openjmltest.testsuites;

/** This tests that appropriate warnings are issued for deprecated syntax */

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

import com.sun.tools.javac.util.Options;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class deprecation extends TCBase {

    String dep_opt = "-Xlint:deprecation";

    @Override
    public void setUp() throws Exception {
        super.setUp();
        expectedExit = 0;
    }

    @Test
    public void testRepresentsB() {
        addOptions(dep_opt);
        helpTCText("A.java",
                """
                public class A {
                 //@ model int i;
                 //@ represents i <- 0;
                 }
                """
                ,"/A.java:3: warning: [deprecated] The left arrow is deprecated in represents clauses, use = instead",19
                );
    }

    @Test
    public void testRepresentsA() {
        helpTCText("A.java",
                """
                public class A {
                 //@ model int i;
                 //@ represents i <- 0;
                 }
                """
                );
    }

    @Test
    public void testParsePlusSilent() {
        helpTCText("A.java",
                """
                public class A {
                 //+@ model int i;
                 }
                """
                );
    }

    @Test
    public void testParsePlus() {
        addOptions(dep_opt);
        helpTCText("A.java",
                """
                public class A {
                 //+@ model int i;
                 }
                """
                ,"/A.java:2: warning: [deprecated] The //+@ and //-@ annotation styles are deprecated - use keys instead",4
                );
    }

    @Test
    public void testParseMinus() {
        addOptions(dep_opt);
        helpTCText("A.java",
                """
                public class A {
                 //-@ model int i;
                 }
                """
                ,"/A.java:2: warning: [deprecated] The //+@ and //-@ annotation styles are deprecated - use keys instead",4
                );
    }

    @Test
    public void testIndex() {
        helpTCText("A.java",
                """
                public class A {
                 void m(int[] a) { for (int i: a) {
                    //@ assert \\index == i;
                 }}}
                """
                );
    }

    @Test
    public void testIndex2() {
        addOptions(dep_opt);
        helpTCText("A.java",
                """
                public class A {
                 void m(int[] a) { for (int i: a) {
                    //@ assert \\index == i;
                 }}}
                """
                ,"/A.java:3: warning: [deprecated] The \\index construct is deprecated in favor of \\count",16
                );
    }


}
