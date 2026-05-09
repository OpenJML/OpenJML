package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

/** These tests check the use of spec_protected, spec_public and the Java visibility modifiers */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class access extends TCBase {

    @Test
    public void testSpecPublic() {
        helpTCText("A.java","public class A { /*@ spec_public */ static private boolean b; } class B { void m() { \n //@ assume A.b;   \n}}"
                );
    }

    @Test
    public void testSpecPublic1() {
        helpTCText("A.java","public class A { /*@ spec_public */ static private boolean b; } class B { void m() { \n boolean bb = A.b;   \n}}"
                ,"/A.java:2: error: b has private access in A",16
                );
    }

    @Test
    public void testSpecProtected() {
        helpTCText("A.java","public class A { /*@ spec_protected */ static private boolean b; } class B { void m() { \n //@ assume A.b;   \n}}"
                );
    }

    @Test
    public void testSpecProtected1() {
        helpTCText("A.java","public class A { /*@ spec_protected */ static private boolean b; } class B { void m() { \n boolean bb = A.b;   \n}}"
                ,"/A.java:2: error: b has private access in A",16
                );
    }

    @Test
    public void testSpecConflict() {
        helpTCText("A.java","public class A { /*@ spec_public spec_protected */ static private boolean b; } "
                ,"/A.java:1: error: A declaration may not be both spec_public and spec_protected",22
                ,"/A.java:1: error: Associated declaration: /A.java:1:",34
                );
    }

    @Test
    public void testSpecConflict1() {
        helpTCText("A.java","public class A { /*@ spec_public spec_public */ static private boolean b; } "
                ,"/A.java:1: error: modifier spec_public may not be repeated",34
                ,"/A.java:1: error: Associated declaration: /A.java:1:", 22
                );
    }

    @Test
    public void testSpecConflict2() {
        helpTCText("A.java","public class A { /*@ spec_protected spec_protected */ static private boolean b; } "
                ,"/A.java:1: error: modifier spec_protected may not be repeated",37
                ,"/A.java:1: error: Associated declaration: /A.java:1:", 22
                );
    }

    @Test
    public void testSpecConflict3() {
        expectedExit = 0;
        helpTCText("A.java","public class A { /*@ spec_public */ static public boolean b; } "
                ,"/A.java:1: warning: [jml-lint] There is no point to a declaration being both public and spec_public",22
                );
    }

    @Test
    public void testSpecConflict4() {
        helpTCText("A.java","public class A { /*@ spec_public */ static protected boolean b; } "
                ); // OK
    }

    @Test
    public void testSpecConflict5() {
        expectedExit = 0;
        helpTCText("A.java","public class A { /*@ spec_protected */ static protected boolean b; } "
                ,"/A.java:1: warning: [jml-lint] There is no point to a declaration being both protected and spec_protected",22
                );
    }

    @Test
    public void testSpecConflict6() {
        helpTCText("A.java","public class A { /*@ spec_protected */ static boolean b; } "
                ); // OK
    }

    @Test
    public void testSpecConflict7() {
        helpTCText("A.java","public class A { /*@ spec_public */ static boolean b; } "
                );  // OK
    }

    @Test
    public void testSpecConflictM() {
        helpTCText("A.java","public class A { /*@ spec_public spec_protected */ static private boolean m(){return true;} } "
                ,"/A.java:1: error: A declaration may not be both spec_public and spec_protected",22
                ,"/A.java:1: error: Associated declaration: /A.java:1:",34
                );
    }

    @Test
    public void testSpecConflictM1() {
        helpTCText("A.java","public class A { /*@ spec_public spec_public */ static private boolean m(){return true;} } "
                ,"/A.java:1: error: modifier spec_public may not be repeated",34
                ,"/A.java:1: error: Associated declaration: /A.java:1:", 22
                );
    }

    @Test
    public void testSpecConflictM2() {
        helpTCText("A.java","public class A { /*@ spec_protected spec_protected */ static private boolean m(){return true;} } "
                ,"/A.java:1: error: modifier spec_protected may not be repeated",37
                ,"/A.java:1: error: Associated declaration: /A.java:1:", 22
                );
    }

    @Test
    public void testSpecConflictM3() {
        expectedExit = 0;
        helpTCText("A.java","public class A { /*@ spec_public */ static public boolean m(){return true;} } "
                ,"/A.java:1: warning: [jml-lint] There is no point to a declaration being both public and spec_public",22
                );
    }

    @Test
    public void testSpecConflictM4() {
        helpTCText("A.java","public class A { /*@ spec_public */ static protected boolean m(){return true;} } "
                ); // OK
    }

    @Test
    public void testSpecConflictM5() {
        expectedExit = 0;
        helpTCText("A.java","public class A { /*@ spec_protected */ static protected boolean m(){return true;} } "
                ,"/A.java:1: warning: [jml-lint] There is no point to a declaration being both protected and spec_protected",22
                );
    }

    @Test
    public void testSpecConflictM6() {
        helpTCText("A.java","public class A { /*@ spec_protected */ static boolean m(){return true;} } "
                ); // OK
    }

    @Test
    public void testSpecConflictM7() {
        helpTCText("A.java","public class A { /*@ spec_public */ static boolean m(){return true;} } "
                );  // OK
    }

    @Test
    public void testSpecConflictC() {
        helpTCText("A.java","public class A { /*@ spec_public spec_protected */ static private class C{} } "
                ,"/A.java:1: error: A declaration may not be both spec_public and spec_protected",22
                ,"/A.java:1: error: Associated declaration: /A.java:1:",34
                );
    }

    @Test
    public void testSpecConflictC1() {
        helpTCText("A.java","public class A { /*@ spec_public spec_public */ static private class C{} } "
                ,"/A.java:1: error: modifier spec_public may not be repeated",34
                ,"/A.java:1: error: Associated declaration: /A.java:1:", 22
                );
    }

    @Test
    public void testSpecConflictC2() {
        helpTCText("A.java","public class A { /*@ spec_protected spec_protected */ static private class C{} } "
                ,"/A.java:1: error: modifier spec_protected may not be repeated",37
                ,"/A.java:1: error: Associated declaration: /A.java:1:", 22
                );
    }

    @Test
    public void testSpecConflictC3() {
        expectedExit = 0;
        helpTCText("A.java","public class A { /*@ spec_public */ static public class C{} } "
                ,"/A.java:1: warning: [jml-lint] There is no point to a declaration being both public and spec_public",22
                );
    }

    @Test
    public void testSpecConflictC4() {
        helpTCText("A.java","public class A { /*@ spec_public */ static protected class C{} } "
                ); // OK
    }

    @Test
    public void testSpecConflictC5() {
        expectedExit = 0;
        helpTCText("A.java","public class A { /*@ spec_protected */ static protected class C{} } "
                ,"/A.java:1: warning: [jml-lint] There is no point to a declaration being both protected and spec_protected",22
                );
    }

    @Test
    public void testSpecConflictC6() {
        helpTCText("A.java","public class A { /*@ spec_protected */ static class C{} } "
                ); // OK
    }

    @Test
    public void testSpecConflictC7() {
        helpTCText("A.java","public class A { /*@ spec_public */ static class C{} } "
                );  // OK
    }

}
