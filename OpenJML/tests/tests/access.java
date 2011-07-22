package tests;

/** These tests check the use of spec_protected, spec_public and the Java visibility modifiers */
public class access extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    
    public void testSpecPublic() {
        helpTCF("A.java","public class A { /*@ spec_public */ static private boolean b; } class B { void m() { \n //@ assume A.b;   \n}}"
                );
    }

    public void testSpecPublic1() {
        helpTCF("A.java","public class A { /*@ spec_public */ static private boolean b; } class B { void m() { \n boolean bb = A.b;   \n}}"
                ,"/A.java:2: b has private access in A",16
                );
    }

    public void testSpecProtected() {
        helpTCF("A.java","public class A { /*@ spec_protected */ static private boolean b; } class B { void m() { \n //@ assume A.b;   \n}}"
                );
    }

    public void testSpecProtected1() {
        helpTCF("A.java","public class A { /*@ spec_protected */ static private boolean b; } class B { void m() { \n boolean bb = A.b;   \n}}"
                ,"/A.java:2: b has private access in A",16
                );
    }

    public void testSpecConflict() {
        helpTCF("A.java","public class A { /*@ spec_public spec_protected */ static private boolean b; } "
                ,"/A.java:1: A declaration may not be both spec_public and spec_protected",34
                );
    }

    public void testSpecConflict1() {
        helpTCF("A.java","public class A { /*@ spec_public spec_public */ static private boolean b; } "
                ,"/A.java:1: duplicate annotation",34
                );
    }

    public void testSpecConflict2() {
        helpTCF("A.java","public class A { /*@ spec_protected spec_protected */ static private boolean b; } "
                ,"/A.java:1: duplicate annotation",37
                );
    }

    public void testSpecConflict3() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ spec_public */ static public boolean b; } "
                ,"/A.java:1: warning: There is no point to a declaration being both public and spec_public",22
                );
    }

    public void testSpecConflict4() {
        helpTCF("A.java","public class A { /*@ spec_public */ static protected boolean b; } "
                ); // OK
    }

    public void testSpecConflict5() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ spec_protected */ static protected boolean b; } "
                ,"/A.java:1: warning: There is no point to a declaration being both protected and spec_protected",22
                );
    }

    public void testSpecConflict6() {
        helpTCF("A.java","public class A { /*@ spec_protected */ static boolean b; } "
                ); // OK
    }

    public void testSpecConflict7() {
        helpTCF("A.java","public class A { /*@ spec_public */ static boolean b; } "
                );  // OK
    }

    public void testSpecConflictM() {
        helpTCF("A.java","public class A { /*@ spec_public spec_protected */ static private boolean m(){return true;} } "
                ,"/A.java:1: A declaration may not be both spec_public and spec_protected",34
                );
    }

    public void testSpecConflictM1() {
        helpTCF("A.java","public class A { /*@ spec_public spec_public */ static private boolean m(){return true;} } "
                ,"/A.java:1: duplicate annotation",34
                );
    }

    public void testSpecConflictM2() {
        helpTCF("A.java","public class A { /*@ spec_protected spec_protected */ static private boolean m(){return true;} } "
                ,"/A.java:1: duplicate annotation",37
                );
    }

    public void testSpecConflictM3() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ spec_public */ static public boolean m(){return true;} } "
                ,"/A.java:1: warning: There is no point to a declaration being both public and spec_public",22
                );
    }

    public void testSpecConflictM4() {
        helpTCF("A.java","public class A { /*@ spec_public */ static protected boolean m(){return true;} } "
                ); // OK
    }

    public void testSpecConflictM5() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ spec_protected */ static protected boolean m(){return true;} } "
                ,"/A.java:1: warning: There is no point to a declaration being both protected and spec_protected",22
                );
    }

    public void testSpecConflictM6() {
        helpTCF("A.java","public class A { /*@ spec_protected */ static boolean m(){return true;} } "
                ); // OK
    }

    public void testSpecConflictM7() {
        helpTCF("A.java","public class A { /*@ spec_public */ static boolean m(){return true;} } "
                );  // OK
    }

    public void testSpecConflictC() {
        helpTCF("A.java","public class A { /*@ spec_public spec_protected */ static private class C{} } "
                ,"/A.java:1: A declaration may not be both spec_public and spec_protected",34
                );
    }

    public void testSpecConflictC1() {
        helpTCF("A.java","public class A { /*@ spec_public spec_public */ static private class C{} } "
                ,"/A.java:1: duplicate annotation",34
                );
    }

    public void testSpecConflictC2() {
        helpTCF("A.java","public class A { /*@ spec_protected spec_protected */ static private class C{} } "
                ,"/A.java:1: duplicate annotation",37
                );
    }

    public void testSpecConflictC3() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ spec_public */ static public class C{} } "
                ,"/A.java:1: warning: There is no point to a declaration being both public and spec_public",22
                );
    }

    public void testSpecConflictC4() {
        helpTCF("A.java","public class A { /*@ spec_public */ static protected class C{} } "
                ); // OK
    }

    public void testSpecConflictC5() {
        expectedExit = 0;
        helpTCF("A.java","public class A { /*@ spec_protected */ static protected class C{} } "
                ,"/A.java:1: warning: There is no point to a declaration being both protected and spec_protected",22
                );
    }

    public void testSpecConflictC6() {
        helpTCF("A.java","public class A { /*@ spec_protected */ static class C{} } "
                ); // OK
    }

    public void testSpecConflictC7() {
        helpTCF("A.java","public class A { /*@ spec_public */ static class C{} } "
                );  // OK
    }


    // TODO - more access tests needed - e.g. invalide combinations on methods and classes
}
