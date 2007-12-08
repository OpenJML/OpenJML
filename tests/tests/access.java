package tests;

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

    // FIXME - more access tests needed
}
