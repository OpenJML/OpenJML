package tests;

public class sysclasses extends TCBase {

    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("MS_SHOULD_BE_FINAL")
    public static String testspecpath2 =  "$A"+z+"$B";

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        testspecpath = testspecpath2;
        super.setUp();
    }

//    /** Tests typechecking an invariant clause - OK*/
//    public void testInvariant() {
//        helpTC(" class A { int k; boolean b; Boolean bb; \n//@ invariant b;\n}");
//    }

    /** Tests using JMLDataGroup*/
    public void testDataGroup() {
        helpTCF("A.java"," class A { //@ public model JMLDataGroup streamState;\n}"
                ); // Gives a symbol not found error if the org.jmlspecs.lang package is not loaded
    }

}
