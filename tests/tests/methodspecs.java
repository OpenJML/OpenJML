package tests;

public class methodspecs extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    /** Tests bad keyword */
    public void testBadKeyword() {
        helpTC(" class A { \n"
                +"//@ also\n"
                +"//@ r equires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:3: This is not a valid keyword in a method specification: r",5
                );
    }

//    /** Tests bad keyword */
//    public void testBadKeyword2() {
//        helpTC(" class A { \n"
//                +"//@ also\n"
//                +"//@ requires true;\n"
//                +"//@ s ignals_only Exception;\n"
//                +"int m() { return 0; }\n"
//                +"}"
//                ,"/TEST.java:4: This is not a valid keyword in a method specification: s",5
//                );
//    }

    // FIXME: We'd like to handle this and the above better - the r looks like a type and the
    // equires like a variable, so this is parsed as a declaration in JML.  It
    // does not check until later that there is no ghost or model.
//    /** Tests bad keyword */
//    public void testBadKeyword3() {
//        helpTC(" class A { \n"
//                +"//@ r equires true;\n"
//                +"//@ signals_only Exception;\n"
//                +"int m() { return 0; }\n"
//                +"}"
//                ,"/TEST.java:4: At most one signals_only clause is permitted in a specification case",5
//                );
//    }
    
    /** Tests multiple signals_only*/
    public void testMultipleSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only Exception;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:4: At most one signals_only clause is permitted in a specification case",5
                );
    }
    
    /** Tests one signals_only*/
    public void testOneSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                );
    }
    
    /** Tests bad signals_only*/
    public void testBadSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only Object;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:3: incompatible types\n  required: java.lang.Exception\n  found:    java.lang.Object",18
                );
    }
    
    /** Tests signals_only \\nothing*/ // OK
    public void testNothingSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only \\nothing;\n"
                +"int m() { return 0; }\n"
                +"}"
                );
    }
    
    /** Tests empty signals_only*/
    public void testEmptySignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only ;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:3: Use \\nothing to denote an empty list of exceptions in a signals_only clause",18
                );
    }
    
    /** Tests multiple signals_only in different cases*/
    public void testMultipleSignalsOnly2() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only Exception;\n"
                +"//@ {|\n"
                +"//@ ensures false;\n"
                +"//@ also\n"
                +"//@ signals_only Exception;\n"
                +"//@ |}\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:7: At most one signals_only clause is permitted in a specification case",5
                );
    }
        
    /** Tests multiple signals_only in different cases */
    public void testMultipleSignalsOnly3() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ {|\n"
                +"//@ signals_only Exception;\n"
                +"//@ also\n"
                +"//@ signals_only Exception;\n"
                +"//@ |}\n"
                +"int m() { return 0; }\n"
                +"}"
        );
    }
    
    /** Tests pure assignable*/
    public void testPureAssignable() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ {|\n"
                +"//@ signals_only Exception;\n"
                +"//@ also\n"
                +"//@ assignable \\everything;\n"
                +"//@ |}\n"
                +"//@ pure\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:6: Assignable clauses are not permitted in pure specification cases",5
        );
    }
    
    /** Tests exceptional ensures */
    public void testExceptionalEnsures() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ ensures false;\n"
                +"//@ also\n"
                +"//@ exceptional_behavior\n"
                +"//@ assignable \\everything;\n"
                +"int m() { return 0; }\n"
                +"}"
        );
    }
    
    /** Tests exceptional ensures */
    public void testExceptionalEnsures2() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ also\n"
                +"//@ exceptional_behavior\n"
                +"//@ ensures false;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:6: Ensures clauses are not permitted in exceptional specification cases",5
        );
    }
    
    /** Tests normal signals */
    public void testNormalSignals() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ signals (Exception e) false;\n"
                +"//@ also\n"
                +"//@ normal_behavior\n"
                +"//@ assignable \\everything;\n"
                +"int m() { return 0; }\n"
                +"}"
        );
    }
    
    /** Tests normal signals */
    public void testNormalSignals2() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ also\n"
                +"//@ normal_behavior\n"
                +"//@ signals (Exception e) false;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:6: Signals clauses are not permitted in normal specification cases",5
        );
    }
    
    
    /** Tests normal signals_only */
    public void testNormalSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ signals_only RuntimeException;\n"
                +"//@ also\n"
                +"//@ normal_behavior\n"
                +"//@ assignable \\everything;\n"
                +"int m() { return 0; }\n"
                +"}"
        );
    }
    
    /** Tests normal signals_only */
    public void testNormalSignalsOnly2() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ also\n"
                +"//@ normal_behavior\n"
                +"//@ signals_only RuntimeException;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:6: Signals_only clauses are not permitted in normal specification cases",5
        );
    }
    
    // TODO - should test normal and exceptional examples and implies_that as well
    
}
