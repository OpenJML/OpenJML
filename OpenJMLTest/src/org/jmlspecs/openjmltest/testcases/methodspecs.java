package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class methodspecs extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    // TODO: It is hard to distinguish a misspelled keyword from the beginning of a declaration
    // but it would be nice to have a clear message about the misspelled keyword, here and in other BadKeyword tests
    /** Tests bad keyword */
    @Test
    public void testBadKeyword() {
        helpTC(" class A { \n"
                +"//@ also\n"
                +"//@ r equires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:3: error: ';' expected",14
                ,"/TEST.java:3: error: Method specs may not precede a variable declaration",7
                ,"/TEST.java:3: error: illegal start of type", 15
                ,"/TEST.java:3: error: <identifier> expected", 19
                );
    }

    /** Tests bad keyword */
    @Test
    public void testBadKeyword2() {
        helpTC(" class A { \n"
                +"\n"
                +"//@ requires true;\n"
                +"//@ s ignals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:4: error: ';' expected",18
                ,"/TEST.java:4: error: Method specs may not precede a variable declaration",7
                ,"/TEST.java:4: error: <identifier> expected",28
                );
    }

    /** Tests bad keyword */
    @Test
    public void testBadKeyword3() {
        helpTC(" class A { \n"
                +"//@ r equires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:2: error: ';' expected",14
                ,"/TEST.java:2: error: illegal start of type", 15
                ,"/TEST.java:2: error: <identifier> expected", 19
                );
    }
    
    /** Tests bad keyword */
    @Test
    public void testBadKeyword3a() {
        helpTC(" class A { \n"
                +"//@ true equires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:2: error: illegal start of type",5
                ,"/TEST.java:2: error: ';' expected",17
                ,"/TEST.java:2: error: illegal start of type", 18
                ,"/TEST.java:2: error: <identifier> expected",22
                );
    }
    
    /** Tests bad keyword */
    @Test
    public void testBadKeyword3b() {
        helpTC(" class A { \n"
                +"//@ class equires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:2: error: '{' expected",18
                );
    }
    
    /** Tests bad keyword */
    @Test
    public void testBadKeyword3c() {
        helpTC(" class A { \n"
                +"//@ model class ;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:2: error: <identifier> expected",16
                );
    }
    
    /** Tests multiple signals_only*/
    @Test
    public void testMultipleSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only Exception;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:4: error: At most one signals_only clause is permitted in a specification case",5
                );
    }
    
    /** Tests one signals_only*/
    @Test
    public void testOneSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                );
    }
    
    /** Tests bad signals_only*/
    @Test
    public void testBadSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only Object;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:3: error: incompatible types: java.lang.Object cannot be converted to java.lang.Throwable",18
                );
    }
    
    /** Tests signals_only \\nothing*/ // OK
    @Test
    public void testNothingSignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only \\nothing;\n"
                +"int m() { return 0; }\n"
                +"}"
                );
    }
    
    /** Tests empty signals_only*/
    @Test
    public void testEmptySignalsOnly() {
        helpTC(" class A { \n"
                +"//@ requires true;\n"
                +"//@ signals_only ;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:3: error: Use \\nothing to denote an empty list of exceptions in a signals_only clause",18
                );
    }
    
    /** Tests multiple signals_only in different cases*/
    @Test
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
                ,"/TEST.java:7: error: At most one signals_only clause is permitted in a specification case",5
                );
    }
        
    /** Tests multiple signals_only in different cases */
    @Test
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
    @Test
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
                ,"/TEST.java:6: error: Pure methods may not assign to any fields: \\everything in A.m()",16
        );
    }
    
    /** Tests pure assignable*/
    @Test
    public void testPureAssignable2() {
        helpTC(" class A { int k; static int sk; \n"
                +"//@ requires true;\n"
                +"//@ {|\n"
                +"//@ signals_only Exception;\n"
                +"//@ also\n"
                +"//@ assignable k, sk, this.k;\n"
                +"//@ |}\n"
                +"//@ pure\n"
                +"int m() {  return 0; }\n"
                +"}"
                ,"/TEST.java:6: error: Pure methods may not assign to any fields: k in A.m()",16
                ,"/TEST.java:6: error: Pure methods may not assign to any fields: sk in A.m()",19
                ,"/TEST.java:6: error: Pure methods may not assign to any fields: this.k in A.m()",27
        );
    }
    
    /** Tests pure assignable*/
    @Test
    public void testPureAssignable3() {
        helpTC(" class B { int bk; static int sbk; } class A extends B { int k; static int sk; \n"
                +"//@ requires true;\n"
                +"//@ {|\n"
                +"//@ signals_only Exception;\n"
                +"//@ also\n"
                +"//@ assignable sk, A.sk, sbk, B.sbk;\n"
                +"//@ |}\n"
                +"//@ pure\n"
                +"A() { }\n"
                +"}"
                ,"/TEST.java:6: error: Pure constructors may not assign to any fields other than non-static member fields: sk",16
                ,"/TEST.java:6: error: Pure constructors may not assign to any fields other than non-static member fields: A.sk",21
                ,"/TEST.java:6: error: Pure constructors may not assign to any fields other than non-static member fields: sbk",26
                ,"/TEST.java:6: error: Pure constructors may not assign to any fields other than non-static member fields: B.sbk",32
        );
    }
    
    /** Tests pure assignable*/
    @Test
    public void testPureAssignable4() {
        helpTC(" interface B { /*@ model instance int bk; model static int sbk; */} class A implements B { int k; static int sk; \n"
                +"//@ requires true;\n"
                +"//@ {|\n"
                +"//@ signals_only Exception;\n"
                +"//@ also\n"
                +"//@ assignable     sbk, A.sbk;\n"
                +"//@ |}\n"
                +"//@ pure\n"
                +"A() { }\n"
                +"}"
                ,"/TEST.java:6: error: Pure constructors may not assign to any fields other than non-static member fields: sbk",20
                ,"/TEST.java:6: error: Pure constructors may not assign to any fields other than non-static member fields: A.sbk",26
        );
    }
    
    /** Tests exceptional ensures */
    @Test
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
    @Test
    public void testExceptionalEnsures2() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ also\n"
                +"//@ exceptional_behavior\n"
                +"//@ ensures false;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:6: error: Ensures clauses are not permitted in exceptional specification cases",5
        );
    }
    
    /** Tests normal signals */
    @Test
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
    @Test
    public void testNormalSignals2() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ also\n"
                +"//@ normal_behavior\n"
                +"//@ signals (Exception e) false;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:6: error: Signals clauses are not permitted in normal specification cases",5
        );
    }
    
    
    /** Tests normal signals_only */
    @Test
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
    @Test
    public void testNormalSignalsOnly2() {
        helpTC(" class A { \n"
                +"//@ behavior\n"
                +"//@ requires true;\n"
                +"//@ also\n"
                +"//@ normal_behavior\n"
                +"//@ signals_only RuntimeException;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:6: error: Signals_only clauses are not permitted in normal specification cases",5
        );
    }
    
    // TODO - should test normal and exceptional examples and implies_that as well
    // TODO - add tests for model programs
}
