package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

public class methodspecs extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    /** Tests bad keyword */
    @Test
    public void testBadKeyword() {
        helpTC(" class A { \n"
                +"//@ also\n"
                +"//@ r equires true;\n"
                +"//@ signals_only Exception;\n"
                +"int m() { return 0; }\n"
                +"}"
                ,"/TEST.java:3: The token r is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)",5
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
                ,"/TEST.java:4: The token s is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)",5
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
                ,"/TEST.java:2: The token r is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)",5
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
                ,"/TEST.java:2: The token true is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)",5
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
                ,"/TEST.java:2: The token class is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)",5
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
                ,"/TEST.java:2: <identifier> expected",16
                ,"/TEST.java:5: reached end of file while parsing",2
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
                ,"/TEST.java:4: At most one signals_only clause is permitted in a specification case",5
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
                ,"/TEST.java:3: incompatible types: java.lang.Object cannot be converted to java.lang.Exception",18
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
                ,"/TEST.java:3: Use \\nothing to denote an empty list of exceptions in a signals_only clause",18
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
                ,"/TEST.java:7: At most one signals_only clause is permitted in a specification case",5
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
                ,"/TEST.java:6: Pure methods may not assign to any fields: \\everything",16
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
                +"int mmm() {  return 0; }\n"
                +"}"
                ,"/TEST.java:6: Pure methods may not assign to any fields: k",16
                ,"/TEST.java:6: Pure methods may not assign to any fields: sk",19
                ,"/TEST.java:6: Pure methods may not assign to any fields: this.k",27
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
                ,"/TEST.java:6: Pure constructors may not assign to any fields other than non-static member fields: sk",16
                ,"/TEST.java:6: Pure constructors may not assign to any fields other than non-static member fields: A.sk",21
                ,"/TEST.java:6: Pure constructors may not assign to any fields other than non-static member fields: sbk",26
                ,"/TEST.java:6: Pure constructors may not assign to any fields other than non-static member fields: B.sbk",32
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
                ,"/TEST.java:6: Pure constructors may not assign to any fields other than non-static member fields: sbk",20
                ,"/TEST.java:6: Pure constructors may not assign to any fields other than non-static member fields: A.sbk",26
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
                ,"/TEST.java:6: Ensures clauses are not permitted in exceptional specification cases",5
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
                ,"/TEST.java:6: Signals clauses are not permitted in normal specification cases",5
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
                ,"/TEST.java:6: Signals_only clauses are not permitted in normal specification cases",5
        );
    }
    
    // TODO - should test normal and exceptional examples and implies_that as well
    // TODO - add tests for model programs
}
