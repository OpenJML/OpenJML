package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.ParseBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class parseErrors extends ParseBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--check");
    }

    @Test public void badTry() {
        checkCompilationUnitErrors("class A { public A() { try{}} }"
                ,"/TEST.java:1: error: 'try' without 'catch', 'finally' or resource declarations", 24, 23, 23, 23 // FIXME - Better would be end=26

                );
    }

    @Test public void orphanCatch() {
        checkCompilationUnitErrors("class A { public A() { catch(Exception e) {}} }"
                ,"/TEST.java:1: error: 'catch' without 'try'", 24, 23, 23, 23 // FIXME - Beeeter would be end=28
                );
    }

    @Test public void orphanFinally() {
        checkCompilationUnitErrors("class A { public A() { finally {}} }"
                ,"/TEST.java:1: error: 'finally' without 'try'", 24, 31, 23, 23 // FIXME - start is after end
                );
    }

    @Test public void orphanElse() {
        checkCompilationUnitErrors("class A { public A() { else {}} }"
                ,"/TEST.java:1: error: 'else' without 'if'", 24, 28, 23, 23 // FIXME - start is after end
                );
    }

    @Test public void orphanCase() {
        checkCompilationUnitErrors("class A { public A() { case 0; } }"
                ,"/TEST.java:1: error: orphaned case", 24, 23, 23, 23
                ,"/TEST.java:1: error: : or -> expected", 30, 29, 29, 29
                );
    }

    @Test public void orphanDefault() {
        checkCompilationUnitErrors("class A { public A() { default: } }"
                ,"/TEST.java:1: error: orphaned default", 24, 23, 23, 23
                );
    }

    // FIXME - should complain about missing 'model'
    @Test public void modelClassWithNoMods() {
        checkCompilationUnitErrors("class A { /*@ class B {} */ }"
                );
    }

    @Ignore // crashes
    @Test public void modifierOnImport() {
        checkCompilationUnitErrors("//@ @Pure import java.lang.System; \nclass A { }"
                ,"/TEST.java:1: error: No modifiers are allowed on an import statement", 5, 4, 4, 7
                ,"/TEST.java:1: error: An import statement in a JML comment must have a model modifier", 10, 9, 9, 14
                );
    }

    @Ignore // crashes
    @Test public void modifierOnImport2() {
        checkCompilationUnitErrors("//@ @Model import java.lang.System; \nclass A { }"
                ,"/TEST.java:1: error: No modifiers are allowed on an import statement", 5, 4, 4, 7
                ,"/TEST.java:1: error: An import statement in a JML comment must have a model modifier", 10, 9, 9, 14
                );
    }

    @Ignore // FIXME - not sure this helps coverage
    @Test public void prematureTypeListEnd() {
        checkCompilationUnitErrors("class A { public A() { /*@ model T<A B> t; */} }"
                ,"/TEST.java:1: error: > or ',' expected", 38, 37, 37, 37
                ,"/TEST.java:1: error: ';' expected", 39, 38, 38, 38
                ,"/TEST.java:1: error: not a statement", 41, 40, 40, 40
                ,"/TEST.java:1: error: Expected a declaration or a JML construct inside the JML annotation here", 41, 40, 40, 40
                );


    }

    @Ignore // FIXME - not sure this helps coverage
    @Test public void prematureTypeListEnd2() {
        checkCompilationUnitErrors("class A { public A() { /*@ model T<A:B> t; */} }"
                ,"/TEST.java:1: error: > or ',' expected", 37, 36, 36, 36
                ,"/TEST.java:1: error: not a statement", 39, 37, 38, 38
                ,"/TEST.java:1: error: Expected a declaration or a JML construct inside the JML annotation here", 38, 37, 37, 37
                );

    }

    @Test public void missingCase() {
        checkCompilationUnitErrors("class A { public void m() { switch (x) { x = 0; } } }"
                ,"/TEST.java:1: error: case, default, or '}' expected", 42, 41, 41, 41
                ,"/TEST.java:1: error: case, default, or '}' expected", 44
                ,"/TEST.java:1: error: case, default, or '}' expected", 46
                ,"/TEST.java:1: error: case, default, or '}' expected", 47
                );
    }

    @Test public void badForInit() {
        checkCompilationUnitErrors("class A { public void m() { for (int : x) {}  } }"
                ,"/TEST.java:1: error: bad initializer for for-loop", 34, 33, 33, 33
                );
    }

    @Test public void emptySpecCase() {
        addOptions("--lang=jml");
        checkCompilationUnitErrors("class A { /*@ normal_behavior */ public void m() {  {}  } }"
                ,"/TEST.java:1: error: The specification case near here is empty, which is not permitted", 15, 14, 14, 14
                );
    }
    
    @Test public void badJmlType() {
        checkCompilationUnitErrors("class A { public void m(/*@[ A @*/ A b) {  {}  } }"
                ,"/TEST.java:1: error: ']' expected", 31, 30, 30, 30
                );
    }

    @Test public void badJmlType2() {
        checkCompilationUnitErrors("class A { public void m(/*@[ A ] x @*/ A b) {  {}  } }"
                ,"/TEST.java:1: error: Incorrectly formed or terminated JML construct near here", 34, 33, 33, 33
                );
    }

    @Ignore  // FIXME - throws exception
    @Test public void badJmlType3() {
        checkCompilationUnitErrors("class A { public void m(/*@ /*@[ A ] x @*/ @*/ A b) {  {}  } }"
                ,"/TEST.java:1: error: Incorrectly formed or terminated JML construct near here", 34, 33, 33, 33
                );
    }

    @Ignore // FIXME - review these
    @Test public void modsOnImpliesThat() {
        checkCompilationUnitErrors("class A { /*@ requires true; also public implies_that requires true; */ public void m() { } }"
                ,"/TEST.java:1: error: No modifiers are allowed prior to a lightweight specification case", 35, 34, 34, 34
                ,"/TEST.java:1: warning: No modifiers are allowed prior to a implies_that token", 35, 34, 34, 34
                );
    }

    @Ignore @Test public void modsOnForExample() {
        checkCompilationUnitErrors("class A { /*@ requires true; also public for_example requires true; */ public void m() { } }"
                ,"/TEST.java:1: error: No modifiers are allowed prior to a lightweight specification case", 35, 34, 34, 34
                ,"/TEST.java:1: warning: No modifiers are allowed prior to a for_example token", 35, 34, 34, 34
                );
    }

    @Ignore @Test public void modsOnFeasibleBehavior() {
        checkCompilationUnitErrors("class A { /*@ requires true; also public feasible_behavior requires true; */ public void m() { } }"
                ,"/TEST.java:1: warning: No modifiers are allowed prior to a feasible_behavior token", 42, 41, 41, 57
                );
    }
    
    @Ignore // FIXME - not reading the enable-preview option
    @Test public void stringTemplate() {
        addOptions("--source","21","--enable-preview");
        checkCompilationUnitErrors("class A { String s = STR.\"My \\{x} template\"; }"
                );
    }


}
