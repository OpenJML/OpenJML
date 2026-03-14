package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.ParseBase;
import org.junit.*;
import static org.junit.Assert.*;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class parseErrors extends ParseBase {
    
    @Override
    public void setUp() throws Exception {
        super.setUp();
        // These options are needed for stringTemplate(); they have to be set before postOptions() is called
        addOptions("--source","21");
        addOptions("--enable-preview","--enable-preview");
        addOptions("--check");
        postOptions();
    }

    @Test public void badTry() {
        checkParseErrors("class A { public A() { try{}} }"
                ,"/TEST.java:1: error: 'try' without 'catch', 'finally' or resource declarations", 24, 23, 23, 23 // FIXME - Better would be end=26

                );
    }

    @Test public void orphanCatch() {
        checkParseErrors("class A { public A() { catch(Exception e) {}} }"
                ,"/TEST.java:1: error: 'catch' without 'try'", 24, 23, 23, 23 // FIXME - Better would be end=28
                );
    }

    @Test public void orphanFinally() {
        checkParseErrors("class A { public A() { finally {}} }"
                ,"/TEST.java:1: error: 'finally' without 'try'", 24, 31, 23, 23 // FIXME - start is after end
                );
    }

    @Test public void orphanElse() {
        checkParseErrors("class A { public A() { else {}} }"
                ,"/TEST.java:1: error: 'else' without 'if'", 24, 28, 23, 23 // FIXME - start is after end
                );
    }

    @Test public void orphanCase() {
        checkParseErrors("class A { public A() { case 0; } }"
                ,"/TEST.java:1: error: orphaned case", 24, 23, 23, 23
                ,"/TEST.java:1: error: : or -> expected", 30, 29, 29, 29
                );
    }

    @Test public void orphanDefault() {
        checkParseErrors("class A { public A() { default: } }"
                ,"/TEST.java:1: error: orphaned default", 24, 23, 23, 23
                );
    }

    // FIXME - should complain about missing 'model'
    @Test public void modelClassWithNoMods() {
        checkParseErrors("class A { /*@ class B {} */ }"
                );
    }

    @Test public void modifierOnImport() {
        checkParseErrors("//@ @Pure import java.lang.System; \nclass A { }"
                ,"/TEST.java:1: error: No modifiers are allowed on an import statement", 5, 4, 4, 16
                ,"/TEST.java:1: error: An import statement in a JML comment must have a model modifier", 11, 10, 10, 16
                ,"/TEST.java:1: warning: misplaced model import", 11, 10, 10, 36 // FIXME - need a clearer error message
                );
    }

    @Test public void modifierOnImport2() {
        checkParseErrors("//@ @Model import java.lang.System; \nclass A { }"
                ,"/TEST.java:1: warning: misplaced model import", 12, 11, 11, 37  // FIXME - need a clearer error message
                );
    }

    @Test public void modifierOnImportOK() {
        checkParseErrors("//@ model import java.lang.System; \nclass A { }"
                );
    }

    // FIXME - not sure this helps coverage
    @Test public void prematureTypeListEnd() {
        checkParseErrors("class A { public A() { /*@ model T<A B> t; */} }"
                ,"/TEST.java:1: error: > or ',' expected", 38, 37, 37, 37
                ,"/TEST.java:1: error: ';' expected", 39, 38, 38, 38
                ,"/TEST.java:1: error: not a statement", 41, 40, 40, 40
                ,"/TEST.java:1: error: Expected a declaration or a JML construct inside the JML annotation here", 41, 40, 40, 40
                );
    }

    // FIXME - not sure this helps coverage
    @Test public void prematureTypeListEnd2() {
        checkParseErrors("class A { public A() { /*@ model T<A:B> t; */} }"
                ,"/TEST.java:1: error: > or ',' expected", 37, 36, 36, 36
                ,"/TEST.java:1: error: Error in parsed declaration, or misspelled keyword: //@ model T<A, (ERROR)> <error>", 37, 27, 36, 36
                ,"/TEST.java:1: error: not a statement", 39, 37, 38, 38
                ,"/TEST.java:1: error: Expected a declaration or a JML construct inside the JML annotation here", 38, 37, 37, 37
                );
    }

    @Test public void missingCase() {
        checkParseErrors("class A { public void m() { switch (x) { x = 0; } } }"
                ,"/TEST.java:1: error: case, default, or '}' expected", 42, 41, 41, 41
                ,"/TEST.java:1: error: case, default, or '}' expected", 44
                ,"/TEST.java:1: error: case, default, or '}' expected", 46
                ,"/TEST.java:1: error: case, default, or '}' expected", 47
                );
    }

    @Test public void badForInit() {
        checkParseErrors("class A { public void m() { for (int : x) {}  } }"
                ,"/TEST.java:1: error: bad initializer for for-loop", 34, 33, 33, 33
                );
    }

    @Test public void emptySpecCase() {
        addOptions("--lang=jml");
        checkParseErrors("class A { /*@ normal_behavior */ public void m() {  {}  } }"
                ,"/TEST.java:1: error: The specification case near here is empty, which is not permitted", 15, 14, 14, 14
                );
    }
    
    @Test public void badJmlType() {
        checkParseErrors("class A { public void m(/*@[ A @*/ A b) {  {}  } }"
                ,"/TEST.java:1: error: ']' expected", 31, 30, 30, 30
                );
    }

    @Test public void badJmlType2() {
        checkParseErrors("class A { public void m(/*@[ A ] x @*/ A b) {  {}  } }"
                ,"/TEST.java:1: error: Incorrectly formed or terminated JML construct near here", 34, 33, 33, 33
                );
    }

    @Test public void badJmlType3() {
        checkParseErrors("class A { public void m(/*@ /*@[ A ] x @*/ @*/ A b) {  {}  } }"
                ,"/TEST.java:1: error: Block comments may not be embedded inside JML block comments", 29, 28, 28, 28
                ,"/TEST.java:1: error: Incorrectly formed or terminated JML construct near here", 38, 37, 37, 37
                ,"/TEST.java:1: error: illegal start of type", 46, 45, 45, 45
                );
    }

    // FIXME - review these
    @Test public void modsOnImpliesThat() {
        checkParseErrors("class A { /*@ requires true; also public implies_that requires true; */ public void m() { } }"
                ,"/TEST.java:1: error: No modifiers are allowed prior to a lightweight specification case", 35, 34, 34, 34
                //,"/TEST.java:1: warning: No modifiers are allowed prior to a implies_that token", 35, 34, 34, 34
                );
    }

    @Test public void modsOnForExample() {
        checkParseErrors("class A { /*@ requires true; also public for_example requires true; */ public void m() { } }"
                ,"/TEST.java:1: error: No modifiers are allowed prior to a lightweight specification case", 35, 34, 34, 34
                //,"/TEST.java:1: warning: No modifiers are allowed prior to a for_example token", 35, 34, 34, 34
                );
    }

    @Ignore // FIXME - implement feasible behavior
    @Test public void modsOnFeasibleBehavior() {
        checkParseErrors("class A { /*@ requires true; also public feasible_behavior requires true; */ public void m() { } }"
                ,"/TEST.java:1: warning: No modifiers are allowed prior to a feasible_behavior token", 42, 41, 41, 57
                );
    }
    
    @Test public void stringTemplate() {
        checkParseErrors("class A { String s = STR.\"My \\{x} template\"; }"
                );
    }
    
    @Test public void badMods2() {
        checkParseErrors(
            """
            class A {
            /*@
            public normal_behavior
              requires true;
            public for_example public normal_example
              requires true;
            @*/
            public void m() {}
            }
            """
            ,"/TEST.java:5: error: No modifiers are allowed prior to a lightweight specification case", 1, 54, 54 ,54  // FIXME - why this error
            ,"/TEST.java:5: warning: No modifiers are allowed prior to a for_example token", 1, 54, 54, 60
            
            );
    }
    
    @Test public void badMods() {
        checkParseErrors(
            """
            class A {
            /*@
            public normal_behavior
              requires true;
            also public implies_that
              requires true;
            @*/
            public void m() {}
            }
            """
            ,"/TEST.java:5: error: No modifiers are allowed prior to a lightweight specification case", 6, 59, 59, 59 // FIXME - why these adiagnostics
            //,"/TEST.java:5: warning: No modifiers are allowed prior to a implies_that token", 8, 61, 61, 72
            
            );
    }
    
    @Test
    public void specGroup1() {
        checkParseErrors(
                """
                class A {
                  //@ public normal_behavior {| |}
                  public void m() {}
                }
                """
                );
    }
    
    @Test
    public void specGroup2() {
        checkParseErrors(
                """
                class A {
                  //@ public normal_behavior {|
                  public void m() {}
                }
                """
                ,"/TEST.java:3: error: Invalid clause or missing end of specification group token ( |} )", 3, 44, 44, 50
                ,"/TEST.java:2: error: Method specifications without a following method declaration", 14, 23, 23, 23  // FIXME - why this cascade of errors
                ,"/TEST.java:4: error: reached end of file while parsing", 2, 64, 64, 64
                );
    }
    
    // FIXME - does not trigger the desired error
    public void orphanMethodSpecs() {
        checkParseErrors(
            """
            class A {
            /*@
            public normal_behavior
              requires true;
            
            @*/
            //@ axiom true;
            public void m() {}
            }
            """
            ,"/TEST.java:5: error: No modifiers are allowed prior to a lightweight specification case", 6, 59, 59, 59 // FIXME - why these adiagnostics
            //,"/TEST.java:5: warning: No modifiers are allowed prior to a implies_that token", 8, 61, 61, 72
            
            );
    }
    
    // Test harness tests -- checking that test failures are properly reported
    
    /** This test allows the included harness tests to complete without an AssertionError, thereby
     *  allowing the normal execution route to be executed for coverage.
     */
    @Test
    public void harnessSkip() {
        skip = true;
        harness1();
        harness1a();
        harness2();
        harness3();
        harness4();
        harness5();
        harness6();
        harness7();
        harness8();
        harness9();
        harness10();
        harness11();
        harness12();
        harness13();
    }
    
    @Test
    public void harness1() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}");
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message",
                    "More errors observed (1) than expected. First extra: /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7",
                    a.getMessage());
        }
    }
    
    @Test
    public void harness1a() {
        var savedout = this.out;
        this.out = tempout;
        try {
            checkParseErrors("public c A {}");
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message",
                    "More errors observed (1) than expected. First extra: /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7",
                    a.getMessage());
        } finally {
            out = savedout;
        }
    }
    
    @Test
    public void harness2() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected"
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (col): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }
    
    @Test
    public void harness3() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 8
                ,"ZZZ", 8
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Fewer errors observed (1) than expected. First extra: ZZZ", 
                    a.getMessage());
        }
    }    

    @Test
    public void harness4() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"ZZZ", 8
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (text): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }

    @Test
    public void harness5() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 99
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (col): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }

    @Test
    public void harness6() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 8, 7, 7, 7
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (start): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }

    @Test
    public void harness7() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 8, 0, -10, -10
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (pos): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }

    @Test
    public void harness8() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 8, 0, 7, -10
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (end): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }

    @Test
    public void harness9() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 8, 0
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (pos): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }

    @Test
    public void harness10() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 8, 0, 7
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Expected 0 or 3 position values after the column value", 
                    a.getMessage());
        }
    }

    @Test
    public void harness11() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,"/TEST.java:1: error: class, interface, enum, or record expected", 8, 0, 7, 7, 7
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Fewer errors observed (1) than expected. First extra: 7", 
                    a.getMessage());
        }
    }

    @Test
    public void harness12() {
        noExtraPrinting = true;
        try {
            checkParseErrors("public c A {}"
                ,8, 0, 7, 7, 7
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (text): /TEST.java:1: error: class, interface, enum, or record expected line=1 col=8 start=0 pos=7 end=7", 
                    a.getMessage());
        }
    }
    
    @Test public void harness13() {
        noExtraPrinting = true;
        try {
            checkParseErrors("class A { public A() { case 0; } }"
                ,"/TEST.java:1: error: orphaned case"
                ,"/TEST.java:1: error: : or -> expected", 30, 29, 29, 29
                );
        } catch (AssertionError a) {
            assertEquals("Intentional failure issued wrong message", 
                    "Failed to match diagnostic 0 (text): /TEST.java:1: error: orphaned case line=1 col=24 start=23 pos=23 end=23", 
                    a.getMessage());
        }
    }
}
