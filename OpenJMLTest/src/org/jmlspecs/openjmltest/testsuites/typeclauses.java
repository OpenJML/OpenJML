package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class typeclauses extends TCBase {

    String eol = "\n";  // Just newline for Windows also
    
    /** Tests typechecking an invariant clause - OK*/
    @Test
    public void testInvariant() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ invariant b;\n}");
    }

    /** Tests typechecking an invariant clause - bad type*/
    @Test
    public void testInvariant2() {
        helpTCText("A.java"," class A { int k; boolean b; Boolean bb; \n//@ invariant k;\n}",
                "/A.java:2: error: incompatible types: int cannot be converted to boolean",15);
    }

    /** Tests typechecking an invariant clause - OK from Boolean*/
    @Test
    public void testInvariant3() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ invariant bb;\n}");
    }

    /** Tests static lookup for invariant */
    @Test
    public void testInvariant4() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ static invariant bb;\n}"
                ,"/TEST.java:2: error: non-static variable bb cannot be referenced from a static context",22
                );
    }

    /** Tests static lookup for invariant */
    @Test
    public void testInvariant5() {
        helpTCText(null, " class A { int k; boolean b; static Boolean bb; \n//@ static invariant bb;\n}");
    }

    /** Tests typechecking an constraint clause - OK*/
    @Test
    public void testConstraint() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ constraint b;\n}");
    }

    /** Tests typechecking an constraint clause - bad type*/
    @Test
    public void testConstraint2() {
        helpTCText("A.java"," class A { int k; boolean b; Boolean bb; \n//@ constraint k;\n}",
                "/A.java:2: error: incompatible types: int cannot be converted to boolean",16);
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint3() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ constraint bb;\n}");
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint4() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ constraint bb for \\everything;\n}");
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint5() {
        helpTCText(null, " class A { public A(){} void m(int i) {} Boolean bb; \n//@ constraint bb for A(), m, m(int), m(Object);\n}"
                ,"/TEST.java:2: error: Constructors are not allowed as methods in non-static constraint clauses",23
                ,"/TEST.java:2: error: incompatible types: java.lang.Object cannot be converted to int",39
                );
    }

    /** Tests typechecking an constraint clause - OK from Boolean*/
    @Test
    public void testConstraint5s() {
        helpTCText(null, " class A { void m(int i) {} static Boolean bb; \n//@ static constraint bb for A();\n}"
                );
    }

    /** Tests static lookup for constraint */
    @Test
    public void testConstraint6() {
        helpTCText(null, " class A { void m(int i) {} Boolean bb; \n//@ static constraint bb ;\n}"
                ,"/TEST.java:2: error: non-static variable bb cannot be referenced from a static context",23
                );
    }

    /** Tests static lookup for constraint */
    @Test
    public void testConstraint7() {
        helpTCText(null, " class A { void m(int i) {} static Boolean bb; \n//@ static constraint bb ;\n}");
    }

    // TODO - the testConstraintM... tests are not implemented
    @Test
    public void testConstraintM() {
        helpTCText(null, " class A { void m(int i) {} Boolean bb; \n//@ constraint bb for m;\n}");
    }

    @Test
    public void testConstraintM1() {
        helpTCText(null, " class A { void m(int i) {} Boolean bb; \n//@ constraint bb for mm;\n}"
                ,"/TEST.java:2: error: Could not match mm() in A", 23
                );
    }

    @Test
    public void testConstraintM2() {
        helpTCText(null, " class A { void m(int i) {} Boolean bb; \n//@ constraint bb for this.m;\n}"
                ,"/TEST.java:2: error: Could not match this.m() in A", 23  // FIXME - needs fixing
                );
    }

    @Test
    public void testConstraintM3() {
        helpTCText(null, " class A { void m(int i) {} Boolean bb; \n//@ constraint bb for A.m;\n}");
    }

    @Test
    public void testConstraintMA() {
        helpTCText(null, " class A { void m(int i) {} Boolean bb; \n//@ constraint bb for m(int);\n}");
    }

    @Test
    public void testConstraintMA1() {
        helpTCText(null, " class A { void m(int i) {} Boolean bb; \n//@ constraint bb for mm(int);\n}"
                ,"/TEST.java:2: error: cannot find symbol\n  symbol:   method mm(int)\n  location: class A",23
                );
    }

    @Test
    public void testConstraintMA2() {
        helpTCText(null, " class A { void m(int i[],Object o) {} void m(int i) {} Boolean bb; \n//@ constraint bb for this.m(int[],Object);\n}");
    }

    @Test
    public void testConstraintMA3() {
        helpTCText(null, " class A { void m(Integer i) {} A a; Boolean bb; \n//@ constraint bb for a.m(java.lang.Integer);\n}");
    }

    @Test
    public void testConstraintMA3s() {
        helpTCText(null, " class A { static void m(Integer i) {} Boolean bb; \n//@ constraint bb for A.m(java.lang.Integer);\n}");
    }

    @Test
    public void testConstraintMA3e() {
        helpTCText(null, " class A { void m(Integer i) {} A a; Boolean bb; \n//@ constraint bb for A.m(java.lang.Integer);\n}"
                ,"/TEST.java:2: error: non-static method m(java.lang.Integer) cannot be referenced from a static context",25
                );
    }

    @Test
    public void testConstraintMA3se() {
        helpTCText(null, " class A { static void m(Integer i) {} A a; Boolean bb; \n//@ constraint bb for a.m(java.lang.Integer);\n}");
    }

    @Test
    public void testConstraintMA4() {
        helpTCText(null, " class A extends B { Boolean bb; \n//@ constraint bb for m(java.lang.Integer);\n} class B { void m(Integer i) {} }"
                ,"/TEST.java:2: error: The method must be a direct member of the class containing the constraint clause",23
                );
    }

    @Test
    public void testConstraintMA5() {
        helpTCText(null, " class A { Boolean bb; \n//@ constraint bb for B.m(java.lang.Integer);\n} class B { void m(Integer i) {} }"
                ,"/TEST.java:2: error: non-static method m(java.lang.Integer) cannot be referenced from a static context",25  // FIXME - not sure this error is correct
                ,"/TEST.java:2: error: The method must be a direct member of the class containing the constraint clause",23
                );
    }

    /** Tests typechecking an axiom clause - OK*/
    @Test
    public void testAxiom() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ axiom b;\n}");
    }

    /** Tests typechecking an axiom clause - bad type*/
    @Test
    public void testAxiom2() {
        helpTCText("A.java"," class A { int k; boolean b; Boolean bb; \n//@ axiom k;\n}",
                "/A.java:2: error: incompatible types: int cannot be converted to boolean",11);
    }

    /** Tests typechecking an axiom clause - OK from Boolean*/
    @Test
    public void testAxiom3() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ axiom bb;\n}");
    }

    /** Tests typechecking an initially clause - OK*/
    @Test
    public void testInitially() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ initially b;\n}");
    }

    /** Tests typechecking an initially clause - bad type*/
    @Test
    public void testInitially2() {
        helpTCText("A.java"," class A { int k; boolean b; Boolean bb; \n//@ initially k;\n}",
                "/A.java:2: error: incompatible types: int cannot be converted to boolean",15);
    }

    /** Tests typechecking an initially clause - OK from Boolean*/
    @Test
    public void testInitially3() {
        helpTCText(null, " class A { int k; boolean b; Boolean bb; \n//@ initially bb;\n}");
    }

    /** Tests typechecking an initially clause - OK from Boolean*/
    @Test
    public void testInitially4() {
        helpTCText("A.java"," class A { int k; boolean b; Boolean bb; \n//@ initially x;\n}",
                "/A.java:2: error: cannot find symbol\n  symbol:   variable x\n  location: class A",15);
    }

    /** Tests initially may be static */
    @Test
    public void testInitially5() {
        helpTCText("A.java"," class A { int k; boolean b; Boolean bb; \n//@ static initially b;\n}"
                ,"/A.java:2: error: non-static variable b cannot be referenced from a static context",22
                );
    }

    @Test
    public void testRepresents() {
        helpTCText("A.java","public class A {\n //@ model int i; represents i = true;\n}"
                ,"/A.java:2: error: incompatible types: boolean cannot be converted to int",34
                );
    }

    @Test
    public void testRepresents1() {
        helpTCText("A.java","public class A {\n //@ model int i; represents i <- true;\n}"
                ,"/A.java:2: error: incompatible types: boolean cannot be converted to int",35
                );
    }

    @Test
    public void testRepresents2() {
        helpTCText("A.java","public class A {\n //@ model int i; represents i \\such_that 0;\n}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",43
                );
    }

    @Test
    public void testRepresents3() {
        helpTCText("A.java","public class A {\n //@ model int i; represents j = 0;\n}"
                ,"/A.java:2: error: cannot find symbol\n  symbol:   variable j\n  location: class A",30
                );
    }
    
    @Test
    public void testRepresents4() {
        helpTCText("A.java","public class A {\n //@ model int i; represents i !0;\n}"
                ,"/A.java:2: error: A represents clause must have a = or \\such_that after the identifier",32
                );
    }
    
    @Test
    public void testRepresents5() {
        helpTCText("A.java","public class A {\n //@ model int j; represents j = ;\n}"
                ,"/A.java:2: error: illegal start of expression",34
                ,"/A.java:2: warning: Inserting missing semicolon at the end of a represents statement", 35
                );
    }
    
    @Test
    public void testRepresents6() {
    	expectedExit = 0;
        helpTCText("A.java","public class A {\n //@ model int i; represents i = 0\n}"
                ,"/A.java:2: warning: Inserting missing semicolon at the end of a represents statement",35
                );
    }
    
    @Test
    public void testRepresents7() {
        helpTCText("A.java","public class A {\n //@ model int i; represents x = 0\n}"
                ,"/A.java:2: warning: Inserting missing semicolon at the end of a represents statement",35
                ,"/A.java:2: error: cannot find symbol"+eol+"  symbol:   variable x"+eol+"  location: class A",30
                );
    }
    
    @Test
    public void testRepresents8() {
        helpTCText("A.java","public class A {\n //@ model Object x; represents x.* = 0;\n}"
                ,"/A.java:2: error: Field accesses are not permitted in a represents clause",34
                );
    }
    
    @Test 
    public void testRepresents9() {
    	expectedExit = 0;
    	addOptions("-lang=jml"); // Part of test
        helpTCText("A.java","public class A {\n //@ model int[] x; represents x[*] = 0;\n}"
                ,"/A.java:2: warning: Strict JML does not allow the [*] syntax",34
                );
    }
    
    @Test
    public void testRepresents9a() {
    	addOptions("-lang=openjml"); // Part of test
        helpTCText("A.java","public class A {\n //@ represents x[*] = 0;\n}"
                ,"/A.java:2: error: cannot find symbol"+eol+"  symbol:   variable x"+eol+"  location: class A",17
                ,"/A.java:2: error: Represents target with wild-card index must be an array: x[*]",17
                );
    }
    
    @Test
    public void testRepresents9b() {
        helpTCText("A.java","public class A {\n //@ model int x; represents x[*] = 0;\n}"
                ,"/A.java:2: error: Represents target with wild-card index must be an array: x[*]",30
                );
    }
    
    @Test
    public void testRepresents10() {
        helpTCText("A.java","public class A {\n //@ model int i; represents x[3] = 0;\n}"
                ,"/A.java:2: error: cannot find symbol"+eol+"  symbol:   variable x"+eol+"  location: class A",30
                ,"/A.java:2: error: Array elements are not permitted in a represents clause",30
               );
    }
    
    @Test
    public void testRepresents11() {
        helpTCText("A.java","public class A {\n //@ model int i; static represents i = 0;\n}"
                ,"/A.java:2: error: A represents clause and its associated model field must both be static or both not be static",26
                );
    }
    
    @Test
    public void testRepresents12() {
        helpTCText("A.java","public class A {\n //@ model static int i; represents i = 0;\n}"
                ,"/A.java:2: error: A represents clause and its associated model field must both be static or both not be static",26
                );
    }
    
    @Test
    public void testRepresents13() {
        helpTCText("A.java","public class A {\n //@ ghost int i; represents i = 0;\n}"
                ,"/A.java:2: error: The target of a represents clause must be a model field: A.i",30
                ,"/A.java:2: Note: Associated declaration: /A.java:2:",16
                );
    }
    
    @Test
    public void testRepresents14() {
        helpTCText("A.java","public class A {\n int i; //@ represents i = 0;\n}"
                ,"/A.java:2: error: The target of a represents clause must be a model field: A.i",24
                ,"/A.java:2: Note: Associated declaration: /A.java:2:",6
                );
    }
    
    @Test
    public void testRepresents13a() {
        addMockFile("$A/A.jml","public class A {\n //@ ghost int i; represents i = 0;\n}");
        helpTCText("A.java","public class A {\n }"
                ,"/$A/A.jml:2: error: The target of a represents clause must be a model field: A.i",30
                ,"/$A/A.jml:2: Note: Associated declaration: /$A/A.jml:2:",16
                );
    }
    
    @Test
    public void testRepresents14a() {
        addMockFile("$A/A.jml","public class A {\n //@ represents i = 0;\n}");
        helpTCText("A.java","public class A {\n int i; \n}"
                ,"/$A/A.jml:2: error: The target of a represents clause must be a model field: A.i",17
                ,"/A.java:2: Note: Associated declaration: /$A/A.jml:2:",6
                );
    }

    /** Check that the target of a static represents clause is in the same class */
    @Test
    public void testRepresents15() {
        helpTCText("A.java","public class A extends B {\n //@ static represents i = 0;\n} class B { //@ static model int i; \n}"
                ,"/A.java:2: error: A represents clause must be declared in the same class as the static model field it represents: B.i",24
                ,"/A.java:3: Note: Associated declaration: /A.java:2:",34
                );
    }
    
    /** Check that the rhs of a static represents clause contains only static fields */
    @Test
    public void testRepresents16() {
        helpTCText("A.java","public class A {\n static int k; /*@ in i; */ int j; //@ model static int i; static represents i = k;\n}"
                );
    }
    
    /** Check that the rhs of a static represents clause contains only static fields */
    @Test
    public void testRepresents16a() {
        helpTCText("A.java","public class A {\n static int k; int j; /*@ in i; */ //@ model static int i; static represents i = j;\n}"
                ,"/A.java:2: error: non-static variable j cannot be referenced from a static context",82
                ,"/A.java:2: error: A non-static variable may not be in a static datagroup",30
                );
    }
    
    /** Check that warning that <- is deprecated */
    @Test
    public void testRepresents17() {
        expectedExit = 0;
        setDeprecation();
        helpTCText("A.java","public class A {\n static int j; /*@ in i; */ //@  model static int i; static represents i <- j;\n}"
                ,"/A.java:2: warning: [deprecated] The left arrow is deprecated in represents clauses, use = instead",74
                );
    }
    

    @Test
    public void testMisc() {
        helpTCText("A.java","public class A {\n //@ ensures ((boolean)\\result);\n int m() { return 0; }}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",24
        );
    }
    
    @Test
    public void testMisc2() {
        helpTCText("A.java","public class A {\n //@ ensures ((short)\\result) == 0;\n int m() { return 0; }}"
        );
    }
    
    @Test
    public void testMisc3() {
        helpTCText("A.java","public class A {\n //@ public normal_behavior ensures true; public model boolean m(); \n }"
        );
    }
    
    @Test
    public void testOld() {
        helpTCText("A.java","public class A {\n //@ old boolean k=true, m = false; requires k; \n public void m() {}}"
                );
    }
    
    @Test
    public void testOld2() {
        helpTCText("A.java","public class A {\n //@ old boolean k, m = false; requires i == 0; \n public void m() {}}"
                ,"/A.java:2: error: A old method clause variable must have an initializer",18
                ,"/A.java:2: error: cannot find symbol\n  symbol:   variable i\n  location: class A",41
        );
    }
    
    @Test
    public void testOld3() {
        helpTCText("A.java","public class A {\n //@ old int i=true; old boolean m=0; requires i == 0; \n public void m() {}}"
                ,"/A.java:2: error: incompatible types: boolean cannot be converted to int",16
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",36
                );
    }
    
    @Test
    public void testOld4() {
        helpTCText("A.java","public class A {\n //@ old int k=0; requires i<k; \n public void m(int i) {}}"
                );        // OK
    }
    
    @Test
    public void testOld5() {
        helpTCText("A.java","public class A {\n //@ old boolean j=false; old boolean  k=true; requires i+j<k; \n public void m(boolean i) {}}"
                ,"/A.java:2: error: bad operand types for binary operator '+'\n  first type:  boolean\n  second type: boolean",58
                );        
    }
    
    @Test
    public void testOld6() {
        helpTCText("A.java","public class A { int i,j,k; \n //@ old boolean j=true; old boolean k=true; requires i+j<k; \n public void m(boolean i) {}}"
                ,"/A.java:2: error: bad operand types for binary operator '+'\n  first type:  boolean\n  second type: boolean",56
                );        
    }
    
    @Test
    public void testOld7() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCText("A.java","public class A { \n //@ old int i=0; old int k=0   ; requires i<k; \n public void m(int i) {}}"
                ,"/A.java:2: error: variable i is already defined in method m(int)",14
                );        
    }
    
    @Test
    public void testOld8() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCText("A.java","public class A { \n //@ old int k=0; old int k=0   ; requires i<k; \n public void m(int i) {}}"
                ,"/A.java:2: error: variable k is already defined in method m(int)",27
                );        
    }
    
    @Test
    public void testOld9() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCText("A.java","public class A { \n //@ old int j=1; old int k=0   ; requires i<k; \n//@{| old int m=0; ensures k<m; also ensures k<m; |} \n public void m(int i) {}}"
                ,"/A.java:3: error: cannot find symbol\n  symbol:   variable m\n  location: class A",48
                );        
    }
    
    @Test
    public void testOld10() { // FIXME - this is not the clearest error message - it should refer to the specifications
        helpTCText("A.java","public class A { \n //@ old int j=1; old int k=0   ; requires i<k; \n//@{| old int k=0; ensures k<m; also ensures i==0; |} \n public void m(int i) {}}"
                ,"/A.java:3: error: variable k is already defined in method m(int)",15
                ,"/A.java:3: error: cannot find symbol\n  symbol:   variable m\n  location: class A",30
                );        
    }

    @Test
    public void testSignals() { //OK
        helpTCText("A.java","public class A {\n//@ signals(Exception e) true; \n void m(){}}");
    }

    @Test
    public void testSignals1() {//OK
        helpTCText("A.java","public class A {\n//@ signals(Exception) true; \n void m(){}}");
    }

    @Test
    public void testSignals2() { //Bad type
        helpTCText("A.java","public class A {\n//@ signals(Object e) true; \n void m(){}}",
                "/A.java:2: error: incompatible types: java.lang.Object cannot be converted to java.lang.Exception",13);
    }

    @Test
    public void testSignals3() { //Bad syntax
        helpTCText("A.java","public class A {\n//@ signals true; \n void m(){}}",
                "/A.java:2: error: Expected a left parenthesis after a signals keyword",13);
    }

    @Test
    public void testSignals4() { //OK
        helpTCText("A.java","public class A {\n//@ signals(RuntimeException ) ; \n void m(){}}"
                );
    }

    @Test
    public void testSignals5() { //Bad type
        helpTCText("A.java","public class A {\n//@ signals(java.io.IOException e) 2; \n void m(){}}",
                "/A.java:2: error: incompatible types: int cannot be converted to boolean",36);
    }

    @Test
    public void testSignals6() { //Bad type
        helpTCText("A.java","public class A {\n//@ signals(int e) true; \n void m(){}}",
                "/A.java:2: error: incompatible types: int cannot be converted to java.lang.Exception",13);
    }

    @Test
    public void testSignals7() { //OK - scoping
        helpTCText("A.java","public class A {\n//@ signals(java.io.IOException e) e==null; \n void m(){}}");
    }

    @Test
    public void testSignalsOnly() { //OK
        helpTCText("A.java","public class A {\n//@ signals_only \\nothing;\nvoid m() {}}");
    }

    @Test
    public void testSignalsOnly1() { //OK
        helpTCText("A.java","public class A {\n//@ signals_only RuntimeException;\nvoid m() {}}");
    }

    @Test
    public void testSignalsOnly2() { //OK
        helpTCText("A.java","public class A {\n//@ signals_only RuntimeException,Exception;\nvoid m() {}}");
    }

    @Test
    public void testSignalsOnly3() {
        helpTCText("A.java","public class A {\n//@ signals_only ;\nvoid m() {}}",
                "/A.java:2: error: Use \\nothing to denote an empty list of exceptions in a signals_only clause",18);
    }

    @Test
    public void testSignalsOnly4() {
        helpTCText("A.java","public class A {\n//@ signals_only RuntimeException java.lang.Exception;\nvoid m() {}}",
                "/A.java:2: error: Missing comma or otherwise ill-formed type name",35);
    }

    @Test
    public void testSignalsOnly5() {
        helpTCText("A.java","public class A {\n//@ signals_only RuntimeException,;\nvoid m() {}}"
                ,"/A.java:2: error: illegal start of type",35
                ,"/A.java:2: error: Invalid expression or missing semicolon here", 36
                );
    }

    @Test
    public void testSignalsOnly6() {
        helpTCText("A.java","public class A {\n//@ signals_only RuntimeException,,RuntimeException;\nvoid m() {}}",
                "/A.java:2: error: illegal start of type",35);
    }

    @Test
    public void testSignalsOnly7() {
        helpTCText("A.java","public class A {\n//@ signals_only RuntimeException\nvoid m() {}}",
                "/A.java:2: error: Invalid expression or missing semicolon here",34);
    }

    @Test
    public void testSignalsOnly8() {
        helpTCText("A.java","public class A {\n//@ signals_only RuntimeException[];\nvoid m() {}}",
                "/A.java:2: error: incompatible types: java.lang.RuntimeException[] cannot be converted to java.lang.Throwable",34);
    }

    @Test
    public void testSignalsOnly9() {
        helpTCText("A.java","public class A {\n//@ signals_only int;\nvoid m() {}}",
                "/A.java:2: error: incompatible types: int cannot be converted to java.lang.Throwable",18);
    }

    @Test
    public void testSignalsOnly10() {
        helpTCText("A.java","public class A {\n//@ signals_only Q;\nvoid m() {}}",
                "/A.java:2: error: cannot find symbol\n  symbol:   class Q\n  location: class A",18);
    }
    
    @Test
    public void testIn() {
        helpTCText("A.java","public class A {\n //@ model \\datagroup k; \n int n; //@ in k; \n}"
                );
    }
    
    @Test
    public void testIn2() {
        helpTCText("A.java","public class A extends B{\n protected int k; \n int n; //@ in k, this.k, super.kk; \n} class B { //@ model int kk; \n}"
                ,"/A.java:3: error: Datagroups in \"in\" and \"maps\" clauses must be model variables",16
                ,"/A.java:3: error: Datagroups in \"in\" and \"maps\" clauses must be model variables",19
                );
    }
    
    @Test
    public void testIn2a() {
        helpTCText("A.java","public class A extends B{\n /*@ spec_public */ protected int k; \n int n; //@ in k, this.k, super.kk; \n} class B { //@ model int kk; \n}"
                );
    }
    
    @Test
    public void testIn3() {
        helpTCText("A.java","public class A {\n /*@ spec_public */ protected int k; \n int n; //@ in m; \n}"
                ,"/A.java:3: error: cannot find symbol\n  symbol:   variable m\n  location: class A",16
                );
    }
    
    @Test
    public void testIn4() {
        helpTCText("A.java","public class A {\n //@ model static int m; \n int n; //@ in m; \n}"
                ,"/A.java:3: error: A non-static variable may not be in a static datagroup",16
                );
    }
    
    @Test
    public void testMaps() {
        helpTCText("A.java","public class A {\n //@ model \\datagroup k; \n A next; //@ maps next.next \\into k; \n}"
        );
    }
    
    @Test
    public void testMaps2() {
        helpTCText("A.java","public class A {\n //@ model \\datagroup k; \n A[] next; //@ maps next[*].next \\into k; \n}"
        );
    }
    
    @Test
    public void testMaps2b() {
        helpTCText("A.java","public class A {\n //@ model \\datagroup k; \n A[] next; //@ maps next[*] \\into k; \n}"
        );
    }
    
    @Test
    public void testMaps3() {
        helpTCText("A.java","public class A {\n //@ model \\datagroup k; \n A[] next; //@ maps next[2 .. 3].next \\into k,k; \n}"
        );
    }
    
    @Test
    public void testMaps4() {
        helpTCText("A.java","public class A {\n //@ model \\datagroup k; \n A[] next; //@ maps next[2].next \\into this.k; \n}"
        );
    }
    
    // TODO - should have some tests checking recovery in maps clauses
    
    @Test
    public void testInitializer() {
        helpTCText("A.java","public class A {\n //@ initializer static_initializer \n}"
        );
    }

    @Test
    public void testInitializer1() {
        helpTCText("A.java","public class A {\n//@ initializer static_initializer initializer static_initializer\n}"
                ,"/A.java:2: error: Only one initializer specification and one static_initializer specification are allowed",36
                ,"/A.java:2: error: Only one initializer specification and one static_initializer specification are allowed",48
        );
    }

    /** Tests that specs get associated with the initializer */
    @Test
    public void testInitializer2() {
        helpTCText("A.java","public class A {\n public int i; public static int j; //@ ensures i==0; initializer ensures j == 0; static_initializer \n}"
        );
    }

    /** Tests that variable references in a static initializer must be static */
    @Test
    public void testInitializer3() {
        helpTCText("A.java","public class A {\n public int i; public static int j; //@ ensures i == 0; static_initializer \n}"
                ,"/A.java:2: error: non-static variable i cannot be referenced from a static context",49
        );
    }

    @Test
    public void testInitializer4() {
        addMockFile("$A/A.jml","public class A {\n public int i; public static int j; //@ ensures i == 0; static_initializer \n}");
        helpTCText("A.java","public class A {\n public int i; public static int j;  \n}"
                ,"/$A/A.jml:2: error: non-static variable i cannot be referenced from a static context",49
        );
    }

    @Test
    public void testInitializer5() {
        addMockFile("$A/A.jml","public class A {\n  static {} \n}");
        helpTCText("A.java","public class A {\n int i; static int j;  \n}"
                ,"/$A/A.jml:2: error: Initializer blocks are not allowed in specifications",10
        );
    }

    @Test
    public void testInitializer6() {
        helpTCText("A.java","public class A {\n {} static {} \n}"
        );
    }

    @Test
    public void testInitializer7() {
        helpTCText("A.java","public class A {\n //@ {} static {} {} static {}\n}"
        );
    }

    /** Tests that specs are parsed with the Java initializer */
    @Test
    public void testInitializer8() {
        helpTCText("A.java","public class A {\n public int i; static public int j; //@ ensures i==0; \n {} //@ ensures i==0; \n static {} \n}"
                ,"/A.java:3: error: non-static variable i cannot be referenced from a static context",17
        );
    }

    @Test
    public void testInitializer9() {
        helpTCText("A.java","public class A {int i; static int j; \n \n static { i = 0; } \n}"
                ,"/A.java:3: error: non-static variable i cannot be referenced from a static context",11
        );
    }

    @Test
    public void testInitializer10() {
        helpTCText("A.java","public class A {public int i; public static int j; \n //@ ensures i==0; \n static { i = 0; } \n}"
                ,"/A.java:3: error: non-static variable i cannot be referenced from a static context",11
                ,"/A.java:2: error: non-static variable i cannot be referenced from a static context",14
        );
    }

    // OK
    @Test
    public void testMonitorsFor() {
        helpTCText("A.java","public class A {A a; Object i,j,k; //@ monitors_for i = j,a.k,Object.class; \n }"
        );
    }
    
    @Test
    public void testMonitorsFor1() {
        helpTCText("A.java","public class A {Object i,j,k; int m; //@ monitors_for i = 5; \n }"
                ,"/A.java:1: error: The expression in a monitors_for clause must have reference type",59
        );
    }
    
    @Test
    public void testMonitorsFor2() {
        helpTCText("A.java","public class A {Object i,j,k; int m; //@ monitors_for i <- m; \n }"
                ,"/A.java:1: error: The expression in a monitors_for clause must have reference type",60
        );
    }
    
    // OK - static does not matter
    @Test
    public void testMonitorsFor3() {
        helpTCText("A.java","public class A {Object i,j; static Object k;  //@ monitors_for k = i,A.k; \n }"
        );
    }
    
    @Test
    public void testMonitorsFor4() {
        helpTCText("A.java","public class A {Object i,j; static Object k;  //@ monitors_for k = Object; \n }"
                ,"/A.java:1: error: cannot find symbol\n  symbol:   variable Object\n  location: class A",68
        );
    }
    
    @Test
    public void testMonitorsFor5() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ monitors_for z = i; \n } class B { public Object z; }"
                ,"/A.java:1: error: The identifier must be a member of the enclosing class: z is in B instead of A",74
        );
    }
    
    //OK
    @Test
    public void testReadable() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ readable j if i == null; writable j if i == null; \n } class B { public Object z; }"
        );
    }
    
    @Test
    public void testReadable1() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if i == null; writable k if i == null; \n } class B { public Object z; }"
                ,"/A.java:1: error: non-static variable i cannot be referenced from a static context",75
                ,"/A.java:1: error: non-static variable i cannot be referenced from a static context",100
        );
    }
    
    @Test
    public void testReadable2() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ readable z if i == null; writable z if i == null; \n } class B { Object z; }"
                ,"/A.java:1: error: The identifier must be a member of the enclosing class: z",70
                ,"/A.java:1: error: The identifier must be a member of the enclosing class: z",95
        );
    }

    //OK
    @Test
    public void testReadable3() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if k == null; writable k if k == null; \n } class B { public Object z; }"
        );
    }
    
    //OK
    @Test
    public void testReadable4() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ readable i if this == null; writable i if this == null; \n } class B { public Object z; }"
        );
    }
    
    @Test
    public void testReadable5() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if this == null; writable k if this == null; \n } class B { public Object z; }"
                ,"/A.java:1: error: non-static variable this cannot be referenced from a static context",75
                ,"/A.java:1: error: non-static variable this cannot be referenced from a static context",103
        );
    }
    
    //OK
    @Test
    public void testReadable6() {
        helpTCText("A.java","public class A extends B {Object i,j; static Object k;  //@ readable k if Object.class == null; writable k if Object.class == null; \n } class B { public Object z; }"
        );
    }
    
    @Test
    public void gitbug107() {
        helpTCText("A.java",
                """
                public class A {
                  //@ axiom \\lockset == \\lockset;
                }
                """
                ,"/A.java:2: error: a \\locksest expression is not permitted in an axiom clause",13
                ,"/A.java:2: error: a \\locksest expression is not permitted in an axiom clause",25
                );
    }
    
    @Test
    public void gitbug212() {
        helpTCText("Depends.java",
                """
                public class Depends {
                    //@ public model int m;
                    private /*@ spec_public @*/ int f;
                    //@ private represents m = f;

                    //@ assignable f;
                    public void inc() {
                        f++;
                    }
                }
                """
                ,"/Depends.java:4: error: Because 'm' reads 'f' in a represents clause, 'f' must be 'in' the model field 'm'", 32
                );
    }
}

