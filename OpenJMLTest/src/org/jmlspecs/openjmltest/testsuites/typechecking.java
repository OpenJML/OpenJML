package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.*;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class typechecking extends TCBase {

    @Override
    public void setUp() throws Exception {
        super.setUp();
    }

    /** Test something very simple with no errors*/
    @Test public void testSomeJava() {
        helpTCText(null, "class A { public A(){} }");
    }

    /** Test something very simple with no errors*/
    @Test public void testSomeJavaB() {
        helpTCText(null, " class A {}");
    }

    /** Test a particular error*/
    @Test public void testSomeJavaBrace() {
        helpTCText(null, " class A {} }"
        ,"/TEST.java:1: error: class, interface, enum, or record expected",13,12,12,12 // FIXME - end position may not be useful - should be 13?
        );
    }

    /** Test scanning something very simple */
    @Test public void testSomeJava2() {
        helpTCText(null, " class A { int k = true; }",
                "/TEST.java:1: error: incompatible types: boolean cannot be converted to int",20);
    }

    /** Test scanning something very simple */
    @Test public void testSomeJML() {
        helpTCText(null, " class A { int k; boolean b; void m() { \n//@ assert k;\n}}",
                "/TEST.java:2: error: incompatible types: int cannot be converted to boolean",12);
    }

    @Test public void testTypeArgs() {
        helpTCText(null, " class A { int k; boolean b; <T> int mm() {} void m() { int t = this.<Integer>mm(); \n//@ assert <Object>\\old(k);\n}}"
                ,"/TEST.java:2: error: illegal start of expression",20
                );
    }
    
    @Test public void testCommentStatement() {
        helpTCText(null,  """
                class B {
                  void m() {
                    //@ comment 5;
                  }
                  void mm() { /*@ comment "asd"+"def"; */ }  // compiler collapses to a literal
                  void mq(int x) { /*@ comment "asd"+x; */ }
                  void mmm() { /*@ comment "asd"; */}
                }
                """
                ,"/TEST.java:3: error: incompatible types: int cannot be converted to java.lang.String", 17
                ,"/TEST.java:6: error: A comment statement may only contain a string literal", 37
                );
    }

    @Test public void testAlso0() {
        helpTCText(null, " class B { void m() {} } class A extends B { /*@ also requires true; */ void m() {}  /*@ requires true; */ void n() {}}"
                );
    }

    @Test public void testAlso1() {
        expectedExit = 0;
        helpTCText(null, " class B { void m() {} } class A extends B { /*@ requires true; */ void m() {} /*@ also requires true; */ void n() {}}"
                ,"/TEST.java:1: warning: [strict-jml] Method m overrides parent class methods and so its specification should begin with 'also' (A.m() overrides B.m())",50
                ,"/TEST.java:1: warning: [strict-jml] Method n does not override parent class methods and so its specification may not begin with 'also'",84
                );
    }

    @Test public void testAlso0I() {
        helpTCText(null, " interface B { void m(); } class A implements B { /*@ also requires true; */ public void m() {}  /*@ requires true; */ void n() {}}"
                );
    }

    @Test public void testAlso1I() {
        expectedExit = 0;
        helpTCText(null, " interface B { void m(); } class A implements B { /*@ public normal_behavior requires true; */ public void m() {} /*@ also requires true; */ void n() {}}"
                ,"/TEST.java:1: warning: [strict-jml] Method m overrides parent class methods and so its specification should begin with 'also' (A.m() overrides B.m())",62
                ,"/TEST.java:1: warning: [strict-jml] Method n does not override parent class methods and so its specification may not begin with 'also'",119
                );
    }

    @Test public void testAlso0II() {
        helpTCText(null, " interface B { void m(); } interface A extends B { /*@ also requires true; */ public void m();  /*@ requires true; */ void n();}"
                );
    }

    @Test public void testAlso1II() {
        expectedExit = 0;
        helpTCText(null, " interface B { void m(); } interface A extends B { /*@ requires true; */ void m(); /*@ also requires true; */ void n();}"
                ,"/TEST.java:1: warning: [strict-jml] Method m overrides parent class methods and so its specification should begin with 'also' (A.m() overrides B.m())",56
                ,"/TEST.java:1: warning: [strict-jml] Method n does not override parent class methods and so its specification may not begin with 'also'",88
                );
    }

    @Test public void testAlsoObject() {
        expectedExit = 0;
        helpTCText(null, "  interface A { /*@ also public normal_behavior requires true; */ String toString();}"
                );
    }

    @Test public void testAlsoObjectBad() {
        expectedExit = 0;
        helpTCText(null, "  interface A { /*@ public normal_behavior requires true; */ String toString();}"
                ,"/TEST.java:1: warning: [strict-jml] Method toString overrides parent class methods and so its specification should begin with 'also' (A.toString() overrides java.lang.Object.toString())",28
                );
    }
    
    @Test public void missingAlso() {
        addOptions("--lang=jml");
        helpTCText(null, "class A extends B { /*@ normal_behavior requires true; */ public void m() { } } class B { /*@ requires true; */ void m(){} } "
                ,"/TEST.java:1: error: Method m overrides parent class methods and so its specification should begin with 'also' (A.m() overrides B.m())", 25, 24, 24, 54
                );
    }

    @Test public void extraAlso() {
        addOptions("--lang=jml");
        helpTCText(null, "class A { /*@ also normal_behavior requires true; */ public void m() {  } }  "
                ,"/TEST.java:1: error: Method m does not override parent class methods and so its specification may not begin with 'also'", 15, 14, 14, 14
                );
    }

    @Test public void testOld1() {
        helpTCText(null, " class A { int k; boolean b; void m() { \n//@ assert \\old;\n}}",
                "/TEST.java:2: error: A \\old expression must have an argument list",12);
    }

    @Test public void testOld2() {
        helpTCText(null, " class A { int k; boolean b; void m() { \n//@ assert \\old();\n}}",
                "/TEST.java:2: error: A \\old expression expects just 1 or 2 arguments, not 0",16);
    }

    @Test public void testOld2a() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\pre();\n}}",
                "/A.java:2: error: A \\pre expression expects just 1 argument, not 0",16);
    }

    @Test public void testOld3() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(k);\n}}",
                "/A.java:2: error: incompatible types: int cannot be converted to boolean",16);
    }

    @Test public void testOld4() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(b);\n}}");
    }

    @Test public void testOld5() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\pre(b,k);\n}}",
                "/A.java:2: error: A \\pre expression expects just 1 argument, not 2",16
                );
    }

    @Test public void testOld6() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(b,5);\n}}",
                "/A.java:2: error: The second argument of an \\old expression must be a simple identifier that is a label",19);
    }

    @Test public void testOld7() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\old(b,k);\n}}"
                ,"/A.java:2: error: Unknown label: k",19);
    }

    @Test public void testOld8() {
        helpTCText("A.java"," class A { int k; boolean b; //@ requires \\old(b); \n void m() { }}",
                "/A.java:1: error: A \\old token with no label may not be present in a requires clause",48);
    }

    @Test public void testOld9() {
        helpTCText("A.java"," class A { int k; boolean b; //@ ensures \\old(b,k); \n void m() { }}",
                "/A.java:1: error: A \\old token with a label may not be present in a ensures clause",47);
    }

    @Test public void testOld10() {
        helpTCText("A.java"," class A { int k; boolean b; //@ requires \\pre(b); \n void m() { }}",
                "/A.java:1: error: A \\pre token may not be present in a requires clause",48);
    }

    @Test public void testOld11() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n k: k=1;\n //@ assert \\old(b,k);\n}}"
                );
    }

    @Test public void testOld12() {
        helpTCText("A.java"," class A { boolean b; void m() { \n k: {};\n boolean bb = false; //@ assert \\old(bb) && \\old(bb,k);\n}}"
                ,"/A.java:3: error: cannot find symbol\n  symbol:   variable bb\n  location: class A",38
                ,"/A.java:3: error: cannot find symbol\n  symbol:   variable bb\n  location: class A",50
                );
    }

    @Test public void testOld13() {
        helpTCText("A.java"," class A { boolean b; void m() { \n k: {};\n //@ assert \\old(b,k);\n}}"
                );
    }
    
    @Test public void replacement() {
        helpTCText("A.java",
                """
                public class A {
                  public static class B extends A {}
                  public static class X {}
                  void p(/*@[A]@*/ A a) {}
                  void q(/*@[B]@*/ A a) {}
                  void r(/*@[X]@*/ A a) {} // ERROR
                }
                """
                ,"/A.java:6: error: a replacement type must be a subtype of the source type: A.X A", 14
                );
    }

    @Test public void testMax() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max(\\lockset);\n}}",
                "/A.java:2: error: incompatible types: java.lang.Object cannot be converted to boolean",16);
    }

    @Test public void testMax1() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max;\n}}"
                ,"/A.java:2: error: illegal start of type",16
                ,"/A.java:2: warning: Inserting missing semicolon at the end of a assert statement", 17
                );
    }

    @Test public void testMax2() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max();\n}}",
                "/A.java:2: error: A \\max expression expects just 1 argument, not 0",16);
    }

    @Test public void testMax3() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max(k);\n}}",
                "/A.java:2: error: A \\max function expects an argument of type org.jmlspecs.lang.JMLSetType<E> rather than int",17,
                "/A.java:2: error: incompatible types: java.lang.Object cannot be converted to boolean",16
                );
    }

    @Test public void testMax5() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\max(b,k);\n}}",
                "/A.java:2: error: A \\max expression expects just 1 argument, not 2",16,
                "/A.java:2: error: A \\max function expects an argument of type org.jmlspecs.lang.JMLSetType<E> rather than boolean",17,
                "/A.java:2: error: incompatible types: java.lang.Object cannot be converted to boolean",16);
    }

    @Test public void testStaticInvariantFor1() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\static_invariant_for(Integer);\n}}"
                );
    }

    @Test public void testStaticInvariantFor2() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\static_invariant_for(Integer,Object);\n}}"
                );
    }

    @Test public void testStaticInvariantFor2a() {
        addOptions("-lang=jml");
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\static_invariant_for(Integer,Object);\n}}"
                ,"/A.java:2: error: A \\static_invariant_for expression expects just 1 argument, not 2",33
                );
    }

    @Test public void testStaticInvariantFor3() {
        helpTCText("A.java","public class A { Integer i; void m() { \n//@ assert \\static_invariant_for(java.lang.Integer);\n}}"
                );
    }

    @Test public void testStaticInvariantFor4() {
        helpTCText("A.java","public class A { void m() { \n//@ assume \\static_invariant_for(java.util.List);\n}}"
                );
    }

    @Test public void testStaticInvariantFor5() {
        helpTCText("A.java","public class A { void m() { \n//@ assume \\static_invariant_for(java.util.List<Integer>);\n}}"
                );
    }

    @Test public void testStaticInvariantFor6() {
        helpTCText("A.java","public class A<T> { void m() { \n//@ assume \\static_invariant_for(A<Integer>);\n}}"
                );
    }

    @Test public void testStaticInvariantFor7() {
        helpTCText("A.java","public class A<T> { void m() { \n//@ assume \\static_invariant_for(A<T>);\n}}"
                ,"/A.java:2: error: non-static type variable T cannot be referenced from a static context",36
                );
    }

    @Test public void testStaticInvariantFor8() {
        helpTCText("A.java","public class A<T> { void m() { \n//@ assume \\static_invariant_for(A);\n}}"
                );
    }

    @Test public void testStaticInvariantFor9() {
        helpTCText("A.java","public class A<T> { void m() { \n//@ assume \\static_invariant_for(int);\n}}"
                ,"/A.java:2: error: The argument of \\static_invariant_for must be a reference type name: int",34
                );
    }

    @Test public void testStaticInvariantFor10() {
        helpTCText("A.java","public class A<T> { void m() { \n//@ assume \\static_invariant_for(\\bigint);\n}}"
                ,"/A.java:2: error: The argument of \\static_invariant_for must be a reference type name: \\bigint",34
                );
    }

    @Test public void testStaticInvariantFor11() {
        helpTCText("A.java","public class A<T> { static int k = 0; void m() { \n//@ assume \\static_invariant_for(k);\n}}"
                ,"/A.java:2: error: cannot find symbol\n  symbol:   class k\n  location: class A<T>",34
                );
    }

    @Test public void testInvariantFor1() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(i);\n}}"
                );
    }

    @Test public void testInvariantFor2() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(k);\n}}"
                ,"/A.java:2: error: The argument of \\invariant_for must be of reference type", 27
                );
    }

    @Test public void testInvariantFor3() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(A);\n}}"
                );
    }

    @Test public void testInvariantFor4() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for();\n}}"
                );
    }

    @Test public void testInvariantFor5() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(Integer,k);\n}}"
                ,"/A.java:2: error: The argument of \\invariant_for must be of reference type", 35
                );
    }

    @Test public void testInvariantFor6() {
        addOptions("-lang=jml");
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(Integer,k);\n}}"
                ,"/A.java:2: error: A \\invariant_for expression expects just 1 argument, not 2", 26
                ,"/A.java:2: error: The argument of \\invariant_for must be of reference type", 27
                ,"/A.java:2: error: The argument of \\invariant_for must be of reference type", 35
                );
    }

    @Test public void testInvariantFor6a() {
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for(Integer,k);\n}}"
                ,"/A.java:2: error: The argument of \\invariant_for must be of reference type", 35
                );
    }

    @Test public void testInvariantFor7() {
        addOptions("-lang=jml");
        helpTCText("A.java","public class A { int k; Integer i; void m() { \n//@ assert \\invariant_for();\n}}"
                ,"/A.java:2: error: A \\invariant_for expression expects just 1 argument, not 0", 26
                );
    }


    @Test public void testType() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(A,k);\n}}"
                ,"/A.java:2: error: More than one argument or otherwise ill-formed type expression as argument of \\type",19
                );
    }

    @Test public void testType2() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type();\n}}"
                ,"/A.java:2: error: illegal start of type",18
                ,"/A.java:3: error: Incorrectly formed or terminated assert statement near here", 1
                ,"/A.java:3: error: reached end of file while parsing", 3
                );
    }

    @Test public void testType3() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(b);\n}}"
                ,"/A.java:2: error: cannot find symbol\n  symbol:   class b\n  location: class A",18
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType4() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(true);\n}}"
                ,"/A.java:2: error: illegal start of type",18
                );
    }

    @Test public void testType5() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(int);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType6() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(int[][]);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType7() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(Object);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType8() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(java.lang.Object);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                                );
    }

    @Test public void testType9() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(java.lang.Object[][]);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType10() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(A);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType11() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(void);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testType12() {
        helpTCText("A.java"," class A { int k; boolean b; void m() { \n//@ assert \\type(Void);\n}}"
                ,"/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",17
                );
    }

    @Test public void testTypeof() {
        helpTCText("A.java"," class A { int k; Boolean b; void m() { \n//@ assert \\typeof(b);\n}}",
                "/A.java:2: error: incompatible types: \\TYPE cannot be converted to boolean",19);
    }

    @Test public void testResult() {
        helpTCText(null, " class A { int k; Boolean b; void m() { \n//@ assert \\result;\n}}"
                ,"/TEST.java:2: error: A \\result expression may not be used in the specification of a method that returns void",13
                ,"/TEST.java:2: error: A \\result expression may not be in a assert clause",13
                );
    }

    @Test public void testResult3() {
        helpTCText("A.java"," public class A { int k; Boolean b;\n //@ ensures \\result;\n void m() { \n}}",
                "/A.java:2: error: A \\result expression may not be used in the specification of a method that returns void",15);
    }

    @Test public void testResult4() {
        helpTCText(null, " class A { int k; Boolean b;\n //@ assert \\result;\n void m() { \n}}",
                "/TEST.java:2: error: The token assert is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)",6);
    }

    @Test public void testResult2() {
        helpTCText("A.java",
                """
                 class A { int k; Boolean b;
                /*@ ensures \\result >= 1; */
                boolean m() {
                 return true;
                }}
                """
                ,"/A.java:2: error: bad operand types for binary operator '>='\n"
                + "  first type:  boolean\n"
                + "  second type: int",21);
    }

    @Test public void testResult5() {
        helpTCText("A.java",
                """
                 class A { int k; Boolean b;
                /*@ ensures \\result == 1; */
                 void m() { }}
                """
                ,"/A.java:2: error: A \\result expression may not be used in the specification of a method that returns void",14);
    }

    /** Tests an input that gave bugs once before */
    @Test public void testMisc1() {
        helpTCText(null, " class A { /*@ ensures \\result     ; */\nboolean m() { \n//@ return true;\n}}"
                ,"/TEST.java:3: error: Expected a declaration or a JML construct inside the JML annotation here", 5
        );
    }
    
    @Test public void testMisc1b() {
        helpTCText(null, " class A { /*@ ensures \\result     ; */\nboolean m() { \n//@ int t;\n}}"
                ,"/TEST.java:3: error: A local declaration within a JML annotation must be ghost: t in A.m()", 9
        );
    }
    
    @Test public void testJmlTypes() {
        helpTCText("A.java","public class A {  int i; /*@ ghost \\TYPE t; */ } ");  //OK
    }

    @Test public void testJmlTypes0() {
        helpTCText("A.java","public class A {  int i,j; /*@ ghost \\TYPE t,tt; */ } "); //OK
    }

    @Test public void testJmlTypes1() {
        helpTCText("A.java","public class A {  /*@ ghost \\bigint i; model \\real r; ghost \\TYPE t; */ } "); //OK
    }

    /** Missing model or ghost modifier */
    @Test public void testJmlTypes2() {
        helpTCText("A.java","public class A {  int i; /*@  \\TYPE t; */ } ",
                "/A.java:1: error: A declaration within a JML annotation must be either ghost or model: A.t",37);
    }

    /** Wrong position model or ghost modifier */
    @Test public void testJmlTypes3() {
        helpTCText("A.java","import org.jmlspecs.annotation.*; public class A {\n  @Ghost int i; } ",
                "/A.java:2: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A.i",3
                );
    }

    @Test public void testJmlTypes4() {
        helpTCText("A.java","import org.jmlspecs.annotation.*; public class A {\n  /*@ @Ghost Object i; */ } ");  //OK
    }

    @Test public void testJmlTypes4a() {
        helpTCText("A.java","import org.jmlspecs.annotation.*; public class A {\n  /*@ @Ghost int i; */ } ");  //OK
    }

    @Test public void testSubtype() { // OK
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t= \\type(int); */Class c;\n//@ ensures t <:= t;\nvoid m() {}}");
    }
    
    @Test public void testSubtype2() { // OK
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class c;\n//@ ensures c <:= c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype2a() { // OK
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ ensures c <:= c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype2b() { // OK
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<? extends Object> c;\n//@ ensures c <:= c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype3() { // OK
        expectedExit = 0;
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ ensures t <:= \\typeof(o);\nvoid m() {}}"
                );
    }
    
    @Test public void testSubtype4() { // OK
        expectedExit = 0;
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ ensures o.getClass() <:= Object.class;\nvoid m() {}}"
                //,"/A.java:2: warning: A non-pure method is being called where it is not permitted: getClass()",22
                );
    }
    
    @Test public void testSubtype5() {
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ ensures JML.erasure(t) <:= c;\nvoid m() {}}");
    }
    
    @Test public void testSubtype6() {
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ ensures t <:= 5;\nvoid m() {}}",
                "/A.java:2: error: The type of the arguments of the subtype operator (<:) must be either \\TYPE or java.lang.Class, not int",19);
    }
    
    @Test public void testSubtype7() {
        helpTCText("A.java","public class A { Object o; /*@ ghost \\TYPE t; */ Class<Object> c;\n//@ ensures true <:= c;\nvoid m() {}}",
                "/A.java:2: error: The type of the arguments of the subtype operator (<:) must be either \\TYPE or java.lang.Class, not boolean",13);
    }
    
    @Test public void testErasure1() {
        helpTCText("A.java","public class A { Object o; //@ ghost \\TYPE t = \\type(java.lang.Integer);\n}"
                );
    }
    
    @Test public void testErasure2() {
        helpTCText("A.java","public class A { Object o; //@ ghost \\TYPE t = \\type(java.util.List);\n}"
                ,"/A.java:1: error: The argument of a \\type construct must be a fully parameterized type: java.util.List",53
                );
    }
    
    @Test public void testErasure3() {
        helpTCText("A.java","public class A { Object o; //@ ghost \\TYPE t = \\type(java.util.List<Integer>);\n}"
                );
    }
    
    @Test public void testErasure4() {
        helpTCText("A.java","public class A { Object o; //@ ghost Class<?> t = \\erasure(\\type(java.lang.Integer));\n}"
                );
    }
    
    @Test public void testErasure5() {
        helpTCText("A.java","public class A { Object o; //@ ghost Class<?> t = \\erasure(\\type(java.util.List));\n}"
                ,"/A.java:1: error: The argument of a \\type construct must be a fully parameterized type: java.util.List",65
                );
    }
    
    @Test public void testErasure6() {
        helpTCText("A.java","public class A { Object o; //@ ghost Class<?> t = \\erasure(\\type(java.util.List<Integer>));\n}"
                );
    }
    
    @Test public void testMisplacedResult() {
        helpTCText("A.java","public class A {  \n//@ requires \\result == 0;\n int m() {return 0;}}",
                "/A.java:2: error: A \\result expression may not be in a requires clause",15);
        
    }
    
    @Test public void testSetComp() {
        helpTCText("A.java","public class A {  \n java.util.Collection c; //@ invariant new JMLSetType { Integer i | c.contains(i) && i<10}; \n \n }"
                //,"/A.java:2: warning: A non-pure method is being called where it is not permitted: contains(java.lang.Object)",79  // FIXME
                ,"/A.java:2: error: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to boolean",55
        );
    }
    
    // Testing scopes in method specs
    @Test public void testSetCompA() {
        helpTCText("A.java","public class A {  \n java.util.Collection c; //@ requires new JMLSetType { Integer i | c.contains(i) && i<10}; \n void m() {} \n }"
                //,"/A.java:2: warning: A non-pure method is being called where it is not permitted: contains(java.lang.Object)",78 // FIXME
                ,"/A.java:2: error: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to boolean",54
                );
    }

    @Test public void testQuantifierA() {
        helpTCText("A.java","public class A {  \n Object i; //@ ghost Object j; \n //@ requires m( (\\exists int i; 0 < i && i <10; m(i)) ); \n/*@ pure*/boolean m(int k) { return false; }\n }",
                "/A.java:3: error: incompatible types: boolean cannot be converted to int",19);
    }
  
    @Test public void testSetCompB() {
        helpTCText("A.java","public class A {  \n java.util.Collection c; //@ ghost int k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n void m() {} \n }"
                ,"/A.java:2: error: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to int",59
        );
    }

    @Test public void testSetCompB3() {
        helpTCText("A.java","public class A {  boolean p; \n java.util.Collection c; //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && p<10}; \n void m() {} \n }"
                ,"/A.java:2: error: bad operand types for binary operator '<'\n  first type:  boolean\n  second type: int",94
        );
    }

    @Test public void testSetCompB2() {
        helpTCText("A.java","public class A {  \n java.util.Collection c; //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n void m() {} \n }"
        );
    }

    @Test public void testQuantifierB() {
        helpTCText("A.java","public class A {  \n  //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \nboolean m(int k) { return false; }\n }",
                "/A.java:2: error: incompatible types: boolean cannot be converted to int",28);
    }
  
    @Test public void testQuantifierB2() {
        helpTCText("A.java","public class A {  \n  //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \nboolean m(boolean k) { return false; } boolean m(int p) { return false; }\n }"
                );
    }
  
    @Test public void testQuantifierB3() {
        helpTCText("A.java","public class A {  \n  //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \nboolean m(boolean k) { return false; } \n }"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",61
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",61  // FIXME - why a duplicate error message
                );
    }
  
    // Looking for a name in the outer scope
    @Test public void testQuantifierB4() {
        helpTCText("A.java","public class A { boolean p;  \n  //@ ghost boolean j = ( (\\exists int i; 0 < i && i <10; m(p)) ); \nboolean m(int k) { return false; } \n }"
                ,"/A.java:2: error: incompatible types: boolean cannot be converted to int",61
                );
    }
  
    // testing scopes in local initializers
    @Test public void testSetCompC() {
        helpTCText("A.java","public class A {  \n java.util.Collection c;  void m() { //@ ghost int k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n} \n }"
                ,"/A.java:2: error: incompatible types: org.jmlspecs.lang.JMLSetType cannot be converted to int",71
                );
    }

    @Test public void testSetCompC3() {
        helpTCText("A.java","public class A {  \n java.util.Collection c;  void m() { boolean p; //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && p<10}; \n} \n }"
                ,"/A.java:2: error: bad operand types for binary operator '<'\n  first type:  boolean\n  second type: int",117
                );
    }

    @Test public void testSetCompC2() {
        helpTCText("A.java","public class A {  \n java.util.Collection c;  void m() { //@ ghost Object k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n} \n }"
                );
    }

    @Test public void testQuantifierC() {
        helpTCText("A.java","public class A {  \n  boolean m(int k) { //@ ghost Object j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \n return false; }\n }",
                "/A.java:2: error: incompatible types: boolean cannot be converted to int",47
                );
    }
    
    @Test public void testQuantifierC2() {
        helpTCText("A.java","public class A {  \n  boolean m(int k) { //@ ghost boolean j = ( (\\exists int i; 0 < i && i <10; m(i)) ); \n return false; }\n }"
                );
    }
    
    @Test public void testQuantifierC3() {
        helpTCText("A.java","public class A {  \n  boolean m(int k) { boolean p ; //@ ghost boolean j = ( (\\exists int i; 0 < i && i <10; m(p)) ); \n return false; }\n }",
                "/A.java:2: error: incompatible types: boolean cannot be converted to int",92
                );
    }
    
    // testing scopes in JML statements
    @Test public void testSetCompD() {
        helpTCText("A.java","public class A {//@ ghost Object k;  \n java.util.Collection c;  void m() { //@ set k = new JMLSetType { Integer i | c.contains(i) && i<10}; \n} \n }"
                );
    }

    @Test public void testQuantifierOK() {
        helpTCText("A.java","public class A { \n/*@ pure */ boolean n(boolean b) { return b; }; \n/*@ pure*/ boolean m(int i) { return false; }\n//@ invariant n( (\\exists int i; 0 < i && i <10; m(i)) ); \n }"
                );
    }
    
    @Test public void testQuantifierD() {
        helpTCText("A.java","public class A { //@ ghost int j;\n  \n  boolean m(int k) { //@ set j = m( (\\exists int i; 0 < i && i <10; m(i)) ); \n return false; }\n }"
                ,"/A.java:3: error: incompatible types: boolean cannot be converted to int",38
                );
    }
    
    // FIXME - error message column is not clear to user when the quantifier is a method argument
    
    @Test public void testQuantifier() {
        helpTCText("A.java","public class A {  \n Object i; //@ ghost Object j; \n /*@ pure*/ boolean m(int i) { return false; }\n//@ invariant m( (\\exists int i; 0 < i && i <10; m(i)) ); \n }",
                "/A.java:4: error: incompatible types: boolean cannot be converted to int",19);
    }
    
    @Test public void testQuantifier1() {
        helpTCText("A.java","public class A {  \n Object i; //@ ghost Object j; \n /*@ pure*/ boolean m(int i) { return false; }\n//@ invariant m( (\\forall int i; 0 < i && i <10; m(i)) ); \n }",
                "/A.java:4: error: incompatible types: boolean cannot be converted to int",19);
    }
    
    @Test public void testQuantifier2() {
        helpTCText("A.java","public class A {  \n Object i; //@ ghost Object j; \n /*@ pure*/ boolean m(int i) { return false; }\n//@ invariant (\\num_of int i; 0 < i && i <10; m(i)) ; \n }",
                "/A.java:4: error: incompatible types: \\bigint cannot be converted to boolean",16
                );
    }
    
    @Test public void testQuantifier3() {
        helpTCText("A.java","public class A {  \n Object i; //@ ghost Object j; \n boolean m(int i) { return false; }\n//@ invariant (\\max long i; 0 < i && i <10; i) ; \n }",
                "/A.java:4: error: incompatible types: long cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier4() {
        helpTCText("A.java","public class A {  \n Object i; //@ ghost Object j; \n boolean m(float i) { return false; }\n//@ invariant (\\sum long i; 0 < i && i <10; i) ; \n }",
                "/A.java:4: error: incompatible types: long cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier5() {
        helpTCText("A.java","public class A {  \n Object i; //@ ghost Object j; \n boolean m(double i) { return false; }\n//@ invariant (\\product long i,k; 0 < i && k <10; i) ; \n }",
                "/A.java:4: error: incompatible types: long cannot be converted to boolean",16);
    }
    
    @Test public void testQuantifier6() {
        helpTCText("A.java","public class A {  \n Object i; Object q = i; //@ ghost Object j; \n boolean m(double i) { return false; }\n//@ invariant (\\product long i; j; i) ; \n }",
                "/A.java:4: error: incompatible types: java.lang.Object cannot be converted to boolean",33,
                "/A.java:4: error: incompatible types: long cannot be converted to boolean",16
                );
    }
    
    @Test public void testQuantifier7() {
        helpTCText("A.java","public class A {  \n Object i; Object j; \n boolean m(double i) { return false; }\n//@ invariant (\\product long i; 0 < j && i <10; i) ; \n }",
                "/A.java:4: error: bad operand types for binary operator '<'\n  first type:  int\n  second type: java.lang.Object",35,
                "/A.java:4: error: incompatible types: long cannot be converted to boolean",16);
    }

    @Test public void testQuantifierChoose() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; 0<i<10; i>5) > 5; */}}"

                );
    }
    
    @Test public void testQuantifierChoose1a() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; 0<i<10; i) > 5; */}}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",48
                );
    }
    
    @Test public void testQuantifierChoose1b() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; 0<i<10; 0) > 5; */}}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",48
                );
    }
    
    @Test public void testQuantifierChoose2a() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; i; i>5) > 5; */}}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",40
                );
    }
    
    @Test public void testQuantifierChoose2b() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; 0; i>5) > 5; */}}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",40
                );
    }
    
    @Test public void testQuantifierChoose3() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; ; i>5) > 5; */}}"

                );
    }
    
    @Test public void testQuantifierChoose4() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; i>5) > 5; */}}"

                );
    }
    @Test public void testQuantifierChoose5() {
        helpTCText("A.java","public class A {  \n void m() { /*@ assert (\\choose int i; i>5); */}}"
                ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",25
                );
    }
    
   @Test public void testQuantifierInv() {
        helpTCText("A.java","public class A {  \n //@ invariant (\\exists int i; 0 < i && i <10;  i > -1) ; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > -1) ; \n void m() {}}"

                );
    }
    
    @Test public void testQuantifierInv1() {
        helpTCText("A.java","public class A { int m; static int s; \n //@ invariant (\\exists int i; 0 < i && i <10;  i > m) ; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > m) ; \n void m() {}}"
                ,"/A.java:3: error: non-static variable m cannot be referenced from a static context",60
                );
    }
    
    @Test public void testQuantifierInv2() {
        helpTCText("A.java","public class A { int m; static int s; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > s) ; \n //@ static invariant (\\exists int i; 0 < i && i <10;  i > s) ; \n void m() {}}"

                );
    }
    
    @Test public void testQuantifierInit() {
        helpTCText("A.java","public class A { int m; static int s; \n //@ ghost boolean b = (\\exists int i; 0 < i && i <10;  i > m) ; \n //@ static ghost boolean bb = (\\exists int i; 0 < i && i <10;  i > m) ; \n //@ requires b && bb;\n void m() {}}"
                ,"/A.java:3: error: non-static variable m cannot be referenced from a static context",69
                );
    }
    
    @Test public void testQuantifierInit1() {
        helpTCText("A.java","public class A { int m; static int s; \n //@ ghost boolean b = (\\exists int i; 0 < i && i <10;  i > s) ; \n //@ static ghost boolean bb = (\\exists int i; 0 < i && i <10;  i > s) ; \n //@ requires b && bb;\n void m() {}}"

                );
    }
    
    @Test public void testQuantifierReq() {
        helpTCText("A.java","public class A {  \n //@ requires (\\exists int i; 0 < i && i <10;  i > -1) ; \n  void m() {}}"

                );
    }
    
    @Test public void testQuantifierReq2() {
        helpTCText("A.java","public class A {  \n //@ requires (\\exists int i; 0 < i && i <10;  i > -1) ; \n  static void m() {}}"

                );
    }
    

    @Test public void testLetX1() {
        helpTCText("A.java","public class A { void m() { //@ assert (\\let ghost int i = 0; i != 0); \n}}"
                ,"/A.java:1: error: ghost or model modifiers not permitted on an expression-local declaration",46
                );
    }
    
    @Test public void testLetX2() {
        helpTCText("A.java","public class A { void m() { //@ assert (\\let model int i = 0; i != 0); \n}}"
                ,"/A.java:1: error: ghost or model modifiers not permitted on an expression-local declaration",46
                );
    }
    
    @Test public void testLet() {
        helpTCText("A.java","public class A { void m() { //@ assert (\\let int i = 0; i != 0); \n}}"
                );
    }
    
    @Test public void testLet2() {
        helpTCText("A.java","public class A { void m() { //@ assert 0 == (\\let int i = 0, int j = 2; i - j); \n}}"
                );
    }
    
    @Test public void testLet3() {
        helpTCText("A.java","public class A { void m() { //@ assert (\\let int i = 0; i); \n}}"
                ,"/A.java:1: error: incompatible types: int cannot be converted to boolean",41);
    }
    
    @Test public void testLet4() {
        helpTCText("A.java","public class A { void m() { //@ assert (\\let int i; i>=0); \n}}"
                ,"/A.java:1: error: = expected",51);
    }
    
    @Test public void testLet5() {
        helpTCText("A.java","public class A { void m() { boolean i; //@ assert (\\let int i=0; i>=0); \n i = true; }}"
                ,"/A.java:1: error: variable i is already defined in method m()",61
                );
    }
    
    @Test public void testLet6() {
        helpTCText("A.java","public class A { void m(boolean i) {  //@ assert (\\let int i=0; i>=0); \n i = true; }}"
                ,"/A.java:1: error: variable i is already defined in method m(boolean)",60
                );
    }
    
    @Test public void testLet7() {
        helpTCText("A.java","public class A { boolean i; //@ invariant (\\let int i=0; i>=0); \n  }"
                );
    }

    @Test public void testLet8() {
        helpTCText("A.java","public class A { void m(int j) {  //@ assert (\\let int i=0; i>=j); \n  }}"
                );
    }
    
    @Test public void testLet9() {
        helpTCText("A.java","public class A { int j; //@ invariant (\\let int i=0; i>=j); \n  }"
                );
    }

    @Test public void testLet10() {
        helpTCText("A.java","public class A { void m(boolean j) {  //@ assert (\\let int i=0; i>=j); \n  }}"
                ,"/A.java:1: error: bad operand types for binary operator '>='\n"
                        + "  first type:  int\n"
                        + "  second type: boolean",66);
    }
    
    @Test public void testLet11() {
        helpTCText("A.java","public class A { boolean j; //@ invariant (\\let int i=0; i>=j); \n  }"
                ,"/A.java:1: error: bad operand types for binary operator '>='\n"
                        + "  first type:  int\n"
                        + "  second type: boolean",59);
    }


    @Ignore  // FIXME - what is \same?
    @Test public void testSame() {
        helpTCText("A.java","public class A { //@ requires  i; also requires \\same; \n boolean m(boolean i) { return false; }\n}"
                );
    }
    @Ignore  // FIXME - what is \same?
    @Test public void testSame1() {
        helpTCText("A.java","public class A { //@ requires 1+\\same; \n boolean m(double i) { return false; }\n}",
                "/A.java:1: error: bad operand types for binary operator '+'\n  first type:  int\n  second type: boolean",32);
    }
    @Ignore // FIXME - should not allow \same inside expressions
    @Test public void testSame2() { 
        helpTCText("A.java","public class A { //@ requires i; also requires !\\same; \n boolean m(boolean i) { return false; }\n}"
                );
    }
    
    @Ignore // FIXME - should not allow \same without previous preconditions
    @Test public void testSame3() {
        helpTCText("A.java","public class A { //@ requires \\same; \n boolean m(double i) { return false; }\n}"
                );
    }
    
    @Ignore // FIXME - semantics of \same
    @Test public void testSame4() {
        helpTCText("A.java","public class A { //@ ensures \\same; \n boolean m(double i) { return false; }\n}"
                ,"/A.java:1: error: A \\same token may only be used in requires clauses",30
                );
    }

    // FIXME
//    @Test public void testLockCompare() {
//        expectedExit = 0;
//        helpTCFText("A.java","public class A { Object o,oo; //@ invariant o < oo; \n }"
//                ,"/A.java:1: warning: Operators < and <= are deprecated as lock comparisons - use <# and <#= instead",47
//                );
//    }
    
    @Test public void testLockCompareX() {
        helpTCText("A.java","public class A { Integer o,oo; //@ invariant o < oo; \n }"
                );
    }
    
    // FIXME
//    @Test public void testLockCompare1() {
//        expectedExit = 0;
//        helpTCFText("A.java","public class A { Object o,oo; //@ invariant o <= oo; \n }"
//                ,"/A.java:1: warning: Operators < and <= are deprecated as lock comparisons - use <# and <#= instead",47
//                );
//    }
    
    @Test public void testLockCompare1X() {
        helpTCText("A.java","public class A { Integer o,oo; //@ invariant o <= oo; \n }"
                );
    }
    
    @Test public void testLockCompare2() {
        helpTCText("A.java","public class A { Object o,oo; int i; //@ invariant o < true; \n }"
                ,"/A.java:1: error: bad operand types for binary operator '<'\n  first type:  java.lang.Object\n  second type: boolean",54
                );
    }
    
    @Test public void testLockCompare2X() {
        helpTCText("A.java","public class A { Integer o,oo; int i; //@ invariant o < 5; \n }"
                );
    }
    
    @Test public void testLockCompare2Y() {
        helpTCText("A.java","public class A { Object o,oo; int i; //@ invariant o < 5; \n }"
                ,"/A.java:1: error: bad operand types for binary operator '<'\n  first type:  java.lang.Object\n  second type: int",54
                );
    }
    
    @Test public void testLockCompare3() {
        helpTCText("A.java","public class A { Object o,oo; boolean b = o <= oo;  \n }"
                ,"/A.java:1: error: bad operand types for binary operator '<='\n  first type:  java.lang.Object\n  second type: java.lang.Object",45
                );
    }
    
    @Test public void testLockCompare4() {
        helpTCText("A.java","public class A { Object o,oo; boolean b = o <= oo;  \n }"
                ,"/A.java:1: error: bad operand types for binary operator '<='\n  first type:  java.lang.Object\n  second type: java.lang.Object",45
                );
    }
    
    @Test public void testLockCompareA() {
        helpTCText("A.java","public class A { Object o,oo; //@ invariant o <# oo; \n }"
                );
    }
    
    @Test public void testLockCompare1A() {
        helpTCText("A.java","public class A { Object o,oo; //@ invariant o <#= oo; \n }"
                );
    }
    
    @Test public void testFreshBad() {
        helpTCText("A.java","public class A { Object o,oo; //@ invariant \\fresh(o);  \n }"
                ,"/A.java:1: error: A \\fresh expression may not be in a invariant clause",52
                );
    }
    
    @Test public void testFreshWeirdError() {
        helpTCText("WeirdError.java",
                """
                public class WeirdError {
                 public Foo getFoo() { return null; }
                }
                """
                ,"/WeirdError.java:2: error: cannot find symbol\n  symbol:   class Foo\n  location: class WeirdError",9
               // ,"/WeirdError.java:2: error: A \\result expression may not be used in the specification of a method that returns void",14
                );
    }
    
    @Test public void testFresh() {
        helpTCText("A.java","public class A { Object o,oo; //@ ensures \\fresh(o); \n void m() {} \n }"
                );
    }
    
    @Test public void testFresh2() {
        helpTCText("A.java","public class A { Object o; //@ ensures \\fresh(o,oo); \n void m() {}  \n }"
                ,"/A.java:1: error: Unknown label: oo",49
                );
    }
    
    @Test public void testFresh3() {
        helpTCText("A.java","public class A { Object o,oo; //@ ensures \\fresh(); \n void m() {}  \n }"
                ,"/A.java:1: error: A \\fresh expression expects just 1 or 2 arguments, not 0",49
                );
    }
    
    @Test public void testFresh4() {
        helpTCText("A.java","public class A { int i; Object o,oo; //@ ensures   \\fresh(i); \n void m() {}  \n }"
                ,"/A.java:1: error: The argument of \\fresh must be of reference type",59
                );
    }
    
    @Test public void testFresh5() {
        helpTCText("A.java","public class A { int i; Object o,oo; //@ ensures   \\fresh(o) + 1 == 0; \n void m() {}  \n }"
                ,"/A.java:1: error: bad operand types for binary operator '+'\n  first type:  boolean\n  second type: int",62
                );
    }
    
    @Test public void testFresh5Bad() {
        helpTCText("A.java","public class A { int i; Object o,oo; //@ ghost boolean k = \\fresh(o);  \n }"
                ,"/A.java:1: error: A \\fresh expression may not be in a jml declaration clause",67
        );
    }
    
    @Test public void testOnlyAssigned() {
        helpTCText("A.java","public class A { Object o,oo; //@ invariant \\only_assigned(o) || \\only_accessed(o) || \\only_captured(o) || \\not_assigned(o) || \\not_modified(o);  \n }"
                ,"/A.java:1: error: A \\only_assigned expression may not be in a invariant clause",59
                ,"/A.java:1: error: A \\only_accessed expression may not be in a invariant clause",80
                ,"/A.java:1: error: A \\only_captured expression may not be in a invariant clause",101
                ,"/A.java:1: error: A \\not_assigned expression may not be in a invariant clause",121
                ,"/A.java:1: error: A \\not_modified expression may not be in a invariant clause",141
                );
    }
    
    @Test public void testOnlyAssigned1() {
        helpTCText("A.java","public class A { Object o,oo; //@ ensures \\only_assigned(o) || \\only_accessed(o) || \\only_captured(o) || \\not_assigned(o) || \\not_modified(o); \n void m() {} \n }"
                );
    }
    
    @Test public void testOnlyAssigned2() {
        helpTCText("A.java","public class A { int i; Object o,oo; //@ ghost boolean k = \\only_assigned(o) || \\only_accessed(o) || \\only_captured(o) || \\not_assigned(o) || \\not_modified(o);  \n }"
                ,"/A.java:1: error: A \\only_assigned expression may not be in a jml declaration clause",74
                ,"/A.java:1: error: A \\only_accessed expression may not be in a jml declaration clause",95
                ,"/A.java:1: error: A \\only_captured expression may not be in a jml declaration clause",116
                ,"/A.java:1: error: A \\not_assigned expression may not be in a jml declaration clause",136
                ,"/A.java:1: error: A \\not_modified expression may not be in a jml declaration clause",156
        );
    }
    
    @Test public void testInformalComment() {
        helpTCText("A.java","public class A {\n //@ invariant (* stuff *);\n //@ ghost int k = (* stuff *);  \n }"
                ,"/A.java:3: error: incompatible types: boolean cannot be converted to int",20
        );
    }

    @Test public void testId() {
        helpTCText("A.java","public class A {\n //@ public model int duration;  \n void m() { //@ set duration = 0;\n } \n }"
//                ,"/A.java:2: error: Expected an identifier, found a JML keyword instead: duration",23
        );
    }

    // The following are situations that are not yet handled properly.
    // That is because model imports are treated just like normal imports,
    // so they can lead to incorrect name resolution in the Java code.

    // Should have one error: the use of List in the declaration of n should fail.
    @Test public void testModelImport1() {
        helpTCText("A.java","//@ model import java.util.List;\n public class A {\n //@ ghost List k;\n List n;  \n }"
                ,"/A.java:4: error: cannot find symbol\n"
                        + "  symbol:   class List\n"
                        + "  location: class A",2
        );
    }
    
    // This should fail for the ghost declaration but not for the Java declaration
    @Test public void testModelImport2() {
        helpTCText("A.java","import java.awt.*; //@ model import java.util.*;\n public class A {\n //@ ghost List k;\n List n;  \n }"
                ,"/A.java:3: error: reference to List is ambiguous\n  both interface java.util.List in java.util and class java.awt.List in java.awt match",12
        );
    }

    // This should fail for the Java declaration but not for the ghost declaration
    @Test public void testModelImport3() {
        helpTCText("A.java","import java.awt.*; import java.util.*;\n//@ model import java.util.List;\n public class A {\n //@ ghost List k;\n List n;  \n }"
                ,"/A.java:5: error: reference to List is ambiguous\n"
                + "  both interface java.util.List in java.util and class java.awt.List in java.awt match",2
                );
    }

    @Test public void testOKImport1() {
        helpTCText("A.java","import java.util.*;\n public class A {\n List n;  \n }"
        );
    }
    
    @Test public void testBadModelImport1() {
        helpTCText("A.java","//@ import java.util.List;\n public class A {\n //@ ghost List k;\n List n;  \n }"
                ,"/A.java:1: error: An import statement in a JML comment must have a model modifier",5
        );
    }
    
    @Test public void testBadModelImport2() {
        helpTCText("A.java","/*@ model */ import java.util.List;\n public class A {\n  \n }"
                ,"/A.java:1: error: A model import declaration must be completely within a JML comment",14,13,13,34
        );
    }
    
    @Test public void testBadModelImport2a() {
        helpTCText("A.java","/*@ model */  public class A {\n  \n }"
                ,"/A.java:1: error: A Java declaration (not within a JML annotation) may not be either ghost or model: A",5
        );
    }
    
    @Test public void testBadModelImport3() {
        helpTCText("A.java","/*@ model import */ java.util.List;\n public class A {\n  \n }"
                ,"/A.java:1: error: Expected an identifier, found end of JML comment instead",18
                ,"/A.java:1: error: '.' expected",20
        );
    }
    
    // Bug: 3366092
    @Test public void testEnum1() {
        helpTCText("A.java","public class A {\n  enum E { X {} }; \n }"
        );
        
    }
    
    // Bug: 3366092
    @Test public void testEnum2() {
        helpTCText("A.java","public class A {\n  enum E { X {}; } \n }"
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3() {
        helpTCText("A.java","public class A {\n  public enum X { Y; X(){}; } \n }"
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3a() {
        helpTCText("A.java","public class A {\n  public enum X { Y; public X(){}; } \n }"
        ,"/A.java:2: error: modifier public not allowed here",29
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3b() {
        helpTCText("A.java","public class A {\n  public enum X { Y; protected X(){}; } \n }"
                ,"/A.java:2: error: modifier protected not allowed here",32
        );
        
    }
    
    // Bug: 3241186
    @Test public void testEnum3c() {
        helpTCText("A.java","public class A {\n  public enum X { Y; private X(){}; } \n }"
        );
        
    }
    
    // Bug: 3421143
    @Test public void testEnum4() {
        helpTCText("A.java","public class A {\n  public enum X { Y; public X m() { for (X c: values()) break; return Y; } } \n }"
        );
        
    }
    
    // Bug: 3373400
    @Test public void testBug4() {
        helpTCText("A.java","interface A<V> { /*@ instance ghost V r; @*/ \n }"
        );
        
    }
    
    // Bug: 3377329
    @Test public void testBug5() {
        helpTCText("A.java",
                """
                public class A {
                  public void test1(Object[] blub) {
                    //@ loop_invariant 0<=i && i <= blub.length;
                    for(int i=0; i< blub.length; i++) {
                      /*@nullable @*/ Object b = blub[i];
                      if (b == null)
                        continue;
                    }
                  }
                  public void test2(Object[] blub) {
                    for(Object b : blub) {
                      if (b == null)
                        continue;
                    }
                  }
                }
                """
                );
    }
    
    // Bug: 3377329
    @Test public void testBug5a() {
        helpTCText("A.java",
                """
                public class A {
                  public void test1(Object[] blub) {
                    //@ loop_invariant 0<=i && i <= blub.length;
                    for(int i=0; i< blub.length; i++) {
                      /*@nullable @*/ Object b = blub[i];
                      if (b == null)
                        break;
                    }
                  }
                  public void test2(Object[] blub) {
                    for(Object b : blub) {
                      if (b == null)
                        break;
                    }
                  }
                }
                """
                );
    }
    
    // Bug: 3388690
    @Test public void testBug6() {
        expectedExit = 0;
        helpTCText("Test.java",
                """
                public class Test {
                private final int my_height; /*@ in height; @*/
                  /*@ public model int height;
                      in_redundantly height;
                      public invariant 0 < height;
                      public constraint \\old(height) == height;
                      private represents height = my_height;
                      private invariant 0 < my_height;
                  @*/
                  public Test() {
                    my_height = 1;
                  }
                }
                """
                ,"/Test.java:4: warning: Do not include a datagroup in itself: height",22
                ,"/Test.java:4: warning: Do not include a datagroup in itself: height",22
        );
    }
    
    @Test public void testComment() {
        expectedExit = 1;
        helpTCText("Test.java",
                """
                public class Test {
                  /*@ ghost String s = "asdf */"; */
                }
                """
                ,"/Test.java:2: error: Unclosed string literal at end of JML annotation",30
                ,"/Test.java:2: error: unclosed string literal",32
                ,"/Test.java:4: error: reached end of file while parsing",1
            );
    }
    
    @Test public void testComment2() {
        expectedExit = 1;
        helpTCText("Test.java",
                """
                public class Test {
                  /*@ ghost int i = 0; /* comment */
                  /*@ ghost int j = 0; */
                  /*@ ghost int k = 0; */
                }
                """
                ,"/Test.java:2: error: Block comments may not be embedded inside JML block comments",24
            );
    }
    
    @Test public void testComment3() {
        expectedExit = 1;
        helpTCText("Test.java",
                """
                public class Test {
                  /*@ ghost int i = 0;
                    @ ghost String j = "  ;
                    @ ghost int k = 0; */
                }
                """
                ,"/Test.java:3: error: unclosed string literal",24
                ,"/Test.java:3: error: ';' expected", 29
            );
    }
    
    @Test public void testSpillover1() {
        expectedExit = 0;
        helpTCText("Test.java",
                """
                public class Test {
                //@ requires i
                //@    > 0
                //@   ; ensures \\result >
                //@   0
                  public int m(int i) { return i;}
                }
                """
                ,"/Test.java:5: warning: Inserting missing semicolon at the end of a ensures statement",8
            );
    }
    
    @Test public void testSpillover2() {
        helpTCText("Test.java",
                """
                public class Test {
                //@ requires i
                //@    > 0
                //@   ensures \\result >
                //@   0
                  public int m(int i) { return i;}
                }
                """
                ,"/Test.java:3: error: Incorrectly formed or terminated requires statement near here -- perhaps a missing semicolon",11
                ,"/Test.java:5: warning: Inserting missing semicolon at the end of a ensures statement",8
            );
    }
    
    @Test public void testBug6a() {
        helpTCText("Test.java",
                """
                public class Test {
                private final int my_height; /*@ in height; @*/
                  /*@ public model int height;
                      in_redundantly height2;
                  @*/
                  /*@ public model int height2;
                      in_redundantly height;
                  @*/
                  public Test() {
                    my_height = 1;
                  }
                }
                """
                ,"/Test.java:6: error: This field participates in a circular datagroup inclusion chain: height2 -> height -> height2",24
                ,"/Test.java:3: error: This field participates in a circular datagroup inclusion chain: height -> height2 -> height",24
                ,"/Test.java:2: error: This field participates in a circular datagroup inclusion chain: my_height -> height -> height2 -> height",19
        );

    }
    
    @Test
    public void typeserr() {
        helpTCText("A.java",
           "class A { //@ ghost boolean b4 = \\type(java.util.Map<java.util.List<?>,?>) <:= \\type(java.util.List<?>);\n}"
                ,"/A.java:1: error: Wildcards are not allowed within \\type expressions: java.util.Map<java.util.List<?>, ?>",69
                ,"/A.java:1: error: Wildcards are not allowed within \\type expressions: java.util.Map<java.util.List<?>, ?>",72
                ,"/A.java:1: error: Wildcards are not allowed within \\type expressions: java.util.List<?>",101
           );
    }
        

    
    @Test public void testSwitchWithStrings() {
        helpTCText("A.java"," class A { public void m(String s) { switch (s) { case \"David\": case \"Cok\": System.out.println(\"me\"); break; default: System.out.println(\"not me\"); } } }"
                );
    }

    @Test public void testQuantifiedExpression() {
        helpTCText("A.java"," class A { /*@ public invariant (\\sum Integer i; 0<=i && i < 6; new Object()); */ }"
                ,"/A.java:1: error: Quantifier bodies may not contain constructors: Object()",65
                ,"/A.java:1: error: Object allocation is not permitted in specification expressions",65
                ,"/A.java:1: error: The value expression of a sum or product expression must be a numeric type, not java.lang.Object",65
                );
    }

    // FIXME - does not appear to be working yet
//    @Test public void testDiamondGenerics() {
//        helpTCFText("A.java","public class A { java.util.List<Integer> list = new java.util.LinkedList<>(); } }"
//                );
//    }

    @Test public void testMultiCatch() {
        helpTCText("A.java","public class A { public void m(int i) { try { if (i == 0) throw new ArrayIndexOutOfBoundsException(); if (i == 1) throw new NullPointerException(); } catch ( final ArrayIndexOutOfBoundsException | NullPointerException e) {}  } }"
                );
    }

    @Test public void testTryWithResources() {
        helpTCText("A.java","import java.io.*; public class A { public void m(int i) { try ( FileReader r = new FileReader(\"\") ) {   } catch (final IOException e) {} finally {} } }"
                );
    }

    @Test public void testErrorGitBug609() {
        addMockFile("$A/B.java","package p; public class B{}");
        helpTCText("A.java","package p; public class A implements Cloneable { private B b; A() { b = new B(); }}"
                ,"/A.java:1: error: cannot find symbol\n  symbol:   class B\n  location: class p.A",58
                ,"/A.java:1: error: cannot find symbol\n  symbol:   class B\n  location: class p.A",77
                );
    }

    @Test public void testJmlLabelExpression() {
        helpTCText("TestJava.java",
                """
                package tt;
                public class TestJava {
                  public int m1bad(boolean b, int k) {
                    int j = 0;
                    //@ ghost boolean bb = (\\forall int i; 0<=i && i <=4; 0!=(\\lbl LBL i));
                    return 1;
                  }
                }
                """
                ,"/TestJava.java:5: error: A JML label expression may not be within a quantified or set-comprehension expression",63
                );
    }

    @Test public void testKeywords() {
        helpTCText("TestJava.java",
                """
                package tt;
                public class TestJava {
                  //@ model public void m1bad(java.util.function.Function<Integer,Integer> f) ;
                }
                """
                );
    }

    @Test public void testBadEnum1() {
        addMockFile("$A/A.jml","public class A extends Enum<A> {}");
        helpTCText("A.java",
                """
                public enum A { X, Y, Z }
                """
                ,"/$A/A.jml:1: error: The type A in the specification matches a Java type with different modifiers: enum", 8
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 8
                );
    }

    @Test public void testBadEnum2() {
        addMockFile("$A/A.jml","public enum A { }");
        helpTCText("A.java",
                """
                public class A { }
                """
                ,"/$A/A.jml:1: error: The type A in the specification matches a Java type with different modifiers: enum", 8
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 8
                );
    }
    // FIXME - need tests that record has same fields and methods
    @Test public void testOKRecord1() {
        addMockFile("$A/A.jml","public record A() {}");
        helpTCText("A.java",
                """
                public record A() { }
                """
                );
    }

    @Test public void testBadRecord1() {
        addMockFile("$A/A.jml","public class A {}");
        helpTCText("A.java",
                """
                public record A() { }
                """
                ,"/$A/A.jml:1: error: The specification declaration must be a record, because the source/binary is", 8
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 8
                );
    }

    @Test public void testBadRecord2() {
        addMockFile("$A/A.jml","public record A() {}");
        helpTCText("A.java",
                """
                public class A { }
                """
                ,"/$A/A.jml:1: error: The specification declaration may not be a record, because the source/binary is not", 8
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 8
                );
    }

    @Test public void testBadSuper6() {
        expectedExit = 2;
        // Object.jml is not in its correct package on the specspath, so it is not found as a match to Object.java
        addMockFile("$A/java/lang/Object.jml","package java.lang; class Object extends java.util.ArrayList<Object> {}");
        helpTCText("Object.java",
                """
                package java.lang;
                class Object{ }
                """
                ,"/Object.java:1: error: package exists in another module: java.base", 1
                ,"/$A/java/lang/Object.jml: error: Parsing failed because there is an attempt to parse a spec file twice, likely indicating that there are two instances of a class, one binary and one in source: java.lang.Object", -1
                ,"/Object.java: error: Unrecoverable compilation problem", -1
                 );
    }

    @Test public void testBadSuper5() {
        expectedExit = 2;
        addMockFile("$A/java/lang/Object.jml","package java.lang; class Object extends java.util.ArrayList<Object> {}");
        helpTCText("Object.java",
                """
                package java.lang;
                class Object{ }
                """
                ,"/Object.java:1: error: package exists in another module: java.base", 1
                ,"/$A/java/lang/Object.jml: error: Parsing failed because there is an attempt to parse a spec file twice, likely indicating that there are two instances of a class, one binary and one in source: java.lang.Object", -1
                ,"/Object.java: error: Unrecoverable compilation problem", -1
                );
    }

    @Test public void testBadSuper4() {
        addMockFile("$A/A.jml","package java.lang; public class Object extends java.util.ArrayList<Object> {}");
        helpTCText("A.java",
                """
                package java.lang;
                public class Object{ }
                """
                ,"/A.java:1: error: package exists in another module: java.base", 1
                ,"/A.java:2: error: class Object is public, should be declared in a file named Object.java", 8
                );
    }

    @Test public void testOKSuper2() {
        addMockFile("$A/A.jml","public class A extends java.util.ArrayList<Object> {}");
        helpTCText("A.java",
                """
                public class A extends java.util.ArrayList<Object>{ }
                """
                );
    }

    @Test public void testBadSuper1() {
        addMockFile("$A/A.jml","public class A extends java.util.ArrayList<Object> {}");
        helpTCText("A.java",
                """
                public class A extends java.util.LinkedList<Object>{ }
                """
                ,"/$A/A.jml:1: error: The specification declaration must declare the same supertype as the source declaration: java.util.ArrayList<java.lang.Object> vs. java.util.LinkedList<java.lang.Object>", 43
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 44
                );
    }

    @Test public void testBadSuper2() {
        addMockFile("$A/A.jml","public class A extends java.util.ArrayList<Object> {}");
        helpTCText("A.java",
                """
                public class A{ }
                """
                ,"/$A/A.jml:1: error: The specification declaration must declare the same supertype as the source declaration: java.util.ArrayList<java.lang.Object> vs. java.lang.Object", 43
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 8
                );
    }

    @Test public void testBadSuper3() {
        addMockFile("$A/A.jml","public class A {}");
        helpTCText("A.java",
                """
                public class A extends java.util.LinkedList<Object>{ }
                """
                ,"/$A/A.jml:1: error: The specification declaration must declare the same supertype as the source declaration: java.util.LinkedList<java.lang.Object>", 8
                ,"/A.java:1: error: Associated declaration: /$A/A.jml:1:", 44
                );
    }

    @Test public void testBadImmutable1() {
        helpTCText("A.java",
                """
                /*@ immutable */ class B {}
                public class A extends B {}
                """
                ,"/A.java:2: error: A class with an immutable superclass must itself be immutable: A", 8
                );
    }

    @Test public void testBadImmutable2() {
        helpTCText("A.java",
                """
                /*@ immutable */ interface B {}
                public class A implements B {}
                """
                ,"/A.java:2: error: A type with an immutable interface must itself be immutable: A", 8
                );
    }

    @Test public void testBadNestedModel() {
        helpTCText("A.java",
                """
                //@ model public class A { model public static class B {}}
                """
                ,"/A.java:1: error: A model type may not contain model declarations: B in A", 48
                );
    }

    @Test public void testOKNestedModel1() {
        helpTCText("A.java",
                """
                //@ model public class A {  public static class B {}}
                """
                );
    }

    @Test public void testOKNestedModel2() {
        helpTCText("A.java",
                """
                public class A { /*@ model public static class B {} */ }
                """
                );
    }

    @Test public void testAbstractModel() {
        addOptions("--check"); // FIXME - these messages should apply to --esc as well
        helpTCText("A.java",
                """
                public class A {
                  //@ abstract static model int z;
                  //@ abstract final model int x = 9;
                  //@ abstract model int y;
                  //@ represents y = 100;
                }
                """
                ,"/A.java:5: error: An abstract model field may not have a represents clause", 18
                //   ,"/A.java:4: error: Associated declaration: /A.java:5:", 26
                ,"/A.java:2: error: a model field may not be both abstract and static", 33
                ,"/A.java:3: error: an abstract model field may not have an initializer", 36
                );
    }

    @Test public void testAbstractModel_esc() {
        addOptions("--esc"); // FIXME - these messages should apply to --esc as well
        helpTCText("A.java",
                """
                public class A {
                  //@ abstract static model int z;
                  //@ abstract final model int x = 9;
                  //@ abstract model int y;
                  //@ represents y = 100;
                }
                """
                ,"/A.java:5: error: An abstract model field may not have a represents clause", 18
                //  ,"/A.java:4: error: Associated declaration: /A.java:5:", 26
                ,"/A.java:2: error: a model field may not be both abstract and static", 33
                ,"/A.java:3: error: an abstract model field may not have an initializer", 36
                );
    }

    @Test public void testAbstractModel_rac() {
        addOptions("--rac"); // FIXME - these messages should apply to --esc as well
        helpTCText("A.java",
                """
                public class A {
                  //@ abstract static model int z;
                  //@ abstract final model int x = 9;
                  //@ abstract model int y;
                  //@ represents y = 100;
                }
                """
                ,"/A.java:5: error: An abstract model field may not have a represents clause", 18
                //   ,"/A.java:4: error: Associated declaration: /A.java:5:", 26
                ,"/A.java:2: error: a model field may not be both abstract and static", 33
                ,"/A.java:3: error: an abstract model field may not have an initializer", 36
                );
    }

    @Test public void testMissingModel() {
        helpTCText("A.java",
                """
                //@  public class A { }
                """
                ,"/A.java:1: error: A method or type declaration within a JML annotation must be model: A", 13
                );
    }

    /** Declarations in quantifiers may not have same names as other in-scope declarations */
    // TODO - would be nice if these pointed to associated declaration
    @Test public void testQuantifierIdents() {
        helpTCText("A.java",
                """
                public class A {
                  public void m(int i) {
                    int j = 0;
                    //@ assert (\\forall int i; \\forall int j; i != j);
                  }
                }
                """
                ,"/A.java:4: error: variable i is already defined in method m(int)", 29
                ,"/A.java:4: error: variable j is already defined in method m(int)", 44
                );
    }
    // TODO: Not sure if this testcase or the one above add any coverage
    @Test public void testQuantifierIdents2() {
        helpTCText("A.java",
                """
                public class A {
                  public void m() {
                    //@ assert (\\forall int i; \\forall int i; i == i);
                  }
                }
                """
                ,"/A.java:3: error: variable i is already defined in method m()", 44
                );
    }

    @Test public void testSpecCaseVisibility() {
        expectedExit = 0; // Only warnings
        helpTCText("TestJava.java",
                """
                package tt;
                public class TestJava {
                  //@ public behavior requires true;
                  public void m1p() {
                  }
                  //@ protected behavior requires true;
                  public void m1r() {
                  }
                  //@ behavior requires true;
                  public void m1k() {
                  }
                  //@ private behavior requires true;
                  public void m1v() {
                  }
                  //@ requires true;
                  public void m1() {
                  }
                  //@ public behavior requires true;
                  protected void m2p() {
                  }
                  //@ protected behavior requires true;
                  protected void m2r() {
                  }
                  //@ behavior requires true;
                  protected void m2k() {
                  }
                  //@ private behavior requires true;
                  protected void m2v() {
                  }
                  //@ requires true;
                  protected void m2() {
                  }
                  //@ public behavior requires true;
                  private void m3p() {
                  }
                  //@ protected behavior requires true;
                  private void m3r() {
                  }
                  //@ behavior requires true;
                  private void m3k() {
                  }
                  //@ private behavior requires true;
                  private void m3v() {
                  }
                  //@ requires true;
                  private void m3() {
                  }
                  //@ public behavior requires true;
                  void m4p() {
                  }
                  //@ protected behavior requires true;
                  void m4r() {
                  }
                  //@ behavior requires true;
                  void m4k() {
                  }
                  //@ private behavior requires true;
                  void m4v() {
                  }
                  //@ requires true;
                  void m4() {
                  }
                }
                """
                ,"/TestJava.java:18: warning: [jml-lint] There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:33: warning: [jml-lint] There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:36: warning: [jml-lint] There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:39: warning: [jml-lint] There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:48: warning: [jml-lint] There is no point to a specification case having more visibility than its method",7
                ,"/TestJava.java:51: warning: [jml-lint] There is no point to a specification case having more visibility than its method",7
                );
    }
    
    @Test public void clauseNames() {
        helpTCText("TestJava.java",
                """
                public class TestJava {
                    //@ axiom A: true;
                    //@ public invariant B: true;
                    //@ ghost public int g; // NO LABEL
                    //@ model public int m; // NO LABEL
                    public int f; //@ in m; // NO LABEL
                    public TestJava t; //@ maps t.f \\into m; // NO LABEL
                    //@ represents C: m = 0;
                    //@ public initially E: true;
                    //@ public constraint F: true;
                    //@ public readable f if true;
                    //@ public writable f if true;

                    //@ public normal_behavior G:
                    //@   requires H: true;
                    //@   old int z = 0; // NO LABEL
                    //@   assignable N: \\nothing;
                    //@   accessible  R: \\nothing;
                    //@   ensures I: true;
                    //@   measured_by T: 0;
                    //@   callable C: \\nothing;
                    //@   duration D: 0;
                    //@   working_space W: 0;
                    //@ also public exceptional_behavior E:
                    //@   requires F: false;
                    //@ also public behavior B:
                    //@   ensures Q: true;
                    //@ also implies_that
                    //@    public normal_behavior YY:
                    //@      requires ZZ: true;
                    //@ also for_example
                    //@       requires UUU: true;
                    public void m() {
                        //@ assert A: true;
                        //@ assume B: true;
                        //@ check C: true;
                        //@ set S: f = 0;
                        //@ ghost int yy = 0; // NO LABEL

                        //@ maintaining X: true;
                        //@ loop_modifies Y: \\nothing;
                        //@ decreases Z: 0;
                        while (true) { break; }

                        //@ refining
                        //@  normal_behavior A:
                        //@    requires B: true;
                        //@ also exceptional_behavior Q:
                        //@    requires B: true;
                        //@ also behavior R:
                        //@    requires B: true;
                        {}
                    }
                }
                """
                        // FIXME - also model programs and various additional statements
                        // FIXME - additional kinds of clauses in block contracts
        );
       
    }

    @Test public void testCastingExplicit() {
        helpTCText("TestJava.java",
                """
                package tt;
                public class TestJava {
                  //@ ghost \\string s = (\\string)""; // OK String -> \\string
                  //@ ghost String ss = (String)s; // OK \\string -> String
                  //@ ghost \\real r = 0.0;        // OK numeric -> \\real
                  //@ ghost double d = (double)r;  // OK \\real -> numeric
                  //@ ghost \\real rr = (\\real)0.0; // OK numeric -> \\real
                  //@ ghost \\bigint k = 0L;   // OK integral -> \\bigint
                  //@ ghost long kk = (long)k; // OK \\bigint -> integral
                  //@ ghost \\real rrr = (\\real)"abc"; // ERROR String -> \\real
                  //@ ghost String sss = (String)rr; // ERROR \\real -> String
                  //@ ghost \\bigint kkk = (\\bigint)"xyz"; // ERROR String -> \\bigint
                  //@ ghost \\bigint kkkk = (\\bigint)rr; // OK \\real -> \\bigint
                  //@ ghost \\bigint k3 = (\\bigint)0; // OK integral -> \\bigint
                  //@ ghost \\real rrrr = (\\real)k; // OK \\bigint -> \\real
                  //@ ghost \\string s3 = (\\string)k; // ERROR \\bigint -> \\string
                  //@ ghost \\bigint k4 = (\\bigint)s; // ERROR \\string -> \\bigint
                }
                """
                ,"/TestJava.java:10: error: A java.lang.String may not be cast to a \\real",32
                ,"/TestJava.java:11: error: A \\real may not be cast to a java.lang.String",34
                ,"/TestJava.java:12: error: A java.lang.String may not be cast to a \\bigint",36
                ,"/TestJava.java:16: error: A \\bigint may not be cast to a \\string",35
                ,"/TestJava.java:17: error: A \\string may not be cast to a \\bigint",35
                );
    }

    @Test public void testCastingImplicit() {
        helpTCText("TestJava.java",
                """
                package tt;
                public class TestJava {
                  //@ ghost \\string s = "";            // OK    String -> \string
                  //@ ghost String ss = s;              // ERROR \\string -> String
                  //@ ghost \\real r = 0.0;             // OK numeric -> \\real
                  //@ ghost double d = r;               // ERROR \\real -> numeric
                  //@ ghost \\bigint k = 0L;            // OK integral -> \\bigint
                  //@ ghost long jj = k;                // ERROR \\bigint -> integral
                  //@ ghost \\real rrr = "abc";         // ERROR String -> \\real
                  //@ ghost \\bigint kk = "abc";        // ERROR String -> \\bigint
                  //@ ghost \\real rra = s;             // ERROR \\string -> \\real
                  //@ ghost \\bigint ka = s;            // ERROR \\string -> \\bigint
                  //@ ghost String sss = r;             // ERROR \\real -> String
                  //@ ghost \\string ssss = r;          // ERROR \\real -> \\string
                  //@ ghost \\bigint kkkk = r;          // ERROR \\real -> \\bigint
                  //@ ghost \\real rrrr = k;            // OK \\bigint -> \\real
                  //@ ghost \\real rrra = "";           // ERROR String -> \\real
                  //@ ghost \\real rrrb = s;            // ERROR \\string -> \\real
                }  // FIXME -  make all messages use backslash names
                """
                ,"/TestJava.java:4: error: incompatible types: \\string cannot be converted to java.lang.String",25
                ,"/TestJava.java:6: error: incompatible types: \\real cannot be converted to double",24
                ,"/TestJava.java:8: error: incompatible types: \\bigint cannot be converted to long",23
                ,"/TestJava.java:9: error: incompatible types: java.lang.String cannot be converted to \\real", 25
                ,"/TestJava.java:10: error: incompatible types: java.lang.String cannot be converted to \\bigint",26
                ,"/TestJava.java:11: error: incompatible types: \\string cannot be converted to \\real",25
                ,"/TestJava.java:12: error: incompatible types: \\string cannot be converted to \\bigint",26
                ,"/TestJava.java:13: error: incompatible types: \\real cannot be converted to java.lang.String",26
                ,"/TestJava.java:14: error: incompatible types: \\real cannot be converted to \\string",28
                ,"/TestJava.java:15: error: incompatible types: \\real cannot be converted to \\bigint",28
                ,"/TestJava.java:17: error: incompatible types: java.lang.String cannot be converted to \\real",26
                ,"/TestJava.java:18: error: incompatible types: \\string cannot be converted to \\real",26
                );
    }

    @Test
    public void testBRCLocation() {
        expectedExit = 1;
        helpTCText("TestJava.java",
                """
                public class TestJava {
                  //@ public normal_behavior
                  //@   returns true;
                  //@   continues true;
                  //@   breaks true;
                  public static void m1(Object[] a) {
                    //@ refining
                    //@   returns true;
                    //@   continues true;
                    //@   breaks true;
                    //@   {| returns true; |}
                    {}
                  }
                }
                """
                ,"/TestJava.java:3: error: A returns clause may only be in a refining specification", 9
                ,"/TestJava.java:4: error: A continues clause may only be in a refining specification", 9
                ,"/TestJava.java:5: error: A breaks clause may only be in a refining specification", 9
                );
        
    }

    @Test
    public void testBRC() {
        expectedExit = 1;
        helpTCText("TestJava.java",
                """
                public class TestJava {
                  public static void m1() {
                    //@ refining
                    //@   returns 0;
                    //@   continues "";
                    //@   breaks true;
                    {}
                  }
                }
                """
                ,"/TestJava.java:4: error: incompatible types: int cannot be converted to boolean", 19
                ,"/TestJava.java:5: error: incompatible types: java.lang.String cannot be converted to boolean", 21
                );
        
    }
    
    @Test
    public void inlineNeedsFinal() {
        expectedExit = 0;
        helpTCText("Test.java",
                """
                public class Test {
                    //@ inline
                    public void m() {}
                }
                """
                ,"/Test.java:2: warning: [jml-lint] Inlined methods should be final since overriding methods will be ignored: m", 9
        );
    }

    @Test
    public void inlineNeedsFinala() {
        helpTCText("TestJava.java",
                """
                public class TestJava {
                    //@ inline final
                    public void m() {}
                }
                """
        );
    }

    @Test
    public void inlineNeedsFinalb() {
        helpTCText("TestJava.java",
                """
                public class TestJava {
                    //@ inline
                    final public void m() {}
                }
                """
        );
    }

    @Test
    public void jmlFinalNotInherited() {
        helpTCText("Test.java",
                """
                public class Test {
                    //@ final
                    public void m() {}
                }
                class TFI extends Test {
                    public void m() {}
                }
                """
                
                ,"/Test.java:6: error: m() in TFI cannot override m() in Test\n"
                        + "  overridden method is final", 17
        );
    }
    
    @Test
    public void parseOnlyA() {
        addOptions("--parse");
        helpTCText("Test.java",
            """
            public class Test {
                public void m() {
                    q = 0; // Type error, but we are only parsing
                }
            }
            """
        );
    }
    
    @Test
    public void parseOnlyB() {
        addOptions("--parse");
        helpTCText("Test.java",
            """
            public class Test {
                public void m() {
                    boolean q = 0;  // Type error, but we are only parsing
                }
            }
            """
        );
    }
    
    @Test
    public void parseOnlyC() {
        addOptions("--parse");
        helpTCText("Test.java",
            """
            public class Test {
                public void m() {
                    q = ; // Parse error
                }
            }
            """
                ,"/Test.java:3: error: illegal start of expression", 13
                ,"/Test.java:3: error: ';' expected", 14
        );
    }
}
