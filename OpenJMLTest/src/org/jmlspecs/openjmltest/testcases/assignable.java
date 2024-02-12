package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

/** Tests the parsing and type-checking of assignable clauses */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class assignable extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    @Test
    public void testAssignableNothing() {
        helpTC(" class A { int k; boolean b; \n//@ assignable \\nothing;\n void m(){} }");
    }

    @Test
    public void testAssignableEverything() {
        helpTC(" class A { int k; boolean b; \n//@ assignable \\everything;\n void m(){} }");
    }

    @Test
    public void testAssignableIdent() {
        helpTC(" class A { int k; boolean b; \n//@ assignable k;\n void m(){} }");
    }

    @Test
    public void testAssignableBadIdent() {
        helpTC(" class A { int k; boolean b; \n//@ assignable m;\n void m(){} }",
                "/TEST.java:2: error: cannot find symbol\n  symbol:   variable m\n  location: class A",16);
    }

    @Test
    public void testAssignableField() {
        helpTC(" class A { int k; boolean b; Object o; \n//@ assignable A.k;\n void m(){} }"
                ,"/TEST.java:2: error: non-static variable k cannot be referenced from a static context",17
                );
    }

    @Test
    public void testAssignableField1() {
    	main.addOptions("-progress");
        helpTC(" class A { int k; boolean b; Object o; \n//@ assignable o.*;\n void m(){} }");
    }

    @Test
    public void testAssignableField2() {
        helpTC(" class A { class B { int p; } int k; boolean b; Object o;  B bb; \n//@ assignable bb.p;\n void m(){} }");
    }
    
    @Test
    public void testAssignableField3() {
        helpTC(" class A { class B { int p; } int k; boolean b; Object o;  B bb; \n//@ assignable bb.*;\n void m(){} }");
    }

    @Test
    public void testAssignableField4() {
        helpTC(" class A { int k; boolean b; Object o; \n//@ assignable A.*;\n void m(){} }");
    }

    @Test
    public void testAssignableArray() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable k[0],k[*],k[2 .. 3], k[3 ..], k[3 .. *];\n void m(){} }");
    }

    @Test
    public void testAssignableArray1() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable k[2.. 3], k[3..], k[3.. *];\n void m(){} }");
    }

    @Test
    public void testAssignableArray2() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable o[0],o[*],o[2 .. 3], o[3 ..], o[3 .. *];\n void m(){} }");
    }

    @Test
    public void testAssignableArray3() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable o[2.. 3], o[3..], o[3.. *];\n void m(){} }");
    }
    
    @Test
    public void testAssignableArray3a() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable o[(i-1)..(i+1)], o[(i+1)..], o[(i+1).. *];\n void m(int i){} }");
    }
    
    @Test
    public void testAssignableDots() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable o[2..3], o[2..*];\n void m(){} }");
    }

    @Test
    public void testAssignableArray4() {
        helpTCF("A.java","public class A { int[] k; boolean b; Object[] o; \n//@ assignable k[true],k[true .. false], k[false ..], k[false .. *];\n void m() {} }"
                ,"/A.java:2: error: Expected an integral type as an index, not boolean",18
                ,"/A.java:2: error: Expected an integral type, not boolean",26
                ,"/A.java:2: error: Expected an integral type, not boolean",34
                ,"/A.java:2: error: Expected an integral type, not boolean",44
                ,"/A.java:2: error: Expected an integral type, not boolean",57
                );
    }

    @Test
    public void testAssignableArray5() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable k[b];\n void m(boolean b) {} }"
                ,"/A.java:2: error: Expected an integral type as an index, not boolean",18
                );
    }

    @Test
    public void testAssignableThis() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this.k, this.*;\n void m(boolean b) {} }"
                );
    }

    @Test
    public void testAssignableThis2() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this.x;\n void m(boolean b) {} }"
                ,"/A.java:2: error: cannot find symbol\n  symbol: variable x",20
		);
    }

    @Test
    public void testAssignableSuper() {
        helpTCF("A.java","public class A extends B { int[] k; Object b; Object[] o; \n//@ assignable super.kk, super.*;\n void m(boolean b) {} }  class B{ int kk; }"
                );
    }

    @Test
    public void testAssignableSuper2() {
        helpTCF("A.java","public class A extends B { int[] k; Object b; Object[] o; \n//@ assignable super.b, super.x;\n void m(boolean b) {} }  class B{ int kk; }"
                ,"/A.java:2: error: cannot find symbol\n  symbol: variable b",21
                ,"/A.java:2: error: cannot find symbol\n  symbol: variable x",30
                );
    }

    @Test
    public void testAssignableBad() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this, super;\n void m(boolean b) {} }"
                ,"/A.java:2: error: A this or super token must be followed by a field selection",16
                ,"/A.java:2: error: A this or super token must be followed by a field selection",22
                );
    }

    @Test
    public void testAssignableBad2() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable k[, k[*, k[i, k[], b., this., super.;\n void m(boolean b) {} }"
                ,"/A.java:2: error: illegal start of expression",18
                ,"/A.java:2: error: ']' expected",19
                ,"/A.java:2: error: Missing comma or right parenthesis or otherwise ill-formed expression", 20
                ,"/A.java:2: error: ']' expected",23
                ,"/A.java:2: error: ']' expected",28
                ,"/A.java:2: error: '.class' expected",33
                ,"/A.java:2: error: <identifier> expected",37
                ,"/A.java:2: error: Expected an identifier or star after the dot",43
                ,"/A.java:2: error: Expected an identifier or star after the dot",51
                );
    }

    @Test
    public void testAssignableBad2a() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable super.;\n void m(boolean b) {} }"
                ,"/A.java:2: error: Expected an identifier or star after the dot",21
                );
    }

    @Test
    public void testAssignableBad2b() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this.;\n void m(boolean b) {} }"
                ,"/A.java:2: error: Expected an identifier or star after the dot",20
                );
    }

    @Test
    public void testAssignableBad2c() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable super;\n void m(boolean b) {} }"
                ,"/A.java:2: error: A this or super token must be followed by a field selection",16
                );
    }

    @Test
    public void testAssignableBad2d() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this;\n void m(boolean b) {} }"
                ,"/A.java:2: error: A this or super token must be followed by a field selection",16
                );
    }

    @Test
    public void testAssignableBad3() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable k b, this.;\n void m(boolean b) {} }"
                ,"/A.java:2: error: Missing comma or right parenthesis or otherwise ill-formed expression",18
                ,"/A.java:2: error: Expected an identifier or star after the dot",25
                );
    }
    
    @Test
    public void testAssignableBad4() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable ;\n void m(boolean b) {} }"
                ,"/A.java:2: error: Use \\nothing to denote an empty list of locations in an assignable clause",16
                );
    }

    @Test
    public void testAssignableBad5() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable .;\n void m(boolean b) {} }"
                ,"/A.java:2: error: illegal start of expression",16
                ,"/A.java:2: error: Use \\nothing to denote an empty list of locations in an assignable clause",17
                );
    }

    @Test
    public void testAssignableBad6() {
        helpTCF("A.java","public class A {  \n//@ assignable  this.*.x;\n void m(boolean b) {} }"
                ,"/A.java:2: error: Further selection is not permitted after a wild-card field",23
                );
    }

    @Test
    public void testAssignableBad7() {
        helpTCF("A.java","public class A { int k;  \n//@ assignable k[*];\n void m(){} }"
                ,"/A.java:2: error: array required, but int found",16
                );
    }

    @Test
    public void testAssignableBad8() {
        helpTCF("A.java","public class A { int k;  \n//@ assignable k[*];\n }"
                ,"/A.java:2: error: Method specifications without a following method declaration",5
                );
    }

    @Test
    public void testAssignableArray9() {
        helpTCF("A.java","public class A { B[] o; \n//@ assignable o[*].kk;\n void m(boolean b) {} }  class B{ int kk; }"
                );
    }

    @Test
    public void testAssignableNoSemi() {
        helpTCF("A.java","public class A { B[] o; \n//@ assignable o\n void m(boolean b) {} }  class B{ int kk; }"
                ,"/A.java:2: error: Invalid expression or missing semicolon here",17
                );
    }

    @Test
    public void testAssignableConstructor1() {
        helpTCF("A.java","public class A { \n"
                +"  private int i; static private int j;\n"
                +"  //@ assignable j;\n"
                +"  public A() { j = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new A(); }\n"
                +"}"
                ,"/A.java:3: error: An identifier with private visibility may not be used in a assignable clause with public visibility",18
                );
    }

    @Test
    public void testAssignableConstructor2() {
        helpTCF("A.java","public class A { \n"
                +"  private int i;\n"
                +"  //@ assignable \\nothing;\n"
                +"  public A() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new A(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor3() {
        helpTCF("A.java","public class A { \n"
                +"  private int i;\n"
                +"  \n" // default assignable with no spec case
                +"  public A() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new A(); }\n"
                +"}"
                );
    }

    @Test
    public void testAssignableConstructor4() {
        helpTCF("A.java","public class A { \n"
                +"  private int i;\n"
                +"  //@ requires true; \n" // default assignable
                +"  public A() { i = 0; }\n"
                +"  //@ assignable \\everything;\n"
                +"  public static void m() { new A(); }\n"
                +"}"
                );
    }

    @Test
    public void testAccessibleIdent() {
        helpTC(" class A { int k; boolean b; \n//@ accessible k;\n void m(){} }");
    }

    @Test
    public void testAccessibleBadIdent() {
        helpTC(" class A { int k; boolean b; \n//@ accessible m;\n void m(){} }",
                "/TEST.java:2: error: cannot find symbol\n  symbol:   variable m\n  location: class A",16);
    }

    @Test
    public void testCapturesIdent() {
        helpTC(" class A { int k; boolean b; \n//@ captures k;\n void m(){} }");
    }

    @Test
    public void testCapturesBadIdent() {
        helpTC(" class A { int k; boolean b; \n//@ captures m;\n void m(){} }",
                "/TEST.java:2: error: cannot find symbol\n  symbol:   variable m\n  location: class A",14);
    }
    
}

