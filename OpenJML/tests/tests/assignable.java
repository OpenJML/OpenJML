package tests;

public class assignable extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

    public void testAssignableNothing() {
        helpTC(" class A { int k; boolean b; \n//@ assignable \\nothing;\n void m(){} }");
    }

    public void testAssignableEverything() {
        helpTC(" class A { int k; boolean b; \n//@ assignable \\everything;\n void m(){} }");
    }

    public void testAssignableIdent() {
        helpTC(" class A { int k; boolean b; \n//@ assignable k;\n void m(){} }");
    }

    public void testAssignableBadIdent() {
        helpTC(" class A { int k; boolean b; \n//@ assignable m;\n void m(){} }",
                "/TEST.java:2: cannot find symbol\nsymbol  : variable m\nlocation: class A",16);
    }

    public void testAssignableField() {
        helpTC(" class A { int k; boolean b; Object o; \n//@ assignable A.k;\n void m(){} }"
                ,"/TEST.java:2: non-static variable k cannot be referenced from a static context",16
                );
    }

    public void testAssignableField1() {
        helpTC(" class A { int k; boolean b; Object o; \n//@ assignable o.*;\n void m(){} }");
    }

    public void testAssignableField2() {
        helpTC(" class A { class B { int p; } int k; boolean b; Object o;  B bb; \n//@ assignable bb.p;\n void m(){} }");
    }
    
    public void testAssignableField3() {
        helpTC(" class A { class B { int p; } int k; boolean b; Object o;  B bb; \n//@ assignable bb.*;\n void m(){} }");
    }

    public void testAssignableField4() {
        helpTC(" class A { int k; boolean b; Object o; \n//@ assignable A.*;\n void m(){} }");
    }

    
    public void testAssignableArray() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable k[0],k[*],k[2 .. 3], k[3 ..], k[3 .. *];\n void m(){} }");
    }

    // FIXME- needs fixing in the scanner
//    public void testAssignableArray1() {
//        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable k[2.. 3], k[3..], k[3.. *];\n void m(){} }");
//    }

    public void testAssignableArray2() {
        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable o[0],o[*],o[2 .. 3], o[3 ..], o[3 .. *];\n void m(){} }");
    }

    // FIXME- needs fixing in the scanner
//    public void testAssignableArray3() {
//        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable o[2.. 3], o[3..], o[3.. *];\n void m(){} }");
//    }
    
    
// FIXME - this needs fixing in the scanner
//    public void testAssignableDots() {
//        helpTC(" class A { int[] k; boolean b; Object[] o; \n//@ assignable o[2..3], o[2..*];\n void m(){} }");
//    }

    public void testAssignableArray4() {
        helpTCF("A.java","public class A { int[] k; boolean b; Object[] o; \n//@ assignable k[true],k[true .. false], k[false ..], k[false .. *];\n void m() {} }"
                ,"/A.java:2: incompatible types\nfound   : boolean\nrequired: int",18
                ,"/A.java:2: incompatible types\nfound   : boolean\nrequired: int",26
                ,"/A.java:2: incompatible types\nfound   : boolean\nrequired: int",34
                ,"/A.java:2: incompatible types\nfound   : boolean\nrequired: int",44
                ,"/A.java:2: incompatible types\nfound   : boolean\nrequired: int",57
                );
    }

    public void testAssignableArray5() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable k[b];\n void m(boolean b) {} }"
                ,"/A.java:2: incompatible types\nfound   : boolean\nrequired: int",18
                );
    }

    public void testAssignableThis() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this.k, this.*;\n void m(boolean b) {} }"
                );
    }

    public void testAssignableThis2() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this.x;\n void m(boolean b) {} }"
                ,"/A.java:2: cannot find symbol\nsymbol  : variable x\nlocation: class A",16
		);
    }

    public void testAssignableSuper() {
        helpTCF("A.java","public class A extends B { int[] k; Object b; Object[] o; \n//@ assignable super.kk, super.*;\n void m(boolean b) {} }  class B{ int kk; }"
                );
    }

    public void testAssignableSuper2() {
        helpTCF("A.java","public class A extends B { int[] k; Object b; Object[] o; \n//@ assignable super.b, super.x;\n void m(boolean b) {} }  class B{ int kk; }"
                ,"/A.java:2: cannot find symbol\nsymbol  : variable b\nlocation: class B",16
                ,"/A.java:2: cannot find symbol\nsymbol  : variable x\nlocation: class B",25
                );
    }

    public void testAssignableBad() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this, super;\n void m(boolean b) {} }"
                ,"/A.java:2: A this or super token must be followed by a field selection",16
                ,"/A.java:2: A this or super token must be followed by a field selection",22
                );
    }

    public void testAssignableBad2() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable k[, k[*, k[i, k[], b., this., super.;\n void m(boolean b) {} }"
                ,"/A.java:2: illegal start of expression",18
                ,"/A.java:2: An invalid expression or succeeding token near here",18
                ,"/A.java:2: Expected a right bracket after the star",23
                ,"/A.java:2: An invalid expression or succeeding token near here",28
                ,"/A.java:2: illegal start of expression",32
                ,"/A.java:2: Expected an identifier or star after the dot",37
                ,"/A.java:2: Expected an identifier or star after the dot",44
                ,"/A.java:2: A this or super token must be followed by a field selection",39
                ,"/A.java:2: Expected an identifier or star after the dot",52
                ,"/A.java:2: A this or super token must be followed by a field selection",46
                );
    }

    public void testAssignableBad2a() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable super.;\n void m(boolean b) {} }"
                ,"/A.java:2: Expected an identifier or star after the dot",22
                ,"/A.java:2: A this or super token must be followed by a field selection",16
                );
    }

    public void testAssignableBad2b() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this.;\n void m(boolean b) {} }"
                ,"/A.java:2: Expected an identifier or star after the dot",21
                ,"/A.java:2: A this or super token must be followed by a field selection",16
                );
    }

    public void testAssignableBad2c() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable super;\n void m(boolean b) {} }"
                ,"/A.java:2: A this or super token must be followed by a field selection",16
                );
    }

    public void testAssignableBad2d() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable this;\n void m(boolean b) {} }"
                ,"/A.java:2: A this or super token must be followed by a field selection",16
                );
    }

    public void testAssignableBad3() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable k b, this.;\n void m(boolean b) {} }"
                ,"/A.java:2: Missing comma or otherwise ill-formed type name",18
                ,"/A.java:2: Expected an identifier or star after the dot",26
                ,"/A.java:2: A this or super token must be followed by a field selection",21
                );
    }
    
    public void testAssignableBad4() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable ;\n void m(boolean b) {} }"
                ,"/A.java:2: Use \\nothing to denote an empty list of locations in an assignable clause",16
                );
    }

    public void testAssignableBad5() {
        helpTCF("A.java","public class A { int[] k; Object b; Object[] o; \n//@ assignable .;\n void m(boolean b) {} }"
                ,"/A.java:2: Incorrectly formed or terminated store-reference near here",16
                ,"/A.java:2: Use \\nothing to denote an empty list of locations in an assignable clause",17
                );
    }

    public void testAssignableBad6() {
        helpTCF("A.java","public class A { int k;  \n//@ assignable k[*], this.*.x;\n void m(boolean b) {} }"
                ,"/A.java:2: Further selection is not permitted after a wild-card field",28
                ,"/A.java:2: The expression preceding the array element selection does not have array type: int",16
                );
    }

    public void testAssignableArray9() {
        helpTCF("A.java","public class A { B[] o; \n//@ assignable o[*].kk;\n void m(boolean b) {} }  class B{ int kk; }"
                );
    }



}

