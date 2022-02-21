package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class namelookup extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }
    
    @Test
    public void testLookup() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   //@ invariant k;\n" +
                "   //@ requires k;\n" +
                "   void m(double k) {}\n" +
                "}"
        ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",18
        ,"/A.java:3: error: incompatible types: double cannot be converted to boolean",17
        );
    }

    @Test
    public void testLookup2() {
        helpTCF("A.java",
                " public class A { int k; float d; \n" +
                "   //@ constraint \\old(k); constraint \\old(d);\n" + // ERRORS int, float to boolean
                "   void m(double d) {\n" +
                "        //@ assert k;\n" +          // ERROR - int to boolean
                "        double k;\n" +
                "        //@ assert k;\n" +          // ERROR - double to boolean
                "        //@ assert \\old(k);\n" +   // ERROR - int to boolean
                "        //@ assert \\old(d);\n" +   // ERROR - double to boolean // pre-state includes formals
                "   }\n" +
                "}"
        ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",23
        ,"/A.java:2: error: incompatible types: float cannot be converted to boolean",43
        ,"/A.java:4: error: incompatible types: int cannot be converted to boolean",20
        ,"/A.java:6: error: incompatible types: double cannot be converted to boolean",20
        ,"/A.java:7: error: incompatible types: int cannot be converted to boolean",24
        ,"/A.java:8: error: incompatible types: double cannot be converted to boolean",24
        );
    }

    @Test
    public void testLookup3() {
        helpTCF("A.java",
                " public class A { int k; Object o; \n" +
                "   void m() {\n" +
                "      //@ ghost Object k;\n" +
                "      boolean b = k;\n" +  // ERROR - k is Java variable with int type
                "      //@ assert k == 1;\n" + // ERROR - k is Object
                "      //@ assert k == null;\n" + // OK
                "      boolean bb = k;\n" + // ERROR - k is int
                "      boolean bbb = k == 0;\n" +  // OK
                "   }\n" +
                "}"
        ,"/A.java:4: error: incompatible types: int cannot be converted to boolean",19
        ,"/A.java:5: error: bad operand types for binary operator '=='\n"
        		+ "  first type:  java.lang.Object\n"
        		+ "  second type: int",20
        ,"/A.java:7: error: incompatible types: int cannot be converted to boolean",20
        );
    }

    @Test
    public void testDupField() {
        helpTCF("A.java",
                " class A { //@ ghost int k;  \n" +
                        "   //@ ghost double k;\n" +
                        "   int m;\n" +
                        "   int m;\n" +
                "}"
                ,"/A.java:2: error: variable k is already defined in class A",21
                ,"/A.java:4: error: variable m is already defined in class A",8
        );
    }

    @Test
    public void testDupField1() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   double k;\n" +
                "   void m(double k) {}\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: error: This specification declaration of field A.k has the same name as a previous field declaration",11
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",16
        ,"/$A/A.jml:3: error: The specification of the method A.m(double) must not have a body",21
        );
    }

    @Test
    public void testDupField1a() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   int k;\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "}"
        ,"/$A/A.jml:2: error: This specification declaration of field A.k has the same name as a previous field declaration",8
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",16
        );
    }

    @Test
    public void testDupField1b() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k);\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: error: This JML field declaration conflicts with an existing field with the same name: A.k",21
        ,"/A.java:1: error: Associated declaration: /$A/A.jml:2:",16
        );
    }

    @Test
    public void testDupField1c() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   int k;\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: error: This specification declaration of field A.k has the same name as a previous field declaration",8
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",16
        );
    }

    @Test
    public void testDupField2() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k) {}\n" +
                "}"
                ,"/A.java:2: error: variable k is already defined in class A",21
                );
    }

    @Test
    public void testDupVar() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   void m(double d) {\n" +
                "      int d;\n" +
                "   }\n" +
                "}",
        "/A.java:3: error: variable d is already defined in method m(double)",11);
    }

    @Test
    public void testDupVar2() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   void m(double d) {\n" +
                "      //@ ghost int d;\n" +
                "   }\n" +
                "}",
        "/A.java:3: error: variable d is already defined in method m(double)",21);
    }

    @Test
    public void testGhostField() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ ghost double k;\n" +
                "   void m() {\n" +
                "      boolean kk = k;\n" + // ERROR - no symbol k
                "      //@ assert k;\n" + // ERROR - double to boolean
                "   }\n" +
                "}",
        "/A.java:4: error: cannot find symbol\n"
        + "  symbol:   variable k\n"
        + "  location: class A", 20,
        "/A.java:5: error: incompatible types: double cannot be converted to boolean", 18
        );
    }

    @Test
    public void testModelField() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ model double k;\n" +
                "   void m() {\n" +
                "      boolean kk = k;\n" + // ERROR - no symbol k
                "      //@ assert k;\n" +  // ERROR - double to boolean
                "   }\n" +
                "}",
        "/A.java:4: error: cannot find symbol\n  symbol:   variable k\n  location: class A", 20,
        "/A.java:5: error: incompatible types: double cannot be converted to boolean",18);
    }

    @Test
    public void testModelMethod() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ model pure double k() { return 0; }\n" +
                "   void m() {\n" +
                "      boolean kk = k();\n" +
                "      //@ assert k();\n" +
                "   }\n" +
                "}",
        "/A.java:4: error: cannot find symbol\n  symbol:   method k()\n  location: class A", 20,
        "/A.java:5: error: incompatible types: double cannot be converted to boolean",19);
    }

    @Test
    public void testModelMethod2() {
        helpTCF("A.java",
                " class A {   int k() { return 0; }\n" +
                "   //@ model double k() { return 1; }\n" + // ERROR - duplicate
                "   void m() {\n" +
                "      boolean kk = k();\n" +
                "   }\n" +
                "}"
		        ,"/A.java:2: error: method k() is already defined in class A",21
		        ,"/A.java:4: error: incompatible types: int cannot be converted to boolean", 21
        );
    }

    @Test
    public void testModelMethod3() {
        helpTCF("A.java",
                " class A { /*@ pure*/  int k(int i) { return 0; }\n" +
                "   //@ model pure double k(boolean d) { return 0; }\n" +
                "   //@ requires k(true); \n" + // ERROR - double to boolean
                "   //@ requires k(0); \n" + // ERROR - int to boolean
                "   void m() {\n" +
                "   }\n" +
                "}",
        "/A.java:3: error: incompatible types: double cannot be converted to boolean", 18,
        "/A.java:4: error: incompatible types: int cannot be converted to boolean",18);
    }

    @Test
    public void testModelMethod4() {
        helpTCF("A.java",
                " class A {   static /*@pure*/int k(int i) { return 0; }\n" +
                "   static class B {\n" +
                "      //@ model pure static double k(int i) { return 0; }\n" +
                "      boolean b = k(0);\n" +  // TYPE ERROR
                "      //@ requires k(0); \n" +  // TYPE ERROR
                "      void m() {\n" +
                "         boolean kk = k(0);\n" +  // TYPE ERROR
                "         //@ assume k(0);\n" +  // TYPE ERROR
                "      }\n" +
                "   }\n" +
                "}"
        ,"/A.java:4: error: incompatible types: int cannot be converted to boolean", 20
        ,"/A.java:5: error: incompatible types: double cannot be converted to boolean", 21
        ,"/A.java:7: error: incompatible types: int cannot be converted to boolean", 24
        ,"/A.java:8: error: incompatible types: double cannot be converted to boolean", 22
        );
    }

    @Test
    public void testModelMethod5() {
        helpTCF("A.java",
                " class A {   \n" +
                "      //@ model pure static double k(int i);\n" +
                "      //@ requires k(0); \n" + // TYPE ERROR
                "      void m() {\n" +
                "         //@ assume k(0);\n" + // TYPE ERROR
                "      }\n" +
                "}"
                ,"/A.java:3: error: incompatible types: double cannot be converted to boolean", 21
                ,"/A.java:5: error: incompatible types: double cannot be converted to boolean", 22
        );
    }

    @Test
    public void testModelClass() {
        helpTCF("A.java",
                " public class A {   \n" +
                "   static class AA {\n" +
                "      //@ model static class B { static double i; }  \n" +
                "      B b;\n" +
                "      //@ ghost B bb;\n" +
                "      void m() {\n" +
                "         boolean kk = B.i;\n" +  // ERROR - int to boolean (top-level B)
                "         //@ assert B.i;\n" + // ERROR - double to boolean (A.AA.B)
                "      }\n" +
                "   }\n" +
                "}\n" +
                " class B { static int i; }  \n" +
                ""
        ,"/A.java:7: error: incompatible types: int cannot be converted to boolean",24 
        ,"/A.java:8: error: incompatible types: double cannot be converted to boolean",22
        );
    }
 
    @Test
    public void testModelClass2() {
        helpTCF("A.java",
                " class AXYZ {   \n" +
                "   static class AAXYZ {\n" +
                "      //@ model static class B { static double i; }  \n" +
                "      B bxyz;\n" +  // ERROR - no B
                "      //@ ghost B bb;\n" + // OK - A.AA.B
                "      void mxyz() {\n" +
                "         boolean kk = B.i;\n" + // ERROR
                "         //@ assert B.i;\n" +   // ERROR - found B, B.i is wrong type
                "      }\n" +
                "   }\n" +
                "}\n" +
                ""
        ,"/A.java:4: error: cannot find symbol\n  symbol:   class B\n  location: class AXYZ.AAXYZ",7
        ,"/A.java:7: error: cannot find symbol\n  symbol:   variable B\n  location: class AXYZ.AAXYZ",23
        ,"/A.java:8: error: incompatible types: double cannot be converted to boolean",22
            );
    }

    @Test
    public void testModelClass3() {
        addMockFile("$A/A.jml",
                "public class A {   \n" +
                "   static class AA { \n" +
                "      //@ model static class B { static double i; }  \n" +
                "      //@ model static class C { static double i; }  \n" +
                "      C b;\n" +            // Sees C
                "      //@ ghost C bb;\n" + // Sees A.AA.C
                "      void m(); \n" +
                "         \n" +
                "         \n" +
                "      \n" +
                "   }\n" +
                "   static class AA {\n" + // ERROR - duplicate - LINE 12
                "   }\n" +
                "   static class BB {\n" + // ERROR - no match
                "   }\n" +
                "}\n" +
                "class A {}\n" +  // ERROR - duplicate
                "class B {}\n" +  // ERROR - no match
                ""
        );
        helpTCF("A.java",
                "public class A {   \n" +
                "   static class AA { \n" +
                "      B b;\n" + // ERROR - AA.B visible only in specs
                "      void m() {\n" +
                "         boolean kk = B.i;\n" + // ERROR - AA.B visible only in specs
                "         //@ assert B.i;\n" + // ERROR, B OK, but B.i is wrong type
                "      }\n" +
                "   }\n" +
                "}\n" +
                "class C {}\n"

                ,"/$A/A.jml:17: error: duplicate class: A",1
                ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:17:",8
                ,"/$A/A.jml:18: error: There is no class to match this Java declaration in the specification file: B",1
                ,"/$A/A.jml:12: error: duplicate class: AA",11
                ,"/$A/A.jml:2: error: Associated declaration: /$A/A.jml:12:",11
                ,"/$A/A.jml:14: error: There is no class to match this Java declaration in the specification file: BB",11 // FIXME - would like to have the prefix
                ,"/A.java:3: error: cannot find symbol\n  symbol:   class B\n  location: class A.AA",7
                ,"/A.java:5: error: cannot find symbol\n  symbol:   variable B\n  location: class A.AA",23
                ,"/A.java:6: error: incompatible types: double cannot be converted to boolean",22
        );
    }
 
    @Test
    public void testToplevelModel() {
        addMockFile("$A/A.jml",
                "public class A {   \n" +
                "}\n" +
                "//@ model class A {}\n" + // ERROR - duplicates a Java declaration
                "//@ model class B {}\n" +
                "//@ model class B {}\n" + // ERROR - duplicates a JML declaration
                "/*@ model class C {}*/\n" +
                " class D {}"              // ERROR - does not match
        );
        helpTCF("A.java",
                "public class A {   \n" +
                "}\n" +
                ""
        ,"/$A/A.jml:3: error: This JML class declaration conflicts with an existing Java class with the same name: A", 11
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:3:",8
        ,"/$A/A.jml:7: error: There is no class to match this Java declaration in the specification file: D",2
        ,"/$A/A.jml:5: error: duplicate class: B", 11
        //,"/$A/A.jml:4: error: Associated declaration: /$A/A.jml:5:",11 // FIXME - WOuld be nice to point to the duplicate
        );
    }
 
}
