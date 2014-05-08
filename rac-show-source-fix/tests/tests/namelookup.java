package tests;

import org.junit.Test;

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
                "}",
        "/A.java:3: incompatible types\n  required: boolean\n  found:    double",17,
        "/A.java:2: incompatible types\n  required: boolean\n  found:    int",18
        );
    }

    @Test
    public void testLookup2() {
        helpTCF("A.java",
                " public class A { int k; float d; \n" +
                "   //@ constraint \\old(k); constraint \\old(d);\n" +
                "   void m(double d) {\n" +
                "        //@ assert k;\n" +
                "        double k;\n" +
                "        //@ assert k;\n" +
                "        //@ assert \\old(k);\n" + 
                "        //@ assert \\old(d);\n" + 
                "   }\n" +
                "}",
        "/A.java:4: incompatible types\n  required: boolean\n  found:    int",20,
        "/A.java:6: incompatible types\n  required: boolean\n  found:    double",20,
        "/A.java:7: incompatible types\n  required: boolean\n  found:    int",24,
        "/A.java:8: incompatible types\n  required: boolean\n  found:    double",24,
        "/A.java:2: incompatible types\n  required: boolean\n  found:    int",23,
        "/A.java:2: incompatible types\n  required: boolean\n  found:    float",43
        );
    }

    @Test
    public void testLookup3() {
        helpTCF("A.java",
                " public class A { int k; Object o; \n" +
                "   void m() {\n" +
                "      //@ ghost Object k;\n" +
                "      boolean b = k == null;\n" +  // ERROR
                "      //@ assert k == 1;\n" +  // Allowed by boxing
                "      //@ assert k == null;\n" +
                "      boolean bb = k == o;\n" +  // Allowed by boxing
                "      boolean bbb = k == null;\n" +  // ERROR
                "   }\n" +
                "}",
        "/A.java:4: incomparable types: int and <nulltype>",21,
        "/A.java:8: incomparable types: int and <nulltype>",23);
    }

    @Test
    public void testDupField() {
        helpTCF("A.java",
                " class A { //@ ghost int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k) {}\n" +
                "}",
        "/A.java:2: variable k is already defined in class A",21
        ,"/A.java:2: The field k in the specification matches a Java field A.k but they have different types: double vs. int",14
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
        ,"/$A/A.jml:2: The field k in the specification matches a Java field A.k but they have different types: double vs. int",4
        ,"/$A/A.jml:2: This specification declaration of field k has the same name as a previous field declaration",11
        ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",16
        ,"/$A/A.jml:3: The specification of the method A.m(double) must not have a body",21
        );
    }

    @Test
    public void testDupField1b() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   int k;\n" +
                "   void m(double k) {}\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: This specification declaration of field k has the same name as a previous field declaration",8
        ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:2: ",16
        ,"/$A/A.jml:3: The specification of the method A.m(double) must not have a body",21
        );
    }

    @Test
    public void testDupField1a() {
        addMockFile("$A/A.jml",
                " class A { int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k);\n" +
                "}");
        helpTCF("A.java",
                        " class A { int k;  \n" +
                        "   void m(double k) {}\n" +
                        "}"
        ,"/$A/A.jml:2: variable k is already defined in class A",21
        ,"/$A/A.jml:2: The field k in the specification matches a Java field A.k but they have different types: double vs. int",14
        );
    }

    @Test
    public void testDupField2() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   //@ ghost double k;\n" +
                "   void m(double k) {}\n" +
                "}",
                "/A.java:2: variable k is already defined in class A",21
                ,"/A.java:2: The field k in the specification matches a Java field A.k but they have different types: double vs. int",14
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
        "/A.java:3: variable d is already defined in method m(double)",11);
    }

    @Test
    public void testDupVar2() {
        helpTCF("A.java",
                " class A { int k;  \n" +
                "   void m(double d) {\n" +
                "      //@ ghost int d;\n" +
                "   }\n" +
                "}",
        "/A.java:3: variable d is already defined in method m(double)",21);
    }

    @Test
    public void testGhostField() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ ghost double k;\n" +
                "   void m() {\n" +
                "      boolean kk = k;\n" +
                "      //@ assert k;\n" +
                "   }\n" +
                "}",
        "/A.java:4: cannot find symbol\n  symbol:   variable k\n  location: class A", 20,
        "/A.java:5: incompatible types\n  required: boolean\n  found:    double",18);
    }

    @Test
    public void testModelField() {
        helpTCF("A.java",
                " class A {   \n" +
                "   //@ model double k;\n" +
                "   void m() {\n" +
                "      boolean kk = k;\n" +
                "      //@ assert k;\n" +
                "   }\n" +
                "}",
        "/A.java:4: cannot find symbol\n  symbol:   variable k\n  location: class A", 20,
        "/A.java:5: incompatible types\n  required: boolean\n  found:    double",18);
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
        "/A.java:4: cannot find symbol\n  symbol:   method k()\n  location: class A", 20,
        "/A.java:5: incompatible types\n  required: boolean\n  found:    double",19);
    }

    @Test
    public void testModelMethod2() {
        helpTCF("A.java",
                " class A {   int k() { return 0; }\n" +
                "   //@ model double k() { return 1; }\n" +
                "   void m() {\n" +
                "      boolean kk = k();\n" +
                "   }\n" +
                "}"
        ,"/A.java:2: method k() is already defined in class A",21
        //,"/A.java:2: The return types of method A.k() are different in the specification and java files: double vs. int",14
        ,"/A.java:4: incompatible types\n  required: boolean\n  found:    int", 21
        );
    }

    @Test
    public void testModelMethod3() {
        helpTCF("A.java",
                " class A { /*@pure*/  int k(int i) { return 0; }\n" +
                "   //@ model pure double k(boolean d) { return 0; }\n" +
                "   //@ requires k(true); \n" +
                "   //@ requires k(0); \n" +
                "   void m() {\n" +
                "   }\n" +
                "}",
        "/A.java:3: incompatible types\n  required: boolean\n  found:    double", 18,
        "/A.java:4: incompatible types\n  required: boolean\n  found:    int",18);
    }

    @Test
    public void testModelMethod4() {
        helpTCF("A.java",
                " class A {   static /*@pure*/int k(int i) { return 0; }\n" +
                "   static class B {\n" +
                "      //@ model pure static double k(int i) { return 0; }\n" +
                "      boolean b = k(0);\n" +
                "      //@ requires k(0); \n" +
                "      void m() {\n" +
                "         boolean kk = k(0);\n" +
                "         //@ assume k(0);\n" +
                "      }\n" +
                "   }\n" +
                "}"
        ,"/A.java:4: incompatible types\n  required: boolean\n  found:    int", 20
        ,"/A.java:7: incompatible types\n  required: boolean\n  found:    int", 24
        ,"/A.java:8: incompatible types\n  required: boolean\n  found:    double", 22
        ,"/A.java:5: incompatible types\n  required: boolean\n  found:    double", 21
        );
    }

    /** No body for model method is OK */
    @Test
    public void testModelMethod5() {
        helpTCF("A.java",
                " class A {   \n" +
                "      //@ model pure static double k(int i);\n" +
                "      //@ requires k(0); \n" +
                "      void m() {\n" +
                "         //@ assume k(0);\n" +
                "      }\n" +
                "}"
        ,"/A.java:5: incompatible types\n  required: boolean\n  found:    double", 22
        ,"/A.java:3: incompatible types\n  required: boolean\n  found:    double", 21
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
                "         boolean kk = B.i;\n" +
                "         //@ assert B.i;\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                " class B { static int i; }  \n" +
                ""
        ,"/A.java:7: incompatible types\n  required: boolean\n  found:    int",24 
        ,"/A.java:8: incompatible types\n  required: boolean\n  found:    double",22
        );
    }
 
    @Test
    public void testModelClass2() {
        helpTCF("A.java",
                " class A {   \n" +
                "   static class AA {\n" +
                "      //@ model static class B { static double i; }  \n" +
                "      B b;\n" +
                "      //@ ghost B bb;\n" +
                "      void m() {\n" +
                "         boolean kk = B.i;\n" +
                "         //@ assert B.i;\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                ""
        ,"/A.java:4: cannot find symbol\n  symbol:   class B\n  location: class A.AA",7
        ,"/A.java:7: cannot find symbol\n  symbol:   variable B\n  location: class A.AA",23
        ,"/A.java:8: incompatible types\n  required: boolean\n  found:    double",22
            );
    }

    @Test
    public void testModelClass3() {
        addMockFile("$A/A.jml",
                "public class A {   \n" +
                "   static class AA {\n" +
                "      //@ model static class B { static double i; }  \n" +
                "      B b;\n" +
                "      //@ ghost B bb;\n" +
                "      void m(); \n" +
                "         \n" +
                "         \n" +
                "      \n" +
                "   }\n" +
                "   static class AA {\n" +
                "   }\n" +
                "   static class BB {\n" +
                "   }\n" +
                "}\n" +
                "class A {}\n" +
                "class B {}\n" +
                ""
        );
        helpTCF("A.java",
                "public class A {   \n" +
                "   static class AA {\n" +
                "      B b;\n" +
                "      void m() {\n" +
                "         boolean kk = B.i;\n" +
                "         //@ assert B.i;\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                ""
       ,"/$A/A.jml:16: This specification declaration of type A has the same name as a previous JML type declaration",1
       ,"/$A/A.jml:1: Associated declaration: /$A/A.jml:16: ",8
       ,"/$A/A.jml:17: This specification declaration of type B does not match any Java type declaration in /A.java",1
       ,"/$A/A.jml:11: This specification declaration of type AA has the same name as a previous JML type declaration",11
       ,"/$A/A.jml:2: Associated declaration: /$A/A.jml:11: ",11
       ,"/$A/A.jml:13: This specification declaration of type BB does not match any Java type declaration in /A.java",11
       // FIXME: Would prefer this: ,"/$A/A.jml:13: This specification declaration of type BB in A does not match any Java type declaration.",11
        ,"/A.java:3: cannot find symbol\n  symbol:   class B\n  location: class A.AA",7
        ,"/A.java:5: cannot find symbol\n  symbol:   variable B\n  location: class A.AA",23
        ,"/A.java:6: incompatible types\n  required: boolean\n  found:    double",22
        );
    }
 
    @Test
    public void testToplevelModel() {
        addMockFile("$A/A.jml",
                "public class A {   \n" +
                "}\n" +
                "//@ model class A {}\n" +
                "//@ model class B {}\n" +
                "//@ model class B {}\n" +
                "/*@ model class C {}*/\n" +
                "public class D {}"
        );
        helpTCF("A.java",
                "public class A {   \n" +
                "}\n" +
                ""
        ,"/$A/A.jml:7: This specification declaration of type D does not match any Java type declaration in /A.java",8
        ,"/$A/A.jml:3: duplicate class: A",11
        ,"/$A/A.jml:5: duplicate class: B",11

        );
    }
 
}
