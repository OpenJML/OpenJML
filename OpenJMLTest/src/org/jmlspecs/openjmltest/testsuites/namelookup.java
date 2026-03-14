package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.*;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class namelookup extends TCBase {

    @Test
    public void testLookup() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ invariant k;
                   //@ requires k;
                   void m(double k) {}
                }
                """
        ,"/A.java:2: error: incompatible types: int cannot be converted to boolean",18
        ,"/A.java:3: error: incompatible types: double cannot be converted to boolean",17
        );
    }

    @Test
    public void testLookup2() {
        helpTCText("A.java",
                """
                 public class A { int k; float d;
                   //@ constraint \\old(k); constraint \\old(d);
                   void m(double d) {
                        //@ assert k;
                        double k;
                        //@ assert k;
                        //@ assert \\old(k);
                        //@ assert \\old(d);
                   }
                }
                """
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
        helpTCText("A.java",
                """
                 public class A { int k; Object o;
                   void m() {
                      //@ ghost Object k;
                      boolean b = k;
                      //@ assert k == 1;
                      //@ assert k == null;
                      boolean bb = k;
                      boolean bbb = k == 0;
                   }
                }
                """
        ,"/A.java:4: error: incompatible types: int cannot be converted to boolean",19
        ,"/A.java:5: error: bad operand types for binary operator '=='\n"
        		+ "  first type:  java.lang.Object\n"
        		+ "  second type: int",20
        ,"/A.java:7: error: incompatible types: int cannot be converted to boolean",20
        );
    }

    @Test
    public void testDupField() {
        helpTCText("A.java",
                """
                 class A { //@ ghost int k;
                   //@ ghost double k;
                   int m;
                   int m;
                }
                """
                ,"/A.java:2: error: variable k is already defined in class A",21
                ,"/A.java:4: error: variable m is already defined in class A",8
        );
    }

    @Test
    public void testDupField1() {
        addMockFile("$A/A.jml",
                """
                 class A { int k;
                   double k;
                   void m(double k) {}
                }
                """);
        helpTCText("A.java",
                """
                 class A { int k;
                   void m(double k) {}
                }
                """
        ,"/$A/A.jml:2: error: This specification declaration of field A.k has the same name as a previous field declaration",11
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",16
        ,"/$A/A.jml:3: error: The specification of the method A.m(double) must not have a body",21
        );
    }

    @Test
    public void testDupField1a() {
        addMockFile("$A/A.jml",
                """
                 class A { int k;
                   int k;
                }
                """);
        helpTCText("A.java",
                """
                 class A { int k;
                }
                """
        ,"/$A/A.jml:2: error: This specification declaration of field A.k has the same name as a previous field declaration",8
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",16
        );
    }

    @Test
    public void testDupField1b() {
        addMockFile("$A/A.jml",
                """
                 class A { int k;
                   //@ ghost double k;
                   void m(double k);
                }
                """);
        helpTCText("A.java",
                """
                 class A { int k;
                   void m(double k) {}
                }
                """
        ,"/$A/A.jml:2: error: This JML field declaration conflicts with an existing field with the same name: A.k",21
        ,"/A.java:1: error: Associated declaration: /$A/A.jml:2:",16
        );
    }

    @Test
    public void testDupField1c() {
        addMockFile("$A/A.jml",
                """
                 class A { int k;
                   int k;
                }
                """);
        helpTCText("A.java",
                """
                 class A { int k;
                   void m(double k) {}
                }
                """
        ,"/$A/A.jml:2: error: This specification declaration of field A.k has the same name as a previous field declaration",8
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:2:",16
        );
    }

    @Test
    public void testDupField2() {
        helpTCText("A.java",
                """
                 class A { int k;
                   //@ ghost double k;
                   void m(double k) {}
                }
                """
                ,"/A.java:2: error: variable k is already defined in class A",21
                );
    }

    @Test
    public void testDupVar() {
        helpTCText("A.java",
                """
                 class A { int k;
                   void m(double d) {
                      int d;
                   }
                }
                """,
        "/A.java:3: error: variable d is already defined in method m(double)",11);
    }

    @Test
    public void testDupVar2() {
        helpTCText("A.java",
                """
                 class A { int k;
                   void m(double d) {
                      //@ ghost int d;
                   }
                }
                """,
        "/A.java:3: error: variable d is already defined in method m(double)",21);
    }

    @Test
    public void testGhostField() {
        helpTCText("A.java",
                """
                 class A {
                   //@ ghost double k;
                   void m() {
                      boolean kk = k; // ERROR - no symbol k
                      //@ assert k;  // ERROR - double to boolean
                   }
                }
                """
        ,"/A.java:4: error: cannot find symbol\n"
        + "  symbol:   variable k\n"
        + "  location: class A", 20
        ,"/A.java:5: error: incompatible types: double cannot be converted to boolean", 18
        );
    }

    @Test
    public void testModelField() {
        helpTCText("A.java",
                """
                 class A {
                   //@ model double k;
                   void m() {
                      boolean kk = k; // ERROR - no symbol k
                      //@ assert k; // ERROR - double to boolean
                   }
                }
                """,
        "/A.java:4: error: cannot find symbol\n  symbol:   variable k\n  location: class A", 20,
        "/A.java:5: error: incompatible types: double cannot be converted to boolean",18);
    }

    @Test
    public void testModelMethod() {
        helpTCText("A.java",
                """
                 class A {
                   //@ model pure double k() { return 0; }
                   void m() {
                      boolean kk = k();
                      //@ assert k();
                   }
                }
                """,
        "/A.java:4: error: cannot find symbol\n  symbol:   method k()\n  location: class A", 20,
        "/A.java:5: error: incompatible types: double cannot be converted to boolean",19);
    }

    @Test
    public void testModelMethod2() {
        helpTCText("A.java",
                """
                 class A {   int k() { return 0; }
                   //@ model double k() { return 1; } // ERROR - duplicate
                   void m() {
                      boolean kk = k();
                   }
                }
                """
                ,"/A.java:2: error: method k() is already defined in class A",21
                ,"/A.java:4: error: incompatible types: int cannot be converted to boolean", 21
        );
    }

    @Test
    public void testModelMethod3() {
        helpTCText("A.java",
                """
                 class A { /*@ pure*/  int k(int i) { return 0; }
                   //@ model pure double k(boolean d) { return 0; }
                   //@ requires k(true); // ERROR - double to boolean
                   //@ requires k(0); // ERROR - int to boolean
                   void m() {
                   }
                }
                """,
        "/A.java:3: error: incompatible types: double cannot be converted to boolean", 18,
        "/A.java:4: error: incompatible types: int cannot be converted to boolean",18);
    }

    @Test
    public void testModelMethod4() {
        helpTCText("A.java",
                """
                 class A {   static /*@pure*/int k(int i) { return 0; }
                   static class B {
                      //@ model pure static double k(int i) { return 0; }
                      boolean b = k(0);  // TYPE ERROR
                      //@ requires k(0);  // TYPE ERROR
                      void m() {
                         boolean kk = k(0);  // TYPE ERROR
                         //@ assume k(0);  // TYPE ERROR
                      }
                   }
                }
                """
        ,"/A.java:4: error: incompatible types: int cannot be converted to boolean", 20
        ,"/A.java:5: error: incompatible types: double cannot be converted to boolean", 21
        ,"/A.java:7: error: incompatible types: int cannot be converted to boolean", 24
        ,"/A.java:8: error: incompatible types: double cannot be converted to boolean", 22
        );
    }

    @Test
    public void testModelMethod5() {
        helpTCText("A.java",
                """
                 class A {
                      //@ model pure static double k(int i);
                      //@ requires k(0);  // TYPE ERROR
                      void m() {
                         //@ assume k(0);  // TYPE ERROR
                      }
                }
                """
                ,"/A.java:3: error: incompatible types: double cannot be converted to boolean", 21
                ,"/A.java:5: error: incompatible types: double cannot be converted to boolean", 22
        );
    }

    @Test
    public void testModelClass() {
        helpTCText("A.java",
                """
                 public class A {
                   static class AA {
                      //@ model static class B { static double i; }
                      B b;
                      //@ ghost B bb;
                      void m() {
                         boolean kk = B.i; // ERROR - int to boolean (top-level B)
                         //@ assert B.i; // ERROR - double to boolean (A.AA.B)
                      }
                   }
                }
                 class B { static int i; }
                """
        ,"/A.java:7: error: incompatible types: int cannot be converted to boolean",24
        ,"/A.java:8: error: incompatible types: double cannot be converted to boolean",22
        );
    }

    @Test
    public void testModelClass2() {
        helpTCText("A.java",
                """
                 class AXYZ {
                   static class AAXYZ {
                      //@ model static class B { static double i; }
                      B bxyz;  // ERROR - no B
                      //@ ghost B bb; // OK - A.AA.B
                      void mxyz() {
                         boolean kk = B.i; // ERROR - no B
                         //@ assert B.i;   // ERROR - found B, B.i is wrong type
                      }
                   }
                }
                """
        ,"/A.java:4: error: cannot find symbol\n  symbol:   class B\n  location: class AXYZ.AAXYZ",7
        ,"/A.java:7: error: cannot find symbol\n  symbol:   variable B\n  location: class AXYZ.AAXYZ",23
        ,"/A.java:8: error: incompatible types: double cannot be converted to boolean",22
            );
    }

    @Test
    public void testModelClass3() {
        addMockFile("$A/A.jml",
                """
                public class A {
                   static class AA {
                      //@ model static class B { static double i; }
                      //@ model static class C { static double i; }
                      C b;            // Sees C
                      //@ ghost C bb; // Sees A.AA.C
                      void m();
                   }
                   static class AA { // ERROR - duplicate - LINE 12
                   }
                   static class BB { // ERROR - no match
                   }
                }
                class A {}  // ERROR - duplicate
                class B {}  // ERROR - no match
                """
        );
        helpTCText("A.java",
                """
                public class A {
                   static class AA {
                      B b;// ERROR - AA.B visible only in specs
                      void m() {
                         boolean kk = B.i; // ERROR - AA.B visible only in specs
                         //@ assert B.i; // ERROR, B OK, but B.i is wrong type
                      }
                   }
                }
                class C {}
                """

                ,"/$A/A.jml:14: error: duplicate class: A", 1
                ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:14:", 8
                ,"/$A/A.jml:15: error: There is no class to match this Java declaration in the specification file: B",1
                ,"/$A/A.jml:9: error: duplicate class: A.AA",11
                ,"/$A/A.jml:2: error: Associated declaration: /$A/A.jml:9:", 11
                ,"/$A/A.jml:11: error: There is no class to match this Java declaration in the specification file: A.BB",11 // FIXME - only prints one level of parent
                ,"/A.java:3: error: cannot find symbol\n  symbol:   class B\n  location: class A.AA",7
                ,"/A.java:5: error: cannot find symbol\n  symbol:   variable B\n  location: class A.AA",23
                ,"/A.java:6: error: incompatible types: double cannot be converted to boolean",22
        );
    }

    @Test
    public void testToplevelModel() {
        addMockFile("$A/A.jml",
                """
                public class A {
                }
                //@ model class A {} // ERROR - duplicates a Java declaration
                //@ model class B {}
                //@ model class B {} // ERROR - duplicates a JML declaration
                /*@ model class C {}*/
                 class D {}          // ERROR - does not match
                """
        );
        helpTCText("A.java",
                """
                public class A {
                }
                """
        ,"/$A/A.jml:3: error: This JML class declaration conflicts with an existing Java class with the same name: A", 11
        ,"/$A/A.jml:1: error: Associated declaration: /$A/A.jml:3:",8
        ,"/$A/A.jml:5: error: This model class declaration has the same name as a previous one: B", 11
        ,"/$A/A.jml:4: error: Associated declaration: /$A/A.jml:5:", 11
        ,"/$A/A.jml:7: error: There is no class to match this Java declaration in the specification file: D",2
        );
    }

}
