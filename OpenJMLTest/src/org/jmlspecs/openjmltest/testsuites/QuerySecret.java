package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.*;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class QuerySecret extends TCBase {

    // FIXME - there still is a problem in that annotations are checked more than once - we have to comment out the error message to avoid repeated error messages

    @Test
    public void testOK1() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Query("q") int m() { return 0; }
                }
                """
        );
    }

    @Test
    public void testBadParse() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Query("q","r") int m() { return 0; }
                }
                """
                ,"/A.java:4: annotation values must be of the form 'name=value'",10
                ,"/A.java:4: annotation values must be of the form 'name=value'",14
        );
    }

    @Test
    public void testBadParse2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Query(v="q") int m() { return 0; }
                }
                """
                ,"/A.java:4: cannot find symbol\n  symbol:   method v()\n  location: @interface org.jmlspecs.annotation.Query",12
        );
    }

    @Test
    public void testBadParse3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Query(9) int m() { return 0; }
                }
                """
                ,"/A.java:4: incompatible types: int cannot be converted to java.lang.String",10
        );
    }

    @Test
    public void testBadParse4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Query(value="q",value="r") int m() { return 0; }
                }
                """
                ,"/A.java:4: duplicate element 'value' in annotation @org.jmlspecs.annotation.Query.",20
        );
    }

    @Test
    public void testConstantExpression() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Query(value="q"+"r") int m() { return 0; }
                }
                """
                ,"/A.java:4: There is no field or datagroup named qr in the class or its super types",15
        );
    }

    @Test
    public void testOKnamed() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Query(value="q") int m() { return 0; }
                }
                """
        );
    }

    @Test
    public void testNotModel() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  \\datagroup q;
                  @Query("q") int m() { return 0; }
                }
                """
                //,"/A.java:4: A datagroup must be declared model",10  // OK
        );
    }

    @Test
    public void testSNotModel() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  \\datagroup q;
                  @Secret("q") int m() { return 0; }
                }
                """
                //,"/A.java:4: A datagroup must be declared model",11
        );
    }

    @Test
    public void testOtherDeclOK() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ model int q;
                  @Query("q") int m() { return 0; }
                }
                """
        );
    }

    @Test
    public void testSOtherDeclOK() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ model int q;
                  @Secret("q") int m() { return 0; }
                }
                """
        );
    }

    /** Can be query for an inherited deata group */
    @Test
    public void testOK2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                class B {
                  /*@ public model \\datagroup q; */
                }
                public class A extends B {
                  @Query("q") int m() { return 0; }
                }
                """
        );
    }

    /** A named data group must exist */
    @Test
    public void testNoDG() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //datagroup q;
                  @Query("q") int m() { return 0; }
                }
                """
                ,"/A.java:4: There is no field or datagroup named q in the class or its super types",10
        );
    }

    /** A named data group may not be in an enclosing class */
    @Test
    public void testNoDG2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  public class X {
                    @Query("q") int m() { return 0; }
                  }
                }
                """
                ,"/A.java:5: There is no field or datagroup named q in the class or its super types",12
        );
    }

    /** A default existent datagroup */
    @Test
    public void testOK3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup m;
                  @Query int m() { return 0; }
                }
                """
        );
    }

    /** A default non-existent datagroup */
    @Test
    public void testOK4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Query int m() { return 0; }
                }
                """
        );
    }

    @Test
    public void testSOK1() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret("q") int m() { return 0; }
                }
                """
        );
    }

    @Test
    public void testSBadParse() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret("q","r") int m() { return 0; }
                }
                """
                ,"/A.java:4: annotation values must be of the form 'name=value'",11
                ,"/A.java:4: annotation values must be of the form 'name=value'",15
                ,"/A.java:4: A secret annotation on a method must have exactly one argument",3
        );
    }

    @Test
    public void testSBadParse2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret(v="q") int m() { return 0; }
                }
                """
                ,"/A.java:4: cannot find symbol\n  symbol:   method v()\n  location: @interface org.jmlspecs.annotation.Secret",13
        );
    }

    @Test
    public void testSBadParse3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret(9) int m() { return 0; }
                }
                """
                ,"/A.java:4: incompatible types: int cannot be converted to java.lang.String",11
        );
    }

    @Test
    public void testSBadParse4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret(value="q",value="r") int m() { return 0; }
                }
                """
                ,"/A.java:4: duplicate element 'value' in annotation @org.jmlspecs.annotation.Secret.",21
        );
    }

    @Test
    public void testSOKnamed() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret(value="q") int m() { return 0; }
                }
                """
        );
    }

    /** Can be query for an inherited deata group */
    @Test
    public void testSOK2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                class B {
                  /*@ public model \\datagroup q; */
                }
                public class A extends B {
                  @Secret("q") int m() { return 0; }
                }
                """
        );
    }

    /** A named data group must exist */
    @Test
    public void testSNoDG() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //\\datagroup q;
                  @Secret("q") int m() { return 0; }
                }
                """
                ,"/A.java:4: There is no field or datagroup named q in the class or its super types",11
        );
    }

    /** A named data group may not be in an enclosing class */
    @Test
    public void testSNoDG2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  public class X {
                    @Secret("q") int m() { return 0; }
                  }
                }
                """
                ,"/A.java:5: There is no field or datagroup named q in the class or its super types",13
        );
    }

    /** A default existent datagroup */
    @Test
    public void testSOK3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup m;
                  @Secret int m() { return 0; }
                }
                """
                ,"/A.java:4: A secret annotation on a method must have exactly one argument",3
        );
    }

    /** A default non-existent datagroup */
    @Test
    public void testSOK4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Query int m() { return 0; }
                }
                """
        );
    }

    /** Same datagroup */
    @Test
    public void testSameDG() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Query
                  @Secret("m")
                  int m() { return 0; }
                }
                """
                ,"/A.java:3: A method may not be both secret and query for the same datagroup",3
        );
    }

    @Test
    public void testNoOuter() {
        helpTCText("Outer.java",
                """
                import org.jmlspecs.annotation.*;
                public class Outer {   int p;
                static public class A {
                  @Query
                  @Secret("p")
                  int m() { return 0; }
                }
                 public class B {
                  @Query
                  @Secret("p")
                  int m() { return 0; }
                }
                }
                """
                ,"/Outer.java:5: There is no field or datagroup named p in the class or its super types",12
                ,"/Outer.java:10: There is no field or datagroup named p in the class or its super types",12
        );
    }

    @Test
    public void testSuper() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                 public class A extends B {
                  @Query
                  @Secret("p")
                  int m() { return 0; }
                }
                  class B {
                  int p;
                }
                """
        );
    }

    @Test
    public void testInterface() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                 public class A implements B {
                  @Query
                  @Secret("p")
                  int m() { return 0; }
                }
                  interface B {
                  //@ instance model int p;
                }
                """
        );
    }

    // Secret no longer allows a default -- FIXME
//    /** Same datagroup */
//    @Test
//    public void testSameDG1() {
//        helpTCFText("A.java",
//                "import org.jmlspecs.annotation.*;\n" +
//                "public class A { \n" +
//                "  @Secret @Query(\"m\") int m() { return 0; } \n" +
//                "} \n"
//                ,"/A.java:3: There is no model field or datagroup named m in the class or its super types",18
//        );
//    }

    /** Same datagroup */
    @Test
    public void testSameDG2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret("m")
                  @Query
                  int m() { return 0; }
                }
                """
                ,"/A.java:4: A method may not be both secret and query for the same datagroup",3
        );
    }

    /** Same datagroup */
    @Test
    public void testSameDG3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret("m")
                  @Query("m")
                  int m() { return 0; }
                }
                """
                ,"/A.java:4: There is no field or datagroup named m in the class or its super types",11
                ,"/A.java:3: There is no field or datagroup named m in the class or its super types",11
        );
    }

    /** Same datagroup */
    @Test
    public void testSameDGOK() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret("q")
                  @Query
                  int m() { return 0; }
                }
                """
        );
    }

    /** Same datagroup */
    @Test
    public void testSameDGOK2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup m;
                  //@ public model \\datagroup q;
                  @Secret("m")
                  @Query("q")
                  int m() { return 0; }
                }
                """
        );
    }

    /** Same datagroup */
    @Test
    public void testSameDGOK3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q,r;
                  @Secret("r")
                  @Query("q")
                  int m() { return 0; }
                }
                """
        );
    }

    /** Same datagroup */
    @Test
    public void testSameDG4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret("q")
                  @Query("q")
                  int m() { return 0; }
                }
                """
                ,"/A.java:5: A method may not be both secret and query for the same datagroup",3
        );
    }

    @Test
    public void testFOK1() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public secret model \\datagroup q;
                  @Secret int m; //@ in q;
                }
                """
        );
    }

    /** Secret, but not in a datagroup */
    @Test
    public void testFNotIn() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret int m;
                }
                """
                //,"/A.java:4: A secret field must be a model field or in a secret datagroup",15
        );
    }

    /** Secret, but not in a datagroup */
    @Test
    public void testFInNonSecret() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  @Secret int m; //@ in q;
                }
                """
                ,"/A.java:4: A datagroup for a secret field must be secret",22
        );
    }

    /** Not secret but in a secret datagroup */
    @Test
    public void testFInSecret() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public secret model \\datagroup q;
                  int m; //@ in q;
                }
                """
                ,"/A.java:4: A datagroup for a non-secret field must be non-secret",14
        );
    }

    /** Not secret but in a secret datagroup */
    @Test
    public void testFInSecret2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public secret model \\datagroup q;
                  //@ model int m; //@ in q;
                }
                """
                ,"/A.java:4: A datagroup for a non-secret field must be non-secret",24
        );
    }

    /** OK - model fields are their own datagroups */
    @Test
    public void testFNotInButModel() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model \\datagroup q;
                  //@ secret model int m;
                }
                """
        );
    }

    /** Valid argument, but not for a field */
    @Test
    public void testFBadParse() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret("q") int m;
                }
                """
                ,"/A.java:3: A secret declaration for a field may not have arguments",11
                //,"/A.java:3: A secret field must be a model field or in a secret datagroup",20
        );
    }

    /** Invalid argument, also not for field */
    @Test
    public void testFBadParse2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret(v="q") int m;
                }
                """
                ,"/A.java:3: cannot find symbol\n  symbol:   method v()\n  location: @interface org.jmlspecs.annotation.Secret",13
                ,"/A.java:3: A secret declaration for a field may not have arguments",12
        );
    }

    /** Invalid argument, aslo not for field */
    @Test
    public void testFBadParse3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret(9) int m;
                }
                """
                ,"/A.java:3: incompatible types: int cannot be converted to java.lang.String",11
                ,"/A.java:3: A secret declaration for a field may not have arguments",11
                //,"/A.java:3: A secret field must be a model field or in a secret datagroup",18   // FIXME
        );
    }

    /** Valid argument, but not for a field */
    @Test
    public void testFBadParse4() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  @Secret(value="q") int m;
                }
                """
                ,"/A.java:3: A secret declaration for a field may not have arguments",16
                //,"/A.java:3: A secret field must be a model field or in a secret datagroup",26
        );
    }

    /** OK - standard use */
    @Test
    public void testRepresents() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret public model int i;
                  //@ secret public model int j; in i;
                  //@ secret public represents i = j;
                }
                """
        );
    }

    /** Differently secret expression */
    @Test
    public void testRepresents0() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret public model int i;
                  //@ secret public model int j;
                  //@ secret public represents i = j;
                }
                """
                ,"/A.java:5: A field may not be read in a secret context unless it is in the same secret datagroup: j not in i",36
        );
    }

    /** Secret id with non-secret represents */
    @Test
    public void testRepresents1() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret public model int i;
                  //@ public represents i = 0;
                }
                """
                ,"/A.java:4: A represents clause and its identifier must both be secret or both not be secret",14
        );
    }

    /** Secret represents with non-secret id */
    @Test
    public void testRepresents2() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model int i;
                  //@ secret public represents i = 0;
                }
                """
                ,"/A.java:4: A represents clause and its identifier must both be secret or both not be secret",21
        );
    }

    /** Secret on represents may not have an argument */
    @Test
    public void testRepresents3() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret public model int i;
                  //@ @Secret("i") public represents i = 0;
                }
                """
                ,"/A.java:4: A secret declaration for a represents clause may not have arguments",15
        );
    }

    /** testing secret in non-secret represents expression */
    @Test
    public void testRepresents5() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret public model int j;
                  //@ public model int i;
                  //@ public represents i = j;
                }
                """
                ,"/A.java:5: Secret fields may not be read in non-secret context: j",29
        );
    }

    /** no secret in invariant */
    @Test
    public void testInvariantSecret() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ secret public model int j;
                  //@ public invariant j == 0;
                  //@ public constraint j == 0;
                }
                """
                ,"/A.java:4: Secret fields may not be read in non-secret context: j",24
                ,"/A.java:5: Secret fields may not be read in non-secret context: j",25
        );
    }

    @Test
    public void testMethodCallSecret() {
        helpTCText("A.java",
                """
                import org.jmlspecs.annotation.*;
                public class A {
                  //@ public model int i;
                  //@ public model int j;
                  //@ @Query("i")
                  public int nq() {
                     mq(); // OK
                     mqq(); // BAD
                     ms(); // OK
                     mo(); // BAD
                     mp(); // OK
                     mss(); return 0; // BAD
                  }
                  //@ @Secret("i")
                  public int ns() {
                     mq(); // OK
                     mqq(); // BAD
                     ms(); // OK
                     mo(); // BAD
                     mss(); return 0; // BAD
                  }
                  public int no() {
                     mq(); // OK
                     mqq(); // OK
                     ms(); // BAD
                     mo(); // OK
                     mss(); return 0; // BAD
                  }
                  @Secret("i") void ms() {}
                  @Secret("j") void mss() {}
                  @Query("i") void mq() {}
                  @Query("j") void mqq() {}
                  void mo() {}
                  @Pure void mp() {}
                }
                """
                ,"/A.java:8: A method called by a query or secret method must belong to the same datagroup",6
                ,"/A.java:10: A method called by a query or secret method must belong to the same datagroup",6
                ,"/A.java:12: A method called by a query or secret method must belong to the same datagroup",6
                ,"/A.java:17: A method called by a query or secret method must belong to the same datagroup",6
                ,"/A.java:19: A method called by a query or secret method must belong to the same datagroup",6
                ,"/A.java:20: A method called by a query or secret method must belong to the same datagroup",6
                ,"/A.java:25: A non-secret, non-query method may not call a secret method",6
                ,"/A.java:27: A non-secret, non-query method may not call a secret method",6
        );
    }
}
