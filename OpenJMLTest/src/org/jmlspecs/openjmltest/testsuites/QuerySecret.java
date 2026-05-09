package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.*;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class QuerySecret extends TCBase {

    // FIXME - there still is a problem in that annotations are checked more than once - we have to comment out the error message to avoid repeated error messages
    
    @Test
    public void testOK1() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    @Test
    public void testBadParse() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Query(\"q\",\"r\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: annotation values must be of the form 'name=value'",10
                ,"/A.java:4: annotation values must be of the form 'name=value'",14
        );
    }
    
    @Test
    public void testBadParse2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Query(v=\"q\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: cannot find symbol\n  symbol:   method v()\n  location: @interface org.jmlspecs.annotation.Query",12
        );
    }
    
    @Test
    public void testBadParse3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Query(9) int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: incompatible types: int cannot be converted to java.lang.String",10
        );
    }
    
    @Test
    public void testBadParse4() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Query(value=\"q\",value=\"r\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: duplicate element 'value' in annotation @org.jmlspecs.annotation.Query.",20
        );
    }
    
    @Test
    public void testConstantExpression() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Query(value=\"q\"+\"r\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: There is no field or datagroup named qr in the class or its super types",15
        );
    }
    
    @Test
    public void testOKnamed() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Query(value=\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    @Test
    public void testNotModel() { 
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  \\datagroup q;\n" +
                "  @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
                //,"/A.java:4: A datagroup must be declared model",10  // OK
        );
    }
    
    @Test
    public void testSNotModel() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  \\datagroup q;\n" +
                "  @Secret(\"q\") int m() { return 0; } \n" +
                "} \n"
                //,"/A.java:4: A datagroup must be declared model",11
        );
    }
    
    @Test
    public void testOtherDeclOK() { 
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ model int q;\n" +
                "  @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    @Test
    public void testSOtherDeclOK() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ model int q;\n" +
                "  @Secret(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** Can be query for an inherited deata group */
    @Test
    public void testOK2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "class B { /*@ public model \\datagroup q; */ }\n" +
                "public class A extends B { \n" + 
                "  @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** A named data group must exist */
    @Test
    public void testNoDG() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //datagroup q;\n" +
                "  @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: There is no field or datagroup named q in the class or its super types",10
        );
    }
    
    /** A named data group may not be in an enclosing class */
    @Test
    public void testNoDG2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A {\n" +
                "  //@ public model \\datagroup q;\n" +
                "  public class X { \n" + 
                "    @Query(\"q\") int m() { return 0; } \n" +
                "  }\n" +
                "} \n"
                ,"/A.java:5: There is no field or datagroup named q in the class or its super types",12
        );
    }
    
    /** A default existent datagroup */
    @Test
    public void testOK3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup m;\n" +
                "  @Query int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** A default non-existent datagroup */
    @Test
    public void testOK4() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Query int m() { return 0; } \n" +
                "} \n"
        );
    }

    @Test
    public void testSOK1() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    @Test
    public void testSBadParse() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(\"q\",\"r\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: annotation values must be of the form 'name=value'",11
                ,"/A.java:4: annotation values must be of the form 'name=value'",15
                ,"/A.java:4: A secret annotation on a method must have exactly one argument",3
        );
    }
    
    @Test
    public void testSBadParse2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(v=\"q\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: cannot find symbol\n  symbol:   method v()\n  location: @interface org.jmlspecs.annotation.Secret",13
        );
    }
    
    @Test
    public void testSBadParse3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(9) int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: incompatible types: int cannot be converted to java.lang.String",11
        );
    }
    
    @Test
    public void testSBadParse4() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(value=\"q\",value=\"r\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: duplicate element 'value' in annotation @org.jmlspecs.annotation.Secret.",21
        );
    }
    
    @Test
    public void testSOKnamed() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(value=\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** Can be query for an inherited deata group */
    @Test
    public void testSOK2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "class B { /*@ public model \\datagroup q; */ }\n" +
                "public class A extends B { \n" + 
                "  @Secret(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** A named data group must exist */
    @Test
    public void testSNoDG() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //\\datagroup q;\n" +
                "  @Secret(\"q\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: There is no field or datagroup named q in the class or its super types",11
        );
    }
    
    /** A named data group may not be in an enclosing class */
    @Test
    public void testSNoDG2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A {\n" +
                "  //@ public model \\datagroup q;\n" +
                "  public class X { \n" + 
                "    @Secret(\"q\") int m() { return 0; } \n" +
                "  }\n" +
                "} \n"
                ,"/A.java:5: There is no field or datagroup named q in the class or its super types",13
        );
    }
    
    /** A default existent datagroup */
    @Test
    public void testSOK3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup m;\n" +
                "  @Secret int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: A secret annotation on a method must have exactly one argument",3
        );
    }
    
    /** A default non-existent datagroup */
    @Test
    public void testSOK4() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Query int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** Same datagroup */
    @Test
    public void testSameDG() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Query @Secret(\"m\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:3: A method may not be both secret and query for the same datagroup",3
        );
    }

    @Test
    public void testNoOuter() {
        helpTCText("Outer.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class Outer {   int p; \n" +
                "static public class A { \n" + 
                "  @Query @Secret(\"p\") int m() { return 0; } \n" +
                "}\n" +
                " public class B { \n" + 
                "  @Query @Secret(\"p\") int m() { return 0; } \n" +
                "}\n" +
                "} \n"
                ,"/Outer.java:4: There is no field or datagroup named p in the class or its super types",18
                ,"/Outer.java:7: There is no field or datagroup named p in the class or its super types",18
        );
    }

    @Test
    public void testSuper() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                " public class A extends B { \n" + 
                "  @Query @Secret(\"p\") int m() { return 0; } \n" +
                "}\n" +
                "  class B { \n" + 
                "  int p; \n" +
                "} \n"
        );
    }

    @Test
    public void testInterface() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                " public class A implements B { \n" + 
                "  @Query @Secret(\"p\") int m() { return 0; } \n" +
                "}\n" +
                "  interface B { \n" + 
                "  //@ instance model int p; \n" +
                "} \n"
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
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Secret(\"m\") @Query int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:3: A method may not be both secret and query for the same datagroup",16
        );
    }
    
    /** Same datagroup */
    @Test
    public void testSameDG3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Secret(\"m\") @Query(\"m\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:3: There is no field or datagroup named m in the class or its super types",23
                ,"/A.java:3: There is no field or datagroup named m in the class or its super types",11
        );
    }
    
    /** Same datagroup */
    @Test
    public void testSameDGOK() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(\"q\") @Query int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** Same datagroup */
    @Test
    public void testSameDGOK2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup m;\n" +
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(\"m\") @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** Same datagroup */
    @Test
    public void testSameDGOK3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q,r;\n" +
                "  @Secret(\"r\") @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
        );
    }
    
    /** Same datagroup */
    @Test
    public void testSameDG4() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret(\"q\") @Query(\"q\") int m() { return 0; } \n" +
                "} \n"
                ,"/A.java:4: A method may not be both secret and query for the same datagroup",16
        );
    }

    @Test
    public void testFOK1() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public secret model \\datagroup q;\n" +
                "  @Secret int m; //@ in q; \n" +
                "} \n"
        );
    }
    
    /** Secret, but not in a datagroup */
    @Test
    public void testFNotIn() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret int m;  \n" +
                "} \n"
                //,"/A.java:4: A secret field must be a model field or in a secret datagroup",15
        );
    }
    
    /** Secret, but not in a datagroup */
    @Test
    public void testFInNonSecret() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  @Secret int m; //@ in q; \n" +
                "} \n"
                ,"/A.java:4: A datagroup for a secret field must be secret",22
        );
    }
    
    /** Not secret but in a secret datagroup */
    @Test
    public void testFInSecret() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public secret model \\datagroup q;\n" +
                "  int m; //@ in q;  \n" +
                "} \n"
                ,"/A.java:4: A datagroup for a non-secret field must be non-secret",14
        );
    }
    
    /** Not secret but in a secret datagroup */
    @Test
    public void testFInSecret2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public secret model \\datagroup q;\n" +
                "  //@ model int m; //@ in q;  \n" +
                "} \n"
                ,"/A.java:4: A datagroup for a non-secret field must be non-secret",24
        );
    }
    
    /** OK - model fields are their own datagroups */
    @Test
    public void testFNotInButModel() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model \\datagroup q;\n" +
                "  //@ secret model int m;  \n" +
                "} \n"
        );
    }
    
    /** Valid argument, but not for a field */
    @Test
    public void testFBadParse() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Secret(\"q\") int m; \n" +
                "} \n"
                ,"/A.java:3: A secret declaration for a field may not have arguments",11
                //,"/A.java:3: A secret field must be a model field or in a secret datagroup",20
        );
    }
    
    /** Invalid argument, also not for field */
    @Test
    public void testFBadParse2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Secret(v=\"q\") int m; \n" +
                "} \n"
                ,"/A.java:3: cannot find symbol\n  symbol:   method v()\n  location: @interface org.jmlspecs.annotation.Secret",13
                ,"/A.java:3: A secret declaration for a field may not have arguments",12
        );
    }
    
    /** Invalid argument, aslo not for field */
    @Test
    public void testFBadParse3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Secret(9) int m; \n" +
                "} \n"
                ,"/A.java:3: incompatible types: int cannot be converted to java.lang.String",11
                ,"/A.java:3: A secret declaration for a field may not have arguments",11
                //,"/A.java:3: A secret field must be a model field or in a secret datagroup",18   // FIXME
        );
    }
    
    /** Valid argument, but not for a field */
    @Test
    public void testFBadParse4() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  @Secret(value=\"q\") int m; \n" +
                "} \n"
                ,"/A.java:3: A secret declaration for a field may not have arguments",16
                //,"/A.java:3: A secret field must be a model field or in a secret datagroup",26
        );
    }
    
    /** OK - standard use */
    @Test
    public void testRepresents() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ secret public model int i;\n" +
                "  //@ secret public model int j; in i; \n" +
                "  //@ secret public represents i = j; \n" +
                "} \n"
        );
    }

    /** Differently secret expression */
    @Test
    public void testRepresents0() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ secret public model int i;\n" +
                "  //@ secret public model int j;\n" +
                "  //@ secret public represents i = j; \n" +
                "} \n"
                ,"/A.java:5: A field may not be read in a secret context unless it is in the same secret datagroup: j not in i",36
        );
    }

    /** Secret id with non-secret represents */
    @Test
    public void testRepresents1() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ secret public model int i;\n" +
                "  //@ public represents i = 0; \n" +
                "} \n"
                ,"/A.java:4: A represents clause and its identifier must both be secret or both not be secret",14
        );
    }

    /** Secret represents with non-secret id */
    @Test
    public void testRepresents2() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model int i;\n" +
                "  //@ secret public represents i = 0; \n" +
                "} \n"
                ,"/A.java:4: A represents clause and its identifier must both be secret or both not be secret",21
        );
    }

    /** Secret on represents may not have an argument */
    @Test
    public void testRepresents3() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ secret public model int i;\n" +
                "  //@ @Secret(\"i\") public represents i = 0; \n" +
                "} \n"
                ,"/A.java:4: A secret declaration for a represents clause may not have arguments",15
        );
    }

    /** testing secret in non-secret represents expression */
    @Test
    public void testRepresents5() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ secret public model int j;\n" +
                "  //@ public model int i;\n" +
                "  //@ public represents i = j; \n" +
                "} \n"
                ,"/A.java:5: Secret fields may not be read in non-secret context: j",29
        );
    }

    /** no secret in invariant */
    @Test
    public void testInvariantSecret() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ secret public model int j;\n" +
                "  //@ public invariant j == 0;\n" +
                "  //@ public constraint j == 0;\n" +
                "} \n"
                ,"/A.java:4: Secret fields may not be read in non-secret context: j",24
                ,"/A.java:5: Secret fields may not be read in non-secret context: j",25
        );
    }

    @Test
    public void testMethodCallSecret() {
        helpTCText("A.java",
                "import org.jmlspecs.annotation.*;\n" +
                "public class A { \n" + 
                "  //@ public model int i;\n" +
                "  //@ public model int j;\n" +
                "  //@ @Query(\"i\") \n" +
                "  public int nq() { \n" +
                "     mq();\n" +  // OK
                "     mqq();\n" +  // BAD
                "     ms();\n" +  // OK
                "     mo();\n" +  // BAD
                "     mp();\n" +  // OK
                "     mss(); return 0;\n" + // BAD
                "  }\n" +
                "  //@ @Secret(\"i\") \n" +
                "  public int ns() { \n" +
                "     mq();\n" +  // OK
                "     mqq();\n" +  // BAD
                "     ms();\n" +  // OK
                "     mo();\n" +  // BAD
                "     mss(); return 0;\n" + // BAD
                "  }\n" +
                "  public int no() { \n" +
                "     mq();\n" +  // OK
                "     mqq();\n" +  // OK
                "     ms();\n" +  // BAD
                "     mo();\n" +  // OK
                "     mss(); return 0;\n" + // BAD
                "  }\n" +
                "  @Secret(\"i\") void ms() {}\n" +
                "  @Secret(\"j\") void mss() {}\n" +
                "  @Query(\"i\") void mq() {}\n" +
                "  @Query(\"j\") void mqq() {}\n" +
                "  void mo() {}\n" +
                "  @Pure void mp() {}\n" +
                "} \n"
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
