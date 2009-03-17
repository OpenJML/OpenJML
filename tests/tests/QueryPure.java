package tests;

public class QueryPure extends TCBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }
    
    public void testClass1() {
        helpTCF("A.java",
                "//@ pure\n" +  // OK
                "public class A { } \n"
        );
    }
    
    public void testClass2() {
        helpTCF("A.java",
                "//@ query\n" +   // OK
                "public class A { } \n"
        );
    }

    public void testClass3() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "@Query\n" +  // OK
                "public class A { } \n"
        );
    }

    public void testClass4() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "@Pure\n" +  // OK
                "public class A { } \n"
        );
    }

    public void testClass5() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "@Pure @Query\n" +   // BAD
                "public class A { } \n"
                ,"/A.java:2: A declaration may not be both pure and query",7
        );
    }

    public void testClass6() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "//@ pure query\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: A declaration may not be both pure and query",10
        );
    }

    public void testClass7() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "@Pure //@ query\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: A declaration may not be both pure and query",11
        );
    }

    public void testClass8() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "@Pure //@ pure\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: duplicate annotation",11
        );
    }

    public void testClass9() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "@Query //@ query\n" +  // BAD
                "public class A { } \n"
                ,"/A.java:2: duplicate annotation",12
        );
    }

    public void testMethod1() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Query\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    public void testMethod2() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ query\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    public void testMethod3() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Pure\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    public void testMethod4() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@pure\n" +  // OK
                "  public void v() {}" +
                "} \n"
        );
    }

    public void testMethod5() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ pure query\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: A declaration may not be both pure and query",12
        );
    }

    public void testMethod6() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Query @Pure\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: A declaration may not be both pure and query",3
        );
    }

    public void testMethod7() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Pure //@ query\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: A declaration may not be both pure and query",13
        );
    }

    public void testMethod8() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Query //@ query\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: duplicate annotation",14
        );
    }

    public void testMethod9() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Query //@ query\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: duplicate annotation",14
        );
    }

    
//    public void testMethod() {
//        helpTCF("A.java",
//                "public class A { \n" +
//                "  void m() {}\n" +  // OK
//                "  //@ model int m1() { return 0; }\n" + // OK
//                "  /*@ model */ int m2() { return 9; }\n" + // BAD
//                "  void p();\n" +  // BAD
//                "  //@ model int p1();\n" +  // OK
//                "  /*@ model */ int p2();\n" +  // BAD
//                "  //@ int q();\n" +  // BAD
//                
//                "  static public class II {\n" +  // Line 9
//                "  void m() {}\n" +  // OK
//                "  //@ model int m1() { return 0; }\n" + // OK
//                "  /*@ model */ int m2() { return 9; }\n" + // BAD
//                "  void p();\n" +  // BAD
//                "  //@ model int p1();\n" +  // OK
//                "  /*@ model */ int p2();\n" +  // BAD
//                "  //@ int q();\n" +  // BAD
//                "  }\n" +
//                
//                "  /*@ static model public class III {\n" +  // Line 18
//                "  void m() {}\n" +  // OK
//                "  model int m1() { return 0; }\n" + // NO NESTING
//                "  void p();\n" +  // BAD
//                "  model int p1();\n" +  // NO NESTING
//                "  }*/\n" +
//                
//                "}\n" +
//                
//                "/*@ model class B { \n" +  // Line 25
//                "  void m() {}\n" +  // OK
//                "   model int m1() { return 0; }\n" + // NO NESTING
//                "  void p();\n" +  // BAD
//                "   model int p1();\n" +  // NO NESTING
//                "}\n*/" +
//                
//                " class C { \n" +  // Line 31
//                "  void m() {}\n" +  // OK
//                "  //@ model int m1() { return 0; }\n" + // OK
//                "  /*@ model */ int m2() { return 9; }\n" + // BAD
//                "  void p();\n" +  // BAD
//                "  //@ model int p1();\n" +  // OK
//                "  /*@ model */ int p2();\n" +  // BAD
//                "  //@ int q();\n" +  // BAD
//                "}"
//                ,"/A.java:4: A Java declaration (not within a JML annotation) may not be either ghost or model",20
//                ,"/A.java:5: missing method body, or declare abstract",8
//                ,"/A.java:7: missing method body, or declare abstract",20
//                ,"/A.java:7: A Java declaration (not within a JML annotation) may not be either ghost or model",20
//                ,"/A.java:12: A Java declaration (not within a JML annotation) may not be either ghost or model",20
//                ,"/A.java:13: missing method body, or declare abstract",8
//                ,"/A.java:15: missing method body, or declare abstract",20
//                ,"/A.java:15: A Java declaration (not within a JML annotation) may not be either ghost or model",20
//                ,"/A.java:16: A method or type declaration within a JML annotation must be model",11
//                ,"/A.java:8: A method or type declaration within a JML annotation must be model",11
//                ,"/A.java:20: A model type may not contain model declarations",13
//                ,"/A.java:21: missing method body, or declare abstract",8
//                ,"/A.java:22: missing method body, or declare abstract",13
//                ,"/A.java:22: A model type may not contain model declarations",13
//                ,"/A.java:34: A Java declaration (not within a JML annotation) may not be either ghost or model",20
//                ,"/A.java:35: missing method body, or declare abstract",8
//                ,"/A.java:37: missing method body, or declare abstract",20
//                ,"/A.java:37: A Java declaration (not within a JML annotation) may not be either ghost or model",20
//                ,"/A.java:38: A method or type declaration within a JML annotation must be model",11
//                ,"/A.java:27: A model type may not contain model declarations",14
//                ,"/A.java:28: missing method body, or declare abstract",8
//                ,"/A.java:29: missing method body, or declare abstract",14
//                ,"/A.java:29: A model type may not contain model declarations",14
//                );
//    }

}
