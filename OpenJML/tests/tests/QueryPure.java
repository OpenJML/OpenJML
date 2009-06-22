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
                "  @Pure //@ pure\n" +  // BAD
                "  public void v() {}" +
                "} \n"
                ,"/A.java:3: duplicate annotation",13
        );
    }

}
