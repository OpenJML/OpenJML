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

    public void testCacheExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ secret public model JMLDataGroup value;\n" +
                "  @Secret protected Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query(\"value\") public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
        );
    }
        
    public void testSimplerCacheExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ model secret Object value;\n" +
                "  @Secret protected Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
        );
    }

    public void testAnotherCacheExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Secret Integer cache = null; \n" + // Requires allowing non-model fields to be datagroups
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query(\"cache\") public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
        );
    }

    public void testAnotherValidExample() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + // To use the implicit declaration, value here must be after the Query
                "} \n"
        );
    }

    public void testInvariant() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + // To use the implicit declaration, value here must be after the Query
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute();\n" +
                "} \n"
        );
    }

    public void testForwardRef() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  //@ secret model Object value;\n" + // we're allowing forward reference
                "} \n"
        );
    }

    public void testCircular() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ secret model Integer cache = null; //@ in value; \n" + 
                "  //@ secret model Object value; in cache; \n" + // error - circular
                "} \n"
                ,"/A.java:3: This field participates in a circular datagroup inclusion chain: cache",46
                ,"/A.java:4: This field participates in a circular datagroup inclusion chain: value",34
        );
    }

    public void testQuery0() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Secret Integer cache = null; //@ in value; \n" + // ERROR - value not found (implicitly defined by the Query) TODO - perhaps relax this restriction
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
                ,"/A.java:3: cannot find symbol\n  symbol:   variable value\n  location: class A",40
        );
    }

    public void testQuery1() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ model secret Object value;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == cache;\n" +  // ERROR - no use of secret in specs
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "} \n"
                ,"/A.java:6: Secret fields may not be read in non-secret context: cache",26
        );
    }

    public void testQuery2() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ model secret Object value;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" + 
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return cache; }\n" + // ERROR - no use of secret in open method
                "} \n"
                ,"/A.java:8: Secret fields may not be read in non-secret context: cache",29
        );
    }

    public void testQuery3() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { f = 0; if (cache == null) cache = compute(); return cache; }\n" + // ERROR - no assignment except to secret
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
                ,"/A.java:5: The field f is not writable since it is not in the value secret datagroup",31
        );
    }

    public void testQuery4() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o;\n " +
                "  @Secret int q; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { q = 0; if (cache == null) cache = compute(); return cache; }\n" + // ERROR - no assignment except to own secret
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
                ,"/A.java:7: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",31
                ,"/A.java:7: The field q is not writable since it is not in the value secret datagroup",31
        );
    }

    public void testQuery5() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o;\n " +
                "  @Secret int q; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute() + q; return cache; }\n" + // ERROR - no reading other secret
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
                ,"/A.java:7: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",70
        );
    }

    public void testQuery6() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute() + q; return cache; }\n" + // OK - q is nested in value
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "} \n"
        );
    }

    public void testQuery7() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o;\n " +
                "  @Secret int q; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" + 
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + q;\n" +// ERROR - no reading other secret
                "} \n"
                ,"/A.java:11: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",80
        );
    }

    public void testQuery8() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + q;\n" + // OK - q is nested in value
                "} \n"
                ,"/A.java:3: cannot find symbol\n  symbol:   variable value\n  location: class A",41 
        );
    }

    public void testQuery8OK() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret(\"value\") public invariant cache != null ==> cache == compute() + q;\n" + // OK - q is nested in value
                "} \n"
        );
    }

    public void testQuery8a() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model Object value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  int f; @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  //@ ensures \\result == compute();\n" +
                "  @Query public int value() { if (cache == null) cache = compute(); return cache; }\n" +
                "  public int use() { return value(); }\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  //@ @Secret public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(0) public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(\"org\") public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(\"value\",\"value\") public invariant true;\n" + // BAD SYNTAX
                "  //@ @Secret(\"v\") public invariant true;\n" + // ERROR - not found
                "} \n"
                ,"/A.java:11: A secret annotation on an invariant must have exactly one argument",22
                ,"/A.java:12: incompatible types\n  required: java.lang.String\n  found:    int",15
                ,"/A.java:13: cannot find symbol\n  symbol:   variable org\n  location: class A",15
                ,"/A.java:14: annotation values must be of the form 'name=value'",15
                ,"/A.java:14: annotation values must be of the form 'name=value'",23
                ,"/A.java:14: A secret annotation on an invariant must have exactly one argument",39
                ,"/A.java:15: cannot find symbol\n  symbol:   variable v\n  location: class A",15
        );
    }

    public void testQuery9() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret public model int value;\n" +
                "  //@ @Secret public model Object o; in value; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Secret(\"value\") public int mm() { cache = null; q = 0; f = 0; }\n" +  // ERROR - can't write f; 
                "} \n"
                ,"/A.java:9: The field f is not writable since it is not in the value secret datagroup",59
        );
    }

    public void testQuery10() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret model int value;\n" +
                "  //@ @Secret public model Object o; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Secret(\"value\") public int mm() {  q = 0;  }\n" +  // ERROR - can't read or write q
                "} \n"
                ,"/A.java:9: A field may not be read in a secret context unless it is in the same secret datagroup: q not in value",39
                ,"/A.java:9: The field q is not writable since it is not in the value secret datagroup",39
        );
    }

    public void testQuery11() {
        helpTCF("A.java",
                "import org.jmlspecs.annotations.*;\n" +
                "public class A { \n" +
                "  //@ @Secret model int value;\n" +
                "  //@ @Secret public model Object o; \n " +
                "  @Secret int q = 5; //@ in o;\n" +
                "  @Pure public int compute() { return 0; }\n" +
                "  int f;\n" +
                "  @Secret Integer cache = null; //@ in value; \n" + 
                "  @Secret public void mm() {  }\n" +  // ERROR - methods must have a argument to @Secret
                "} \n"
                ,"/A.java:9: A secret annotation on a method must have exactly one argument",3
        );
    }

    // FIXME - what about secret invariants, represents clauses or initializers of secret fields
    // FIXME - what about reading from/writing to - selections and array references
    // FIXME - what about calling non-secret methods, constructors

}
