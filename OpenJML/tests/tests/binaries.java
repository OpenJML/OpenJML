package tests;

public class binaries extends TCBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        //jmldebug = true;
        super.setUp();
    }

    /** Tests that a system spec file is loaded from mock files - though this has no error reports to be sure it happened*/
    public void testBinary() {
        addMockFile("$A/java/io/File.spec",
                "package java.io; //@ model class VVV{}\n public class File implements Serializable, Comparable<File> { \n//@model static public class TTT {} \n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
        );
    }

    /** Tests that a system spec file with an unmatched Java method is errored */
    public void testBinary2() {
        addMockFile("$A/java/io/File.spec",
                "package java.io; //@ model class VVV{ static int i; }\n" + 
                "public class File  implements Serializable, Comparable<File> { \n" +
                " public void m() { /*@ assert i; assume j; */ }\n" +
                "//@model static public class TTT { static int j; } " +
                "\n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
                ,"/$A/java/io/File.spec:3: The method java.io.File.m is a Java method (neither ghost nor model) but does not match any methods in the corresponding Java class. \n      Signatures found:   <none>",14
        );
    }
    
    /** Tests that a system spec file with an matched Java method is checked */
    public void testBinary2a() {
        addMockFile("$A/java/io/File.spec",
                "package java.io; //@ model class VVV{ static int i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                " public void exists() { /*@ assert true; assume true; */ }\n" +
                "//@model static public class TTT { static int j; } " +
                "\n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
                ,"/$A/java/io/File.spec:3: The specification of the method java.io.File.exists() must not have a body",23
                ,"/$A/java/io/File.spec:3: The return types of method java.io.File.exists() are different in the specification and java files: void vs. boolean",9
        );
    }
    
    /** Tests that model methods etc. in system spec files are actually checked */
    public void testBinary3() {
        addMockFile("$A/java/io/File.spec",
                "package java.io; //@ model class VVV{ public static int i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "/*@ invariant VVV.i; invariant TTT.j; */ \n" +
                "//@model static public class TTT { public static int j; } \n" +
                "}\n ");
        helpTCF("java/io/A.java",
                "package java.io; class A { \n" +
                "    java.io.File file; \n" +
                " public void m() { /*@ assert java.io.VVV.i; assume java.io.File.TTT.j; */ }\n" +
                "}"
                ,"/java/io/A.java:3: incompatible types\n  required: boolean\n  found:    int",42
                ,"/java/io/A.java:3: incompatible types\n  required: boolean\n  found:    int",69
                ,"/$A/java/io/File.spec:3: incompatible types\n  required: boolean\n  found:    int",18
                ,"/$A/java/io/File.spec:3: incompatible types\n  required: boolean\n  found:    int",35
        );
    }

    /** Checks that a Java field in the spec file actually matches the binary; also various lookup tests */
    public void testBinary4() {
        addMockFile("$A/java/io/File.spec",
                "package java.io; \n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "  static public int j;\n" +
                "  //@ ghost static public int k; \n" +
                "}\n ");
        helpTCF("java/io/A.java",
                "package java.io; class A { \n" +
                "    java.io.File file; \n" +
                " public void m() { boolean i = File.j; int ii = File.k; \n" +
                "     boolean q = File.separatorChar; \n" + 
                "     /*@ assert java.io.File.j; assume java.io.File.k; */ }\n" +
                "}"
                ,"/$A/java/io/File.spec:3: The field j is a Java field (neither ghost nor model) but does not match any fields in the corresponding Java class.",21
                ,"/java/io/A.java:3: cannot find symbol\n  symbol:   variable j\n  location: class java.io.File",36
                ,"/java/io/A.java:3: cannot find symbol\n  symbol:   variable k\n  location: class java.io.File",53
                ,"/java/io/A.java:4: incompatible types\n  required: boolean\n  found:    char",22
                ,"/java/io/A.java:5: cannot find symbol\n  symbol:   variable j\n  location: class java.io.File",29
                ,"/java/io/A.java:5: incompatible types\n  required: boolean\n  found:    int",52
        );
    }

}
