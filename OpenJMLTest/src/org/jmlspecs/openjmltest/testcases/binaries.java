package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class binaries extends TCBase {

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        //jmldebug = true;
        super.setUp();
        //main.addOptions("-jmldebug");
    }

    /** Tests that a system spec file is loaded from mock files - though this has no error reports to be sure it happened*/
    @Test
    public void testBinary() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{}\n public class File implements Serializable, Comparable<File> { \n//@model static public class TTT {} \n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
        );
    }

    /** Tests that a system spec file with an unmatched Java method is errored */
    @Test
    public void testBinary2() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{ static int i; }\n" + 
                "public class File  implements Serializable, Comparable<File> { \n" +
                " public void m() {  }\n" +
                "//@ model static class TTT { static int j; } " +
                "\n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
                ,"/$A/java/io/File.jml:3: error: There is no binary method to match this Java declaration in the specification file: java.io.File.m",14
        );
    }
    
    /** Tests that a system spec file with an matched Java method is checked */
    @Test
    public void testBinary2a() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{ static int i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                " public void exists() { /*@ assert true; assume true; */ }\n" +
                "//@ model static class TTT { static int j; } " +
                "\n }");
        helpTCF("A.java",
                " class A { \n" +
                "    java.io.File file; \n" +
                "}"
                // FIXME - different order in Java7 and Java8
                ,"/$A/java/io/File.jml:3: error: The return types of method java.io.File.exists() are different in the specification and java files: void vs. boolean",9
                ,"/$A/java/io/File.jml:3: error: The specification of the method java.io.File.exists() must not have a body",23
        );
    }
    
    /** Tests that model methods etc. in system spec files are actually checked */
    @Test
    public void testBinary3() { 
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{ public static int i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "/*@ public invariant VVV.i; public invariant TTT.j; */ \n" +
                "//@ model static public class TTT { public static int j; } \n" +
                "}\n ");
        helpTCF("A.java",
                "class A { \n" +
                "    java.io.File file; \n" +
                " public void m() { /*@ assert java.io.VVV.i; assume java.io.File.TTT.j; */ }\n" +
                "}"
                ,"/A.java:3: error: java.io.VVV is not public in java.io; cannot be accessed from outside package",38
                ,"/A.java:3: error: java.io.VVV is not public in java.io; cannot be accessed from outside package",38 // TODO: It is OpenJDK itslef that duplicates this error message
                ,"/A.java:3: error: incompatible types: int cannot be converted to boolean",69
                ,"/$A/java/io/File.jml:3: error: incompatible types: int cannot be converted to boolean",25
                ,"/$A/java/io/File.jml:3: error: incompatible types: int cannot be converted to boolean",49
        );
    }

    /** Variation in which A.java does not reference VVV and TTT, just File */
    @Test
    public void testBinary3a() { 
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model class VVV{ public static int i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "/*@ public invariant VVV.i; public invariant TTT.j; */ \n" +
                "//@ model static class TTT { public static int j; } \n" +
                "}\n ");
        helpTCF("A.java",
                "class A { \n" +
                "    java.io.File file; \n" +
                " public void m() {  }\n" +
                "}"
                ,"/$A/java/io/File.jml:3: error: incompatible types: int cannot be converted to boolean",25
                ,"/$A/java/io/File.jml:3: error: incompatible types: int cannot be converted to boolean",49
        );
    }

    /** Tests that model methods etc. in system spec files are actually checked */  // FIXME - not sure this should actually work - unlerss File is parsed by some other means, how would one know where VVV and TTT are
    @Test
    public void testBinary3b() { 
        addMockFile("$A/java/io/File.jml",
                "package java.io; //@ model  class VVV{ public static boolean i; }\n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "/*@ public invariant VVV.i; public invariant TTT.j; */ \n" +
                "//@ model static public class TTT { public static boolean j; } \n" +
                "}\n ");
        helpTCF("A.java",
                "class A { \n" +
                "    java.io.File file; \n" +
                " public void m() { /*@  assume java.io.File.TTT.j; */ }\n" +
                "}"
        );
    }

    // Checks a bug in which the following crashes after seeing that java.io (for Class A) is not in the unnamed package
    @Test
    public void testBinary3c() { 
//        addMockFile("$A/java/io/File.jml",
//                "package java.io; //@ model class VVV{ public static int i; }\n" + 
//                "public class File implements Serializable, Comparable<File> { \n" +
//                "/*@ public invariant VVV.i; public invariant TTT.j; */ \n" +
//                "//@ model static class TTT { public static int j; } \n" +
//                "}\n ");
        helpTCF("A.java",
                "package java.io; class A { \n" +
                "    java.io.File file; \n" +
                " public void m() {  }\n" +
                "}"
                ,"/A.java:1: error: package exists in another module: java.base",1
        );
    }

    /** Checks that a Java field in the spec file actually matches the binary; also various lookup tests */
    @Test
    public void testBinary4() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; \n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "  static public int j;\n" +
                "  //@ ghost static public int k; \n" +
                "}\n ");
        helpTCF("A.java",
                "import java.io.File; class A { \n" +
                "    java.io.File file; \n" +
                " public void m() { boolean i = File.j; int ii = File.k; \n" +
                "     boolean q = File.separatorChar; \n" + 
                "     /*@ assert java.io.File.j; assume java.io.File.k; */ }\n" +
                "}"
                ,"/$A/java/io/File.jml:3: error: There is no binary field to match this declaration in the specification file: java.io.File.j",21
                ,"/A.java:3: error: cannot find symbol\n  symbol:   variable j\n  location: class java.io.File",36
                ,"/A.java:3: error: cannot find symbol\n  symbol:   variable k\n  location: class java.io.File",53
                ,"/A.java:4: error: incompatible types: char cannot be converted to boolean",22
                ,"/A.java:5: error: cannot find symbol\n  symbol:   variable j\n  location: class java.io.File",29
                ,"/A.java:5: error: incompatible types: int cannot be converted to boolean",52
        );
    }

    /** Checks that an extra Java class in a spec file is reported */
    @Test
    public void testBinary5() {
        addMockFile("$A/java/io/File.jml",
                "package java.io; \n" + 
                "public class File implements Serializable, Comparable<File> { \n" +
                "}\n" +
                "class Extra {}\n");
        helpTCF("/A.java",
                "class A { \n" +
                "    java.io.File file; \n" +
                "}"
                ,"/$A/java/io/File.jml:4: error: There is no binary class to match this Java declaration in the specification file: java.io.Extra",1
        );
    }
}
